module

public import OverfullWork.KuhnOsthusStyleMatching
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section


/-! Obtain the compatibility matching in Lemma 8.1 from the
multiplicities of the styles rather than from compatibility degrees. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset

/-- The forbidden styles specify which complete exceptional paths cannot
receive each piece. Multiplicity bounds yield the two Hall conditions. -/
theorem exists_style_assignment_from_multiplicities {A B J : Type*}
    [Fintype A] [Fintype B] [DecidableEq J]
    (forbidden : A → Finset J) (style : B → J) {p t u : ℕ}
    (hSize : Fintype.card A ≤ Fintype.card B)
    (hStyles : ∀ a, (forbidden a).card ≤ p)
    (hB : ∀ j, (univ.filter (fun b => style b = j)).card ≤ t)
    (hA : ∀ j, (univ.filter (fun a => j ∈ forbidden a)).card ≤ u)
    (hLeft : 2 * (p*t) ≤ Fintype.card B)
    (hRight : 2 * u ≤ Fintype.card A) :
    ∃ f : A → B, Function.Injective f ∧ ∀ a, style (f a) ∉ forbidden a := by
  classical
  apply exists_style_matching_of_half_degrees (fun a b => style b ∉ forbidden a) hSize
  · intro a
    let bad := univ.filter (fun b => style b ∈ forbidden a)
    have hBad : bad = (forbidden a).biUnion (fun j => univ.filter (fun b => style b = j)) := by
      ext b
      simp only [bad,mem_filter,mem_univ,true_and,mem_biUnion]
      exact ⟨fun h => ⟨style b,h,rfl⟩,fun ⟨j,hj,h⟩ => h.symm ▸ hj⟩
    have hCount : bad.card ≤ p*t := by
      rw [hBad]
      exact (card_biUnion_le_card_mul _ _ _ (fun j _ => hB j)).trans
        (Nat.mul_le_mul_right _ (hStyles a))
    have hSplit := card_filter_add_card_filter_not (s := (univ : Finset B))
      (fun b => style b ∈ forbidden a)
    rw [card_univ] at hSplit
    change bad.card + (univ.filter (fun b => style b ∉ forbidden a)).card =
      Fintype.card B at hSplit
    omega
  · intro b
    have hCount := hA (style b)
    have hSplit := card_filter_add_card_filter_not (s := (univ : Finset A))
      (fun a => style b ∈ forbidden a)
    rw [card_univ] at hSplit
    omega

end OverfullWork.DirectedRobustExpansion
