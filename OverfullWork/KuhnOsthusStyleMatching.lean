module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Fintype.Card

@[expose] public section


/-! The Hall argument for assigning the ordinary path pieces to different
styles of complete exceptional path systems in Kühn–Osthus Lemma 8.1. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset

theorem exists_style_matching_of_half_degrees {A B : Type*} [Fintype A] [Fintype B]
    (compatible : A → B → Prop) [DecidableRel compatible]
    (hSize : Fintype.card A ≤ Fintype.card B)
    (hLeft : ∀ a, Fintype.card B ≤ 2 * (univ.filter (compatible a)).card)
    (hRight : ∀ b, Fintype.card A ≤ 2 * (univ.filter (fun a => compatible a b)).card) :
    ∃ f : A → B, Function.Injective f ∧ ∀ a, compatible a (f a) := by
  classical
  let N : A → Finset B := fun a => univ.filter (compatible a)
  have hHall (S : Finset A) : S.card ≤ (S.biUnion N).card := by
    by_cases hLarge : Fintype.card A < 2 * S.card
    · have hAll : S.biUnion N = univ := by
        apply eq_univ_of_forall
        intro b
        by_contra hMissing
        let M := univ.filter (fun a => compatible a b)
        have hOutside : M ⊆ univ \ S := by
          intro a ha
          have hCompatible := (mem_filter.mp ha).2
          exact mem_sdiff.mpr ⟨mem_univ _,fun haS =>
            hMissing (mem_biUnion.mpr ⟨a,haS,mem_filter.mpr ⟨mem_univ _,hCompatible⟩⟩)⟩
        have hBound := card_le_card hOutside
        rw [card_sdiff_of_subset (subset_univ S),card_univ] at hBound
        have hMin : Fintype.card A ≤ 2 * M.card := hRight b
        have hS := card_le_univ S
        omega
      rw [hAll,card_univ]
      exact (card_le_univ S).trans hSize
    · by_cases hn : S.Nonempty
      · obtain ⟨a,ha⟩ := hn
        have hN : N a ⊆ S.biUnion N := fun b hb => mem_biUnion.mpr ⟨a,ha,hb⟩
        have hBound := card_le_card hN
        have hMin : Fintype.card B ≤ 2 * (N a).card := hLeft a
        omega
      · rw [not_nonempty_iff_eq_empty.mp hn,card_empty]
        exact Nat.zero_le _
  obtain ⟨f,hf,hN⟩ := (all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  exact ⟨f,hf,fun a => (mem_filter.mp (hN a)).2⟩

end OverfullWork.DirectedRobustExpansion
