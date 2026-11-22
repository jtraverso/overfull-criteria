module

public import OverfullWork.KuhnOsthusWalkBlowup

@[expose] public section


/-! Split (CA2) into the equal walk reserves of Kühn–Osthus Lemma 9.7.
The same index division is used on every quarter of every occurrence
of a walk edge. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V I : Type*} [Fintype V]

/-- Partition a reserve of `r*k` perfect matchings per pair into
`r` reserves of `k` matchings per pair. Every physical arc has
one owner and each reserve has exact semidegrees. -/
theorem partition_successor_matching_bank {r k : ℕ}
    (A : I → Finset V) (s : Equiv.Perm I)
    (M : ∀ j, Fin (r*k) → A j ≃ A (s j))
    (hCell : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hArc : ∀ i b c, b ≠ c → ∀ x, M i b x ≠ M i c x) :
    let N (p : Fin r) (j : I) (i : Fin k) := M j (finProdFinEquiv (p,i))
    let U := successorCellMatchingUnion A s M
    let pieces (p : Fin r) := successorCellMatchingUnion A s (N p)
    (∀ x y, U.Adj x y ↔ ∃! p, (pieces p).Adj x y) ∧
      (∀ p, pieces p ≤ U) ∧
      ∀ p i (x : A i), inDegree (pieces p) x = k ∧ outDegree (pieces p) x = k := by
  intro N U pieces
  have hLe (p : Fin r) : pieces p ≤ U := by
    rintro x y ⟨j,i,a,hx,hy⟩
    exact ⟨j,finProdFinEquiv (p,i),a,hx,hy⟩
  refine ⟨?_,hLe,?_⟩
  · intro x y
    constructor
    · rintro ⟨j,b,a,rfl,hy⟩
      obtain ⟨⟨p,i⟩,hb⟩ := (finProdFinEquiv : Fin r × Fin k ≃ Fin (r*k)).surjective b
      refine ⟨p,⟨j,i,a,rfl,?_⟩,?_⟩
      · change (M j (finProdFinEquiv (p,i)) a).val = y
        rwa [hb]
      · rintro p' ⟨j',i',a',ha',hy'⟩
        have hEq : j' = j := by
          by_contra hne
          exact disjoint_left.mp (hCell _ _ hne) (ha' ▸ a'.prop) a.prop
        subst j'
        have ha : a' = a := Subtype.ext ha'
        subst a'
        have hBanks : finProdFinEquiv (p',i') = b := by
          by_contra hne
          exact hArc j _ _ hne a (Subtype.ext (hy'.trans hy.symm))
        exact congrArg Prod.fst (finProdFinEquiv.injective (hBanks.trans hb.symm))
    · rintro ⟨p,hp,_⟩
      exact hLe p hp
  · intro p
    apply successor_cell_matching_union_degrees A s (N p) hCell
    intro j b c hne x
    exact hArc j _ _ (fun he => hne (congrArg Prod.snd (finProdFinEquiv.injective he))) x

end OverfullWork.DirectedRobustExpansion
