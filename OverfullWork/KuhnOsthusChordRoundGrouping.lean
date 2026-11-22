module

public import OverfullWork.KuhnOsthusPreparedChordSystems
public import OverfullWork.KuhnOsthusWalkBankPartition

@[expose] public section


/-! Split the required arcs of the chord absorber among the rounds
of Kühn–Osthus Lemma 9.7, with ownership in the physical graph. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V W : Type*}

/-- An embedding transports the union of ordinary arcs. -/
theorem lift_directed_pair_sup (e : W ↪ V) (H U : Digraph W) :
    liftDirectedPair e e (H ⊔ U) = liftDirectedPair e e H ⊔ liftDirectedPair e e U := by
  ext x y
  constructor
  · rintro ⟨a,b,ha,hb,hh | hu⟩
    · exact Or.inl ⟨a,b,ha,hb,hh⟩
    · exact Or.inr ⟨a,b,ha,hb,hu⟩
  · rintro (⟨a,b,ha,hb,hh⟩ | ⟨a,b,ha,hb,hu⟩)
    · exact ⟨a,b,ha,hb,Or.inl hh⟩
    · exact ⟨a,b,ha,hb,Or.inr hu⟩

/-- Group the original exceptional factors into equal rounds. A
factor can have many complete exceptional path systems, but all
of its arcs go to one round. -/
theorem group_exceptional_factors_into_chord_rounds {r t : ℕ}
    (E : Fin (r*t) → Digraph V)
    (hDis : ∀ i j, i ≠ j → Disjoint (E i) (E j)) :
    let round (i : Fin r) := ⨆ j : Fin t, E (finProdFinEquiv (i,j))
    let total := ⨆ i, E i
    (∀ i, round i ≤ total) ∧ ∀ x y, total.Adj x y → ∃! i, (round i).Adj x y := by
  intro round total
  have hLe (i : Fin r) : round i ≤ total :=
    iSup_le (fun j => le_iSup E (finProdFinEquiv (i,j)))
  refine ⟨hLe,?_⟩
  intro x y hxy
  obtain ⟨z,hz⟩ := Digraph.iSup_adj.mp hxy
  let e : Fin r × Fin t ≃ Fin (r*t) := finProdFinEquiv
  obtain ⟨⟨i,j⟩,he⟩ := e.surjective z
  refine ⟨i,Digraph.iSup_adj.mpr ⟨j,he.symm ▸ hz⟩,?_⟩
  intro i' h'
  obtain ⟨j',hj'⟩ := Digraph.iSup_adj.mp h'
  have hEq : e (i',j') = e (i,j) := by
    by_contra hn
    exact disjoint_iff_inf_le.mp (hDis _ _ hn) ⟨hj',he.symm ▸ hz⟩
  exact congrArg Prod.fst (e.injective hEq)

variable [Fintype V]

/-- Combine the factorization, the walk-bank split and the
exceptional-factor grouping. Every required physical arc has
one round owner before any Hamilton cycle is chosen. -/
theorem combine_chord_round_arc_owners {r : ℕ} (Z : Finset V) (H U : Digraph ↥Zᶜ) (E : Digraph V)
    (H' U' : Fin r → Digraph ↥Zᶜ) (E' : Fin r → Digraph V)
    (hHU : Disjoint H U)
    (hH : ∀ i, H' i ≤ H) (hU : ∀ i, U' i ≤ U) (hE : ∀ i, E' i ≤ E)
    (hH' : ∀ x y, H.Adj x y → ∃! i, (H' i).Adj x y)
    (hU' : ∀ x y, U.Adj x y → ∃! i, (U' i).Adj x y)
    (hE' : ∀ x y, E.Adj x y → ∃! i, (E' i).Adj x y) :
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
    let total := liftDirectedPair e e H ⊔ liftDirectedPair e e U ⊔ E
    let round (i : Fin r) := liftDirectedPair e e (U' i ⊔ H' i) ⊔ E' i
    Disjoint (liftDirectedPair e e H ⊔ liftDirectedPair e e U) E →
    (∀ i, round i ≤ total) ∧ ∀ x y, total.Adj x y → ∃! i, (round i).Adj x y := by
  intro e total round hDis
  let V' : Digraph ↥Zᶜ := U ⊔ H
  let B (i : Fin r) := U' i ⊔ H' i
  have hDis' : Disjoint (liftDirectedPair e e V') E := by
    dsimp [V']
    rw [lift_directed_pair_sup,sup_comm]
    exact hDis
  have hCover x y (he : V'.Adj x y) : ∃! i, (B i).Adj x y := by
    rcases he with hu | hh
    · obtain ⟨i,hi,hOwner⟩ := hU' x y hu
      refine ⟨i,Or.inl hi,?_⟩
      rintro j (hj | hj)
      · exact hOwner j hj
      · exact (disjoint_iff_inf_le.mp hHU ⟨hH j hj,hu⟩).elim
    · obtain ⟨i,hi,hOwner⟩ := hH' x y hh
      refine ⟨i,Or.inr hi,?_⟩
      rintro j (hj | hj)
      · exact (disjoint_iff_inf_le.mp hHU ⟨hh,hU j hj⟩).elim
      · exact hOwner j hj
  have hLift (i : Fin r) : liftDirectedPair e e (B i) ≤ liftDirectedPair e e V' :=
    liftDirectedPair_mono e e (sup_le_sup (hU i) (hH i))
  have hEq : liftDirectedPair e e V' ⊔ E = total := by
    change liftDirectedPair e e (U ⊔ H) ⊔ E = _
    rw [lift_directed_pair_sup,sup_comm (liftDirectedPair e e U) (liftDirectedPair e e H)]
  refine ⟨fun i => hEq ▸ sup_le_sup (hLift i) (hE i),?_⟩
  intro x y
  rw [←hEq]
  rintro (⟨a,b,rfl,rfl,hab⟩ | he)
  · obtain ⟨i,hi,hOwner⟩ := hCover a b hab
    refine ⟨i,Or.inl ((liftDirectedPair_adj e e (B i) a b).mpr hi),?_⟩
    rintro j (hj | hj)
    · exact hOwner j ((liftDirectedPair_adj e e (B j) a b).mp hj)
    · exact (disjoint_iff_inf_le.mp hDis' ⟨⟨a,b,rfl,rfl,hab⟩,hE j hj⟩).elim
  · obtain ⟨i,hi,hOwner⟩ := hE' x y he
    refine ⟨i,Or.inr hi,?_⟩
    rintro j (hj | hj)
    · exact (disjoint_iff_inf_le.mp hDis' ⟨hLift j hj,he⟩).elim
    · exact hOwner j hj

end OverfullWork.DirectedRobustExpansion
