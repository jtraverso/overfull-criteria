module

public import OverfullWork.OrdinaryEndpointSupport

@[expose] public section


/-! # Actual safe free-neighbor set at an alternating-path endpoint

Every ambient opposite-part neighbor is either still available or has
a colored crossing copy. Removing W then pays exactly its cardinality.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.PrunedCore OverfullWork.RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 20000000

noncomputable def bootstrapSet (P : M.PartialColouring k) (A W : Finset V) (v : V) : Finset V :=
  (P.available.crossingSupport A).neighborFinset v\W

theorem bootstrapSet_member (P : M.PartialColouring k) (A W : Finset V) (v x : V)
    (hx : x ∈ P.bootstrapSet A W v) :
    (P.available.crossingSupport A).Adj v x ∧ x ∉ W := by
  exact ⟨(mem_neighborFinset _ _ _).mp (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩

theorem opposite_support_bootstrap_bound (P : M.PartialColouring k) (A W : Finset V) (v : V)
    (D : Finset V) (hOpp : ∀ x ∈ D, ¬(v ∈ A ↔ x ∈ A)) :
    neighboursIn M.supportGraph D v ≤ (P.bootstrapSet A W v).card+W.card+(P.graph.crossingSupport A).degree v := by
  have hs : D.filter (fun x => M.supportGraph.Adj v x) ⊆
      (P.available.crossingSupport A).neighborFinset v ∪ (P.graph.crossingSupport A).neighborFinset v := by
    intro x hx
    obtain ⟨hxD,hxM⟩ := mem_filter.mp hx
    have hCross := hOpp x hxD
    by_cases hOld : 0 < P.graph.mult s(v,x)
    · exact mem_union_right _ ((mem_neighborFinset _ _ _).mpr ⟨hOld,hCross⟩)
    · have hZero : P.graph.mult s(v,x)=0 := by omega
      have hAvail : 0 < P.available.mult s(v,x) := by
        change 0 < M.mult s(v,x)-P.graph.mult s(v,x)
        rw [hZero,Nat.sub_zero]
        exact hxM
      exact mem_union_left _ ((mem_neighborFinset _ _ _).mpr ⟨hAvail,hCross⟩)
  have hh := (card_le_card hs).trans (card_union_le _ _)
  have hDelete := card_le_card_sdiff_add_card (s := (P.available.crossingSupport A).neighborFinset v) (t := W)
  rw [neighboursIn_eq_filter_card]
  simp only [card_neighborFinset_eq_degree] at hh
  change (P.available.crossingSupport A).degree v ≤ (P.bootstrapSet A W v).card+W.card at hDelete
  omega

theorem bootstrap_from_support_discrepancy (P : M.PartialColouring k) (A W : Finset V) (v : V)
    (D : Finset V) (hSide : (v ∈ A ∧ D=Aᶜ) ∨ (v ∉ A ∧ D=A))
    (d ξ : ℝ) (hSupport : d ≤ (M.supportGraph.degree v:ℝ))
    (hDis : |(neighboursIn M.supportGraph A v:ℝ)-(neighboursIn M.supportGraph Aᶜ v:ℝ)| < ξ) :
    d-ξ < 2*((P.bootstrapSet A W v).card:ℝ)+2*(W.card:ℝ)+2*((P.graph.crossingSupport A).degree v:ℝ) := by
  have hSplit := OverfullWork.LowSetEdgePreprocessing.neighboursIn_add_compl M.supportGraph A v
  have hSplitR : (neighboursIn M.supportGraph A v:ℝ)+(neighboursIn M.supportGraph Aᶜ v:ℝ)=M.supportGraph.degree v := by
    exact_mod_cast hSplit
  have hOpp : ∀ x ∈ D, ¬(v ∈ A ↔ x ∈ A) := by
    intro x hx
    rcases hSide with ⟨hv,rfl⟩|⟨hv,rfl⟩
    · have hn := mem_compl.mp hx;tauto
    · tauto
  have hCountR : (neighboursIn M.supportGraph D v:ℝ) ≤
      (P.bootstrapSet A W v).card+(W.card:ℝ)+(P.graph.crossingSupport A).degree v := by
    exact_mod_cast P.opposite_support_bootstrap_bound A W v D hOpp
  rcases hSide with ⟨hv,hD⟩|⟨hv,hD⟩
  · rw [hD] at hCountR
    have hAbs := (abs_lt.mp hDis).2
    linarith
  · rw [hD] at hCountR
    have hAbs := (abs_lt.mp hDis).1
    linarith

end SimpleGraph.MultiGraph.PartialColouring
