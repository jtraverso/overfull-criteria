module

public import OverfullWork.CMSOperation41SkeletonPrescriptions

@[expose] public section


/-! Case S2.1 for an independent active set. Construct the appropriate
matching skeleton, choose its free representatives within the history
cap, and pass its marked replacement words to the core packing. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PaperLowSkeleton LowSkeletonPreparation LowVertexMatchingAbsorption
open PrunedCore
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem exists_capped_projection_of_skeleton (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (W U : Finset V) (hs : IsSkeleton G H W)
    (used : ℕ → Finset V) (j cap k b : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ b) (hTotal : j*b ≤ k*cap)
    (hDegree : ∀ v ∈ U,v ∉ W → 0 < G.degree v → U.card+4*(W.card+1)+k ≤ G.degree v) :
    let S := univ.filter fun v : V => cap ≤ projectionLoad (range j) used v
    ∃ P : LowSkeletonProjection.Projection G (outerLeaves H W) U (nonisolatedVertices H∪S),
      ∀ a : outerLeaves H W,a.val ∈ U → projectionLoad (range j) used (P.representative a).val < cap := by
  have hZ : (nonisolatedVertices H).card ≤ 2*(W.card+1) :=
    (nonisolatedVertices_card_le_twice_edges H).trans (Nat.mul_le_mul_left 2 hs.edge_bound)
  have hA : (outerLeaves H W).card ≤ W.card+1 := hs.outer_card_le
  exact exists_projection_with_free_load_cap G (outerLeaves H W) U (nonisolatedVertices H)
    (range j) used cap k b hCap (fun i hi => hUsed i (mem_range.mp hi))
    (by simpa only [card_range] using hTotal) (fun v hv => by
      obtain ⟨hA',hU⟩ := mem_inter.mp hv
      have hNotW := mem_compl.mp (mem_filter.mp hA').1
      have hOne := (mem_filter.mp hA').2
      have hLe := SimpleGraph.degree_le_of_le hs.le_graph (v := v)
      have hAvail := hDegree v hU hNotW (by omega)
      omega)

private theorem capped_or_matching_endpoint {G H : SimpleGraph V} [DecidableRel H.Adj]
    {W U Z : Finset V}
    (P : LowSkeletonProjection.Projection G (outerLeaves H W) U Z)
    (used : ℕ → Finset V) (j cap : ℕ)
    (hFresh : ∀ a : outerLeaves H W,a.val ∈ U → projectionLoad (range j) used (P.representative a).val < cap)
    {f : ℕ} (R : TrimmingReplacementWords G U (Fin f))
    (hRange : ∀ v,v ∈ Set.range R.endpoint ↔ ∃ a : outerLeaves H W,P.representative a = v)
    (hFixed : ∀ a : outerLeaves H W,a.val ∉ U → ∃ w ∈ W,H.Adj w a.val ∧ R.prescribedGraph.Adj w a.val) :
    ∀ i,projectionLoad (range j) used (R.endpoint i).val < cap ∨
      ∃ w ∈ W,H.Adj w (R.endpoint i).val ∧ R.prescribedGraph.Adj w (R.endpoint i).val := by
  intro i
  obtain ⟨a,ha⟩ := (hRange _).mp ⟨i,rfl⟩
  by_cases h : a.val ∈ U
  · exact Or.inl (ha ▸ hFresh a h)
  · obtain ⟨w,hw,hAdj,hEdge⟩ := hFixed a h
    have hEqual : (R.endpoint i).val = a.val := (congrArg Subtype.val ha).symm.trans (P.fixed a h)
    exact Or.inr ⟨w,hw,hEqual.symm ▸ hAdj,hEqual.symm ▸ hEdge⟩

set_option maxHeartbeats 2400000 in
private theorem capped_s2_1_prescription_of_even_matching (G M : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel M.Adj] (W U : Finset V) (hWU : W ⊆ U)
    (hEven : Even W.card) (hSize : 2 ≤ W.card) (hLe : M ≤ G) (hm : OneFactor.IsMatchingGraph M)
    (hCover : ∀ w ∈ W,∃! v,M.Adj w v)
    (hCross : ∀ u v,M.Adj u v → (u ∈ W ∧ v ∉ W) ∨ (v ∈ W ∧ u ∉ W))
    (hColour : M.EdgeColorable 2)
    (used : ℕ → Finset V) (j cap k b : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ b) (hTotal : j*b ≤ k*cap)
    (hDegree : ∀ v ∈ U,v ∉ W → 0 < G.degree v → U.card+4*(W.card+1)+k ≤ G.degree v) :
    ∃ (f : ℕ) (R : TrimmingReplacementWords G U (Fin f)),
      IsSkeleton G M W ∧ 0 < f ∧ 2*f ≤ W.card+1 ∧ R.gaps.Nonempty ∧ R.coreIncidentGaps = ∅ ∧
      (∀ edge ∈ R.gaps,∃ a ∈ W,∃ b ∈ W,edge = s(a,b)) ∧
      (∀ i,R.body i ≠ []) ∧
      (∀ i,projectionLoad (range j) used (R.endpoint i).val < cap ∨
        ∃ w ∈ W,M.Adj w (R.endpoint i).val ∧ R.prescribedGraph.Adj w (R.endpoint i).val) ∧
      M ≤ R.prescribedGraph ∧
      (∀ i v,v ∈ R.body i → v ∉ W → ∃ w ∈ W,M.Adj w v) := by
  have hs := isSkeleton_of_even_matching G M W hLe hm hCover hCross hSize hEven hColour
  obtain ⟨P,hFresh⟩ := exists_capped_projection_of_skeleton G M W U hs used j cap k b
    hCap hUsed hTotal hDegree
  obtain ⟨f,R,hf,hCard,hGap,hNoCore,hMarked,hBody,hRange,hFixed,hEdges,hInterior⟩ :=
    exists_even_skeleton_prescription hWU hs hm P
  exact ⟨f,R,hs,hf,hCard.trans_le hs.outer_card_le,hGap,hNoCore,hMarked,hBody,
    capped_or_matching_endpoint P used j cap hFresh R hRange hFixed,hEdges,hInterior⟩

set_option maxHeartbeats 3200000 in
theorem exists_clean_independent_s2_1_prescription_of_strict_comparison
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W U : Finset V) (hWU : W ⊆ U) (hIndependent : G.IsIndepSet (W : Set V))
    (hCompare : ∀ w ∈ W,∀ x,G.Adj w x → neighboursIn G W x < G.degree w)
    (hPos : ∀ w ∈ W,0 < G.degree w) (hSize : 2 ≤ W.card)
    (used : ℕ → Finset V) (j cap k b : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ b) (hTotal : j*b ≤ k*cap)
    (hDegree : ∀ v ∈ U,v ∉ W → 0 < G.degree v → U.card+4*(W.card+1)+k ≤ G.degree v) :
    ∃ (H : SimpleGraph V) (f : ℕ) (R : TrimmingReplacementWords G U (Fin f)),
      IsSkeleton G H W ∧ 0 < f ∧ 2*f ≤ W.card+1 ∧ R.gaps.Nonempty ∧ R.coreIncidentGaps = ∅ ∧
      (∀ edge ∈ R.gaps,∃ a ∈ W,∃ b ∈ W,edge = s(a,b)) ∧
      (∀ i,R.body i ≠ []) ∧
      (∀ i,projectionLoad (range j) used (R.endpoint i).val < cap ∨
        ∃ w ∈ W,H.Adj w (R.endpoint i).val ∧ R.prescribedGraph.Adj w (R.endpoint i).val) ∧
      H ≤ R.prescribedGraph ∧
      (∀ i v,v ∈ R.body i → v ∉ W → ∃ w ∈ W,H.Adj w v) := by
  by_cases hEven : Even W.card
  · obtain ⟨M₁,M₂,hM₁,_,hm₁,hm₂,hDis,hCover₁,_,hCross₁,_⟩ :=
      two_matchings_of_strict_independent_cut G W hIndependent hCompare hPos
    have hUnion := (two_matching_union_colouring M₁ M₂ hm₁ hm₂ hDis).1
    have hMColour := Critical.colourable_of_copy (Copy.ofLE M₁ (M₁⊔M₂) le_sup_left) hUnion
    obtain ⟨f,R,hRest⟩ := capped_s2_1_prescription_of_even_matching G M₁ W U hWU hEven hSize
      hM₁ hm₁ hCover₁ hCross₁ hMColour used j cap k b hCap hUsed hTotal hDegree
    exact ⟨M₁,f,R,hRest⟩
  · have hOdd := Nat.not_even_iff_odd.mp hEven
    have hThree : 3 ≤ W.card := by obtain ⟨a,ha⟩ := hOdd; omega
    obtain ⟨M₁,M₂,w,a,b',hM₁,hM₂,hm₁,hm₂,hDis,hCover₁,hCover₂,hw,hwa,hwb,hFreshB,
      hs,hDegreeB,hOuter,ha,hb,hab⟩ :=
      exists_odd_skeleton_of_clean_independent_cut G W hIndependent hCompare hPos hThree hOdd
    have hbOut : b' ∉ W := fun h => hIndependent hw h (hM₂ hwb).ne (hM₂ hwb)
    have hFour : 4 ≤ (outerLeaves (M₁⊔SimpleGraph.edge w b') W).card := by omega
    obtain ⟨P,hFresh⟩ := exists_capped_projection_of_skeleton G (M₁⊔SimpleGraph.edge w b') W U hs
      used j cap k b hCap hUsed hTotal hDegree
    obtain ⟨f,R,hf,hCard,hGap,hNoCore,hMarked,hBody,hRange,hFixed,hEdges,hInterior⟩ :=
      exists_odd_skeleton_prescription hWU hm₁ hw hwa hbOut hab hs ha hb hFour P
    have hs' : @IsSkeleton V _ _ G (M₁⊔SimpleGraph.edge w b') (Classical.decRel _) W := by
      have hDec : (inferInstance : DecidableRel (M₁⊔SimpleGraph.edge w b').Adj) = Classical.decRel _ :=
        Subsingleton.elim _ _
      rw [←hDec]
      exact hs
    exact ⟨M₁⊔SimpleGraph.edge w b',f,R,hs',by omega,hCard.trans_le hs.outer_card_le,hGap,hNoCore,hMarked,hBody,
      capped_or_matching_endpoint P used j cap hFresh R hRange hFixed,hEdges,hInterior⟩

theorem exists_clean_independent_s2_1_prescription (G : SimpleGraph V) [DecidableRel G.Adj]
    (W U : Finset V) (hWU : W ⊆ U) (hIndependent : G.IsIndepSet (W : Set V))
    (hReady : CleanedSourceVAL.IsReady G W) (hPos : ∀ w ∈ W,0 < G.degree w) (hSize : 2 ≤ W.card)
    (used : ℕ → Finset V) (j cap k b : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ b) (hTotal : j*b ≤ k*cap)
    (hDegree : ∀ v ∈ U,v ∉ W → U.card+4*(W.card+1)+k ≤ G.degree v) :
    ∃ (H : SimpleGraph V) (f : ℕ) (R : TrimmingReplacementWords G U (Fin f)),
      IsSkeleton G H W ∧ 0 < f ∧ 2*f ≤ W.card+1 ∧ R.gaps.Nonempty ∧ R.coreIncidentGaps = ∅ ∧
      ∀ i,projectionLoad (range j) used (R.endpoint i).val < cap ∨
        ∃ w ∈ W,H.Adj w (R.endpoint i).val := by
  have hCompare := MaximumNeighbourCleanup.hall_of_final_inequality G W hReady.1 hReady.2
  obtain ⟨H,f,R,hs,hf,hCard,hGap,hNoCore,_,_,hLoad,_,_⟩ :=
    exists_clean_independent_s2_1_prescription_of_strict_comparison G W U hWU hIndependent
      hCompare hPos hSize used j cap k b hCap hUsed hTotal (fun v hv hw _ => hDegree v hv hw)
  exact ⟨H,f,R,hs,hf,hCard,hGap,hNoCore,fun i => (hLoad i).imp_right
    (fun ⟨w,hw,hAdj,_⟩ => ⟨w,hw,hAdj⟩)⟩

set_option maxHeartbeats 1800000 in
/-- S2.1 for an inherited active pair. The degree lower bound gives two
crossing matchings even if the two active vertices are adjacent. -/
theorem exists_inherited_pair_s2_1_prescription_of_projection_room (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (W U : Finset V) (hWU : W ⊆ U) (hSize : W.card = 2)
    (hActiveDegree : ∀ w ∈ W,6 ≤ G.degree w)
    (used : ℕ → Finset V) (j cap k b : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ b) (hTotal : j*b ≤ k*cap)
    (hDegree : ∀ v ∈ U,v ∉ W → 0 < G.degree v → U.card+4*(W.card+1)+k ≤ G.degree v) :
    ∃ (H : SimpleGraph V) (f : ℕ) (R : TrimmingReplacementWords G U (Fin f)),
      IsSkeleton G H W ∧ 0 < f ∧ 2*f ≤ W.card+1 ∧ R.gaps.Nonempty ∧ R.coreIncidentGaps = ∅ ∧
      (∀ edge ∈ R.gaps,∃ a ∈ W,∃ b ∈ W,edge = s(a,b)) ∧
      (∀ i,R.body i ≠ []) ∧
      (∀ i,projectionLoad (range j) used (R.endpoint i).val < cap ∨
        ∃ w ∈ W,H.Adj w (R.endpoint i).val ∧ R.prescribedGraph.Adj w (R.endpoint i).val) ∧
      H ≤ R.prescribedGraph ∧
      (∀ i v,v ∈ R.body i → v ∉ W → ∃ w ∈ W,H.Adj w v) := by
  obtain ⟨M₁,M₂,hM₁,hM₂,hm₁,hm₂,hDis,hCover₁,hCover₂,hCross₁,hCross₂⟩ :=
    two_matchings_of_high_degree_cut G W (by simpa only [hSize] using hActiveDegree)
  have hUnion := (two_matching_union_colouring M₁ M₂ hm₁ hm₂ hDis).1
  have hMColour := Critical.colourable_of_copy (Copy.ofLE M₁ (M₁⊔M₂) le_sup_left) hUnion
  obtain ⟨f,R,h⟩ := capped_s2_1_prescription_of_even_matching G M₁ W U hWU
    (by rw [hSize]; decide) (by omega) hM₁ hm₁ hCover₁ hCross₁ hMColour
    used j cap k b hCap hUsed hTotal hDegree
  exact ⟨M₁,f,R,h⟩

theorem exists_inherited_pair_s2_1_prescription (G : SimpleGraph V) [DecidableRel G.Adj]
    (W U : Finset V) (hWU : W ⊆ U) (hSize : W.card = 2)
    (hActiveDegree : ∀ w ∈ W,6 ≤ G.degree w)
    (used : ℕ → Finset V) (j cap k b : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ b) (hTotal : j*b ≤ k*cap)
    (hDegree : ∀ v ∈ U,v ∉ W → U.card+4*(W.card+1)+k ≤ G.degree v) :
    ∃ (H : SimpleGraph V) (f : ℕ) (R : TrimmingReplacementWords G U (Fin f)),
      IsSkeleton G H W ∧ 0 < f ∧ 2*f ≤ W.card+1 ∧ R.gaps.Nonempty ∧ R.coreIncidentGaps = ∅ ∧
      ∀ i,projectionLoad (range j) used (R.endpoint i).val < cap ∨
        ∃ w ∈ W,H.Adj w (R.endpoint i).val := by
  obtain ⟨H,f,R,hs,hf,hCard,hGap,hNoCore,_,_,hLoad,_,_⟩ :=
    exists_inherited_pair_s2_1_prescription_of_projection_room G W U hWU hSize hActiveDegree
      used j cap k b hCap hUsed hTotal (fun v hv hw _ => hDegree v hv hw)
  exact ⟨H,f,R,hs,hf,hCard,hGap,hNoCore,fun i => (hLoad i).imp_right
    (fun ⟨w,hw,hAdj,_⟩ => ⟨w,hw,hAdj⟩)⟩

end OverfullWork.CMSTrimmingRound
