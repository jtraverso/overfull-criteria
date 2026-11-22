module

public import OverfullWork.CMSOperation41CleanCutPrescriptions
public import OverfullWork.CMSOperation41CutSupport
public import OverfullWork.CMSOperation41PhysicalLayerFamily
public import OverfullWork.CMSOperation41RoundPrescription

@[expose] public section


/-! For S2.1 with an independent active set of size at least two,
attach all retired vertices that were not already in the replacement
words. Positive degree credits can then occur only at a current
exceptional vertex or at a vertex that has become isolated. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PrunedCore
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 3600000 in
private theorem attach_s2_1_retired_spokes (G H : SimpleGraph V) [DecidableRel G.Adj]
    (initial exceptional active : Finset V) (hExceptional : exceptional ⊆ initial)
    (hActive : active ⊆ exceptional) {f : ℕ}
    (S : TrimmingReplacementWords G initial (Fin f)) (hf : 0 < f)
    (hCard : 2*f ≤ active.card+1) (hGap : S.gaps.Nonempty)
    (hMarked : ∀ e ∈ S.gaps,∃ a ∈ active,∃ b ∈ active,e = s(a,b))
    (hBody : ∀ i,S.body i ≠ [])
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hLoad : ∀ i,projectionLoad (range j) used (S.endpoint i).val < cap ∨
      ∃ w ∈ active,H.Adj w (S.endpoint i).val ∧ S.prescribedGraph.Adj w (S.endpoint i).val)
    (hEdges : H ≤ S.prescribedGraph)
    (hInterior : ∀ i v,v ∈ S.body i → v ∉ active → ∃ w ∈ active,H.Adj w v)
    (hSpokes : ∀ v ∈ initial,v ∉ exceptional → 0 < G.degree v →
      initial.card+(active.card+1)+k+2*initial.card ≤ G.degree v) :
    ∃ (f : ℕ) (R : TrimmingReplacementWords G initial (Fin f)),
      0 < f ∧ 2*f ≤ active.card+1+2*initial.card ∧
      R.gaps.Nonempty ∧ R.coreIncidentGaps = ∅ ∧ (∀ i,R.body i ≠ []) ∧
      (∀ x y,R.prescribedGraph.Adj x y → x ∈ initial ∨ y ∈ initial) ∧
      (∀ v,v ∉ exceptional → 0 < G.degree v → R.degreeCredit ∅ v = 0) ∧
      (∀ i,projectionLoad (range j) used (R.endpoint i).val < cap ∨
        ∃ w ∈ active,H.Adj w (R.endpoint i).val ∧ R.prescribedGraph.Adj w (R.endpoint i).val) ∧
      (∀ (degree : V → ℕ) (d : ℕ),2 ≤ d →
        (∀ v,degree v ≤ d) →
        (∀ v ∈ initial,degree v = G.degree v) →
        (∀ v ∈ exceptional,degree v+2 ≤ d) →
        ∀ v,degree v+R.degreeCredit ∅ v ≤ d) ∧
      (active.card = 2 → ∀ w ∈ active,R.prescribedGraph.degree w = 1) ∧
      H ≤ R.prescribedGraph ∧ f ≤ initial.card ∧
      (∀ v ∈ exceptional,v ∉ active → 0 < R.prescribedGraph.degree v →
        ∃ w ∈ active,R.prescribedGraph.Adj w v) := by
  let B := (initial \ exceptional).filter (fun v => 0 < G.degree v ∧ ∀ i,v ∉ S.body i)
  have hBS : B ⊆ initial \ exceptional := filter_subset _ _
  have hB : B ⊆ initial := hBS.trans sdiff_subset
  have hBC : B.card ≤ initial.card := card_le_card hB
  have hCount : f+B.card ≤ initial.card := by
    have hDis : Disjoint active B :=
      Finset.disjoint_left.mpr (fun v ha hb => (mem_sdiff.mp (hBS hb)).2 (hActive ha))
    have hUnion := card_le_card (union_subset (hActive.trans hExceptional) hB)
    rw [card_union_of_disjoint hDis] at hUnion
    omega
  have hSupply (v : V) (hv : v ∈ B) :
      initial.card+2*Fintype.card (Fin f)+(∅ : Finset V).card+k+2*B.card ≤ G.degree v := by
    have hD := hSpokes v (hB hv) (mem_sdiff.mp (hBS hv)).2 (mem_filter.mp hv).2.1
    simp only [card_empty,add_zero,Fintype.card_fin]
    omega
  obtain ⟨T,hTGaps,hTEnds,hTOld,hTNew,_,hTFresh⟩ := S.exists_with_retired_spokes B ∅ hB
    (fun i v h hIn => (mem_filter.mp hIn).2.2 i h) (fun _ => notMem_empty _)
    used j cap k budget hCap hUsed hTotal hSupply
  let coord : Fin (f+B.card) ≃ Fin f ⊕ ↥B := (Fintype.equivFinOfCardEq (by simp)).symm
  let R := T.reindex coord
  have hRGaps : R.gaps = S.gaps := hTGaps
  have hOldEdges : S.prescribedGraph ≤ R.prescribedGraph := by
    intro u v hAdj
    obtain ⟨hNot,i,hPair⟩ := (S.prescribedGraph_adj u v).mp hAdj
    apply (R.prescribedGraph_adj u v).mpr
    refine ⟨by rwa [hRGaps],coord.symm (Sum.inl i),?_⟩
    have hWord : R.word (coord.symm (Sum.inl i)) = S.word i := by
      change T.word (coord (coord.symm (Sum.inl i))) = S.word i
      rw [Equiv.apply_symm_apply]
      simp only [TrimmingReplacementWords.word,hTEnds,hTOld]
    rwa [hWord]
  have hRBody (i : Fin (f+B.card)) : R.body i ≠ [] := by
    change T.body (coord i) ≠ []
    cases h : coord i with
    | inl i' => exact hTOld i' ▸ hBody i'
    | inr v => rw [hTNew]; simp
  have hPays (v : V) (hv : v ∈ exceptional) (hna : v ∉ active)
      (hPos : 0 < R.prescribedGraph.degree v) : ∃ w ∈ active,R.prescribedGraph.Adj w v := by
    have hOccur : ∃ i,v ∈ R.body i := by
      by_contra! h
      have hz := R.prescribed_degree_eq_zero_of_absent_body (hExceptional hv) h
      omega
    obtain ⟨i,hi⟩ := hOccur
    change v ∈ T.body (coord i) at hi
    cases h : coord i with
    | inl t =>
      rw [h,hTOld] at hi
      obtain ⟨w,hw,he⟩ := hInterior t v hi hna
      exact ⟨w,hw,hOldEdges (hEdges he)⟩
    | inr x =>
      rw [h,hTNew,List.mem_singleton] at hi
      exact ((mem_sdiff.mp (hBS x.property)).2 (hi ▸ hv)).elim
  have hCore : R.coreIncidentGaps = ∅ := by
    apply R.core_incident_gaps_eq_empty_of_exceptional_pairs
    intro edge he
    obtain ⟨a,ha,b,hb,hEq⟩ := hMarked edge (hRGaps ▸ he)
    exact ⟨a,hExceptional (hActive ha),b,hExceptional (hActive hb),hEq⟩
  have hRetired (v : V) (hv : v ∉ exceptional) (hp : 0 < G.degree v) :
      R.degreeCredit ∅ v = 0 := by
    by_cases hi : v ∈ initial
    · have hOccur : ∃ i,v ∈ R.body i := by
        by_cases hAlready : ∃ i,v ∈ S.body i
        · obtain ⟨i,hi⟩ := hAlready
          refine ⟨coord.symm (Sum.inl i),?_⟩
          change v ∈ T.body (coord (coord.symm (Sum.inl i)))
          rwa [Equiv.apply_symm_apply,hTOld]
        · have hMem : v ∈ B := mem_filter.mpr
            ⟨mem_sdiff.mpr ⟨hi,hv⟩,hp,fun i h => hAlready ⟨i,h⟩⟩
          let v' : B := ⟨v,hMem⟩
          refine ⟨coord.symm (Sum.inr v'),?_⟩
          change v ∈ T.body (coord (coord.symm (Sum.inr v')))
          rw [Equiv.apply_symm_apply,hTNew]
          exact List.mem_cons_self
      rw [TrimmingReplacementWords.degreeCredit,if_pos (Or.inr hOccur),
        trimming_gap_degree_eq_card_incident_pairs]
      apply card_eq_zero.mpr
      apply eq_empty_of_forall_notMem
      intro edge he
      obtain ⟨a,ha,b,hb,rfl⟩ := hMarked edge (hRGaps ▸ (mem_filter.mp he).1)
      exact (Sym2.mem_iff.mp (mem_filter.mp he).2.1).elim
        (fun h => hv (h ▸ hActive ha)) (fun h => hv (h ▸ hActive hb))
    · exact R.degree_credit_eq_zero_on_core_of_no_core_gaps hCore hi
  refine ⟨f+B.card,R,by omega,by omega,hRGaps.symm ▸ hGap,hCore,hRBody,
    R.prescribedGraph_meets_exceptional_set (fun i h => (hRBody i h).elim),hRetired,?_,?_,?_,
    hEdges.trans hOldEdges,hCount,hPays⟩
  · rintro ⟨i,side⟩
    change projectionLoad (range j) used (T.endpoint (coord i,side)).val < cap ∨
      ∃ w ∈ active,H.Adj w (T.endpoint (coord i,side)).val ∧
        R.prescribedGraph.Adj w (T.endpoint (coord i,side)).val
    cases h : coord i with
    | inl i' =>
      rw [hTEnds]
      exact (hLoad (i',side)).imp_right (fun ⟨w,hw,hMatch,hEdge⟩ => ⟨w,hw,hMatch,hOldEdges hEdge⟩)
    | inr v => exact Or.inl (hTFresh v side)
  · intro degree d hD hBound hExact hDef v
    have hCredit := R.degree_credit_le_two ∅ v
    by_cases he : v ∈ exceptional
    · exact (Nat.add_le_add_left hCredit _).trans (hDef v he)
    by_cases hi : v ∈ initial
    · by_cases hp : 0 < G.degree v
      · rw [hRetired v he hp,Nat.add_zero]
        exact hBound v
      · have hz : degree v = 0 := by rw [hExact v hi]; omega
        omega
    · rw [R.degree_credit_eq_zero_on_core_of_no_core_gaps hCore hi,Nat.add_zero]
      exact hBound v
  · intro hPair
    exact R.prescribed_degree_one_on_active_pair active (hActive.trans hExceptional) hPair
      (hRGaps.symm ▸ hGap) (fun e he => hMarked e (hRGaps ▸ he))

theorem exists_independent_s2_1_with_retired_spokes (G : SimpleGraph V) [DecidableRel G.Adj]
    (initial exceptional active : Finset V) (hExceptional : exceptional ⊆ initial)
    (hActive : active ⊆ exceptional) (hIndependent : G.IsIndepSet (active : Set V))
    (hStrict : ∀ w ∈ active,∀ x,G.Adj w x → neighboursIn G active x < G.degree w)
    (hPos : ∀ w ∈ active,0 < G.degree w) (hSize : 2 ≤ active.card)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hProjection : ∀ v ∈ initial,v ∉ active → 0 < G.degree v →
      initial.card+4*(active.card+1)+k ≤ G.degree v)
    (hSpokes : ∀ v ∈ initial,v ∉ exceptional → 0 < G.degree v →
      initial.card+(active.card+1)+k+2*initial.card ≤ G.degree v) :
    ∃ (H : SimpleGraph V) (f : ℕ) (R : TrimmingReplacementWords G initial (Fin f)),
      0 < f ∧ 2*f ≤ active.card+1+2*initial.card ∧
      R.gaps.Nonempty ∧ R.coreIncidentGaps = ∅ ∧ (∀ i,R.body i ≠ []) ∧
      (∀ x y,R.prescribedGraph.Adj x y → x ∈ initial ∨ y ∈ initial) ∧
      (∀ v,v ∉ exceptional → 0 < G.degree v → R.degreeCredit ∅ v = 0) ∧
      (∀ i,projectionLoad (range j) used (R.endpoint i).val < cap ∨
        ∃ w ∈ active,H.Adj w (R.endpoint i).val ∧ R.prescribedGraph.Adj w (R.endpoint i).val) ∧
      (∀ (degree : V → ℕ) (d : ℕ),2 ≤ d →
        (∀ v,degree v ≤ d) →
        (∀ v ∈ initial,degree v = G.degree v) →
        (∀ v ∈ exceptional,degree v+2 ≤ d) →
        ∀ v,degree v+R.degreeCredit ∅ v ≤ d) ∧
      f ≤ initial.card ∧ (∀ w ∈ active,1 ≤ R.prescribedGraph.degree w) ∧
      (∀ v ∈ exceptional,v ∉ active → 0 < R.prescribedGraph.degree v →
        ∃ w ∈ active,R.prescribedGraph.Adj w v) := by
  obtain ⟨H,_,S,hs,hf,hCard,hGap,_,hMarked,hBody,hLoad,hEdges,hInterior⟩ :=
    exists_clean_independent_s2_1_prescription_of_strict_comparison G active initial
      (hActive.trans hExceptional) hIndependent hStrict hPos hSize used j cap k budget
      hCap hUsed hTotal hProjection
  obtain ⟨f,R,hf',hCard',hGap',hCore,hBody',hMeet,hRetired,hLoad',hDegree,_,hKeep,hCount,hPays⟩ :=
    attach_s2_1_retired_spokes G H initial exceptional active hExceptional hActive
      S hf hCard hGap hMarked hBody used j cap k budget hCap hUsed hTotal hLoad hEdges hInterior hSpokes
  exact ⟨H,f,R,hf',hCard',hGap',hCore,hBody',hMeet,hRetired,hLoad',hDegree,hCount,
    fun w hw => (hs.low_positive w hw).trans (degree_le_of_le hKeep),hPays⟩

/-- The independent active set of size at least two produces a full
Step 2 certificate, including the deleted edges that pay for projection. -/
theorem exists_independent_trimming_prescription (G : SimpleGraph V) [DecidableRel G.Adj]
    (initial exceptional active : Finset V) (hExceptional : exceptional ⊆ initial)
    (hActive : active ⊆ exceptional) (hIndependent : G.IsIndepSet (active : Set V))
    (hStrict : ∀ w ∈ active,∀ x,G.Adj w x → neighboursIn G active x < G.degree w)
    (hPos : ∀ w ∈ active,0 < G.degree w) (hSize : 2 ≤ active.card)
    (hCore : 3 ≤ initialᶜ.card) (degree : V → ℕ) (d : ℕ) (hD : 2 ≤ d)
    (hBound : ∀ v,degree v ≤ d) (hExact : ∀ v ∈ initial,degree v = G.degree v)
    (hDef : ∀ v ∈ exceptional,degree v+2 ≤ d)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hProjection : ∀ v ∈ initial,v ∉ active → 0 < G.degree v →
      initial.card+4*(active.card+1)+k ≤ G.degree v)
    (hSpokes : ∀ v ∈ initial,v ∉ exceptional → 0 < G.degree v →
      initial.card+(active.card+1)+k+2*initial.card ≤ G.degree v) :
    ∃ R : TrimmingRoundPrescription G initial degree d,
      R.size ≤ initial.card ∧ R.omitted = ∅ ∧
      (∀ w ∈ active,1 ≤ R.words.prescribedGraph.degree w) ∧
      (∀ v,v ∉ exceptional → 0 < G.degree v → R.words.degreeCredit R.omitted v = 0) ∧
      (∀ i,projectionLoad (range j) used (R.words.endpoint i).val < cap ∨
        ∃ w ∈ active,R.words.prescribedGraph.Adj w (R.words.endpoint i).val) ∧
      (∀ v ∈ exceptional,v ∉ active → 0 < R.words.prescribedGraph.degree v →
        ∃ w ∈ active,R.words.prescribedGraph.Adj w v) := by
  obtain ⟨H,f,R,_,_,hGap,hNoCore,hBody,_,hRetired,hLoad,hDegree,hCount,hAtLeast,hPays⟩ :=
    exists_independent_s2_1_with_retired_spokes G initial exceptional active hExceptional hActive
      hIndependent hStrict hPos hSize used j cap k budget hCap hUsed hTotal hProjection hSpokes
  let C : TrimmingRoundPrescription G initial degree d :=
    { size := f
      words := R
      omitted := ∅
      endpoints_retained := fun _ => notMem_empty _
      core_credit_bound := by simp [hNoCore]
      empty_body_is_gap := fun i h => (hBody i h).elim
      minimum_length := by simpa only [card_empty,Nat.sub_zero] using hCore.trans (Nat.le_add_right _ _)
      even_or_gap := Or.inr hGap
      degree_cap := hDegree degree d hD hBound hExact hDef }
  refine ⟨C,hCount,rfl,hAtLeast,hRetired,?_,hPays⟩
  intro i
  rcases hLoad i with h | ⟨w,hw,_,he⟩
  · exact Or.inl h
  · exact Or.inr ⟨w,hw,he⟩

set_option maxHeartbeats 2700000 in
theorem exists_inherited_pair_trimming_prescription (G : SimpleGraph V) [DecidableRel G.Adj]
    (initial exceptional active : Finset V) (hExceptional : exceptional ⊆ initial)
    (hActive : active ⊆ exceptional) (hPair : active.card = 2)
    (hPos : ∀ w ∈ active,6 ≤ G.degree w) (hSize : 3 ≤ (initialᶜ : Finset V).card)
    (degree : V → ℕ) (d : ℕ) (hD : 2 ≤ d) (hBound : ∀ v,degree v ≤ d)
    (hExact : ∀ v ∈ initial,degree v = G.degree v)
    (hDef : ∀ v ∈ exceptional,degree v+2 ≤ d)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hProjection : ∀ v ∈ initial,v ∉ active → 0 < G.degree v →
      initial.card+4*(active.card+1)+k ≤ G.degree v)
    (hSpokes : ∀ v ∈ initial,v ∉ exceptional → 0 < G.degree v →
      initial.card+(active.card+1)+k+2*initial.card ≤ G.degree v) :
    ∃ R : TrimmingRoundPrescription G initial degree d,
      R.size ≤ initial.card ∧ R.omitted = ∅ ∧
      (∀ w ∈ active,R.words.prescribedGraph.degree w = 1) ∧
      (∀ v,v ∉ exceptional → 0 < G.degree v → R.words.degreeCredit R.omitted v = 0) ∧
      (∀ i,projectionLoad (range j) used (R.words.endpoint i).val < cap ∨
        ∃ w ∈ active,R.words.prescribedGraph.Adj w (R.words.endpoint i).val) ∧
      (∀ v ∈ exceptional,v ∉ active → 0 < R.words.prescribedGraph.degree v →
        ∃ w ∈ active,R.words.prescribedGraph.Adj w v) := by
  obtain ⟨H,_,S,_,hf,hCard,hGap,_,hMarked,hBody,hLoad,hEdges,hInterior⟩ :=
    exists_inherited_pair_s2_1_prescription_of_projection_room G active initial
      (hActive.trans hExceptional) hPair hPos used j cap k budget hCap hUsed hTotal hProjection
  obtain ⟨f,R,_,_,hGap',hCore,hBody',_,hRetired,hLoad',hDegree,hOne,_,hCount,hPays⟩ :=
    attach_s2_1_retired_spokes G H initial exceptional active hExceptional hActive
      S hf hCard hGap hMarked hBody used j cap k budget hCap hUsed hTotal hLoad hEdges hInterior hSpokes
  let C : TrimmingRoundPrescription G initial degree d :=
    { size := f
      words := R
      omitted := ∅
      endpoints_retained := fun _ => notMem_empty _
      core_credit_bound := by simp [hCore]
      empty_body_is_gap := fun i h => (hBody' i h).elim
      minimum_length := by simpa only [card_empty,Nat.sub_zero] using hSize.trans (Nat.le_add_right _ _)
      even_or_gap := Or.inr hGap'
      degree_cap := hDegree degree d hD hBound hExact hDef }
  refine ⟨C, hCount, rfl, hOne hPair, hRetired, ?_, hPays⟩
  intro i
  rcases hLoad' i with h | ⟨w,hw,_,he⟩
  · exact Or.inl h
  · exact Or.inr ⟨w,hw,he⟩

end OverfullWork.CMSTrimmingRound
