module

public import OverfullWork.LowSetEdgePreprocessing

@[expose] public section


/-! The auxiliary graph of Operation 4.1 may still contain core edges
already counted as deleted. Algorithm 1 only reads low-set incidences,
which agree with the physical graph. The same finite deletion trace
therefore preserves the physical obstruction. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PrunedCore LowSetEdgePreprocessing
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_auxiliary_low_preprocessing (G : SimpleGraph V) (W : Finset V) :
    ∃ H : SimpleGraph V,DeletionRun W G H ∧ H ≤ G ∧
      ∀ w ∈ W,∀ x,H.Adj w x → neighboursIn H W x < H.degree w := by
  classical
  let P (m : ℕ) := ∃ H : SimpleGraph V,DeletionRun W G H ∧ H ≤ G ∧ H.edgeSet.ncard = m
  have hExists : ∃ m,P m := ⟨G.edgeSet.ncard,G,DeletionRun.refl G,le_rfl,rfl⟩
  obtain ⟨H,hRun,hLe,hCard⟩ := Nat.find_spec hExists
  refine ⟨H,hRun,hLe,?_⟩
  intro w hw x hAdj
  by_contra! hBad
  let R := H.deleteEdges {s(w,x)}
  have hSmall : R.edgeSet.ncard < Nat.find hExists := by
    rw [←hCard]
    apply Set.ncard_lt_ncard _ (Set.toFinite _)
    rw [edgeSet_deleteEdges]
    exact Set.sdiff_ssubset_left_iff.mpr ⟨s(w,x),hAdj,rfl⟩
  exact Nat.find_min hExists hSmall
    ⟨R,DeletionRun.step hRun hw hAdj hBad,(deleteEdges_le _).trans hLe,rfl⟩

theorem exists_independent_active_cleanup (G : SimpleGraph V) (W : Finset V)
    (hIndependent : G.IsIndepSet (W : Set V)) :
    ∃ T : SimpleGraph V,
      let A := W.filter (fun w => 0 < T.degree w)
      DeletionRun W G T ∧ T ≤ G ∧ T.IsIndepSet (A : Set V) ∧
        ∀ w ∈ A,∀ x,T.Adj w x → neighboursIn T A x < T.degree w := by
  obtain ⟨T,hRun,hLe,hStrict⟩ := exists_auxiliary_low_preprocessing G W
  let A := W.filter (fun w => 0 < T.degree w)
  have hSub : A ⊆ W := filter_subset _ _
  exact ⟨T,hRun,hLe,fun u hu v hv hne h => hIndependent (hSub hu) (hSub hv) hne (hLe h),
    fun w hw x h => (neighboursIn_mono T hSub x).trans_lt (hStrict w (hSub hw) x h)⟩

set_option maxHeartbeats 1700000 in
theorem replay_auxiliary_low_preprocessing_on {G T : SimpleGraph V} {W Z : Finset V}
    (p : DeletionRun W G T) (hWZ : W ⊆ Z) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hSame : ∀ w ∈ Z,∀ x,H.Adj w x ↔ G.Adj w x)
    (hSmall : ∀ w ∈ W,H.degree w < H.maxDegree)
    (hNC : ¬H.EdgeColorable H.maxDegree) :
    ∃ R : SimpleGraph V,DeletionRun W H R ∧ R ≤ H ∧ R.maxDegree = H.maxDegree ∧
      ¬R.EdgeColorable R.maxDegree ∧
      (∀ w ∈ Z,∀ x,R.Adj w x ↔ T.Adj w x) ∧
      R.induce ((W : Set V)ᶜ) = H.induce ((W : Set V)ᶜ) := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableRel H.Adj)
    (fun u v => Classical.propDecidable (H.Adj u v))
  induction p with
  | refl => exact ⟨H,DeletionRun.refl H,le_rfl,rfl,hNC,hSame,rfl⟩
  | @step U dU p w x hw hEdge hBad ih =>
    obtain ⟨S,hRun,hLe,hMax,hUncol,hSync,hInduce⟩ := ih
    have hDegree : S.degree w = U.degree w := by
      rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
      congr 1
      ext v
      simp only [mem_neighborFinset]
      exact hSync w (hWZ hw) v
    have hCount : neighboursIn S W x = neighboursIn U W x := by
      unfold neighboursIn
      congr 1
      ext v
      simp only [mem_filter,mem_neighborFinset]
      exact and_congr_left (fun hv => (S.adj_comm x v).trans ((hSync v (hWZ hv) x).trans (U.adj_comm v x)))
    have hBadS : S.degree w ≤ neighboursIn S W x := by rwa [hDegree,hCount]
    have hEdgeS : S.Adj w x := (hSync w (hWZ hw) x).mpr hEdge
    have hSmallS (v : V) (hv : v ∈ W) : S.degree v < S.maxDegree := by
      rw [hMax]
      exact (S.degree_le_of_le hLe).trans_lt (hSmall v hv)
    let R := S.deleteEdges {s(w,x)}
    let : DecidableRel R.Adj := Classical.decRel _
    have hLe' : R ≤ H := (deleteEdges_le _).trans hLe
    have hNoH : ¬R.EdgeColorable H.maxDegree := by
      intro hColour
      apply hUncol
      apply (colourable_iff_delete_bad_edge S W hSmallS hw hBadS).mpr
      rwa [hMax]
    have hMax' : R.maxDegree = H.maxDegree := Critical.maxDegree_eq_of_obstruction hLe' hNoH
    refine ⟨R,DeletionRun.step hRun hw hEdgeS hBadS,hLe',hMax',by rwa [hMax'],?_,?_⟩
    · intro v hv z
      change (S.deleteEdges {s(w,x)}).Adj v z ↔ (U.deleteEdges {s(w,x)}).Adj v z
      simp only [deleteEdges_adj,hSync v hv z]
    · exact (induce_compl_delete_bad_edge S W hw).trans hInduce

theorem replay_auxiliary_low_preprocessing {G T : SimpleGraph V} {W : Finset V}
    (p : DeletionRun W G T) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hSame : ∀ w ∈ W,∀ x,H.Adj w x ↔ G.Adj w x)
    (hSmall : ∀ w ∈ W,H.degree w < H.maxDegree)
    (hNC : ¬H.EdgeColorable H.maxDegree) :
    ∃ R : SimpleGraph V,DeletionRun W H R ∧ R ≤ H ∧ R.maxDegree = H.maxDegree ∧
      ¬R.EdgeColorable R.maxDegree ∧
      (∀ w ∈ W,∀ x,R.Adj w x ↔ T.Adj w x) ∧
      R.induce ((W : Set V)ᶜ) = H.induce ((W : Set V)ᶜ) := by
  exact replay_auxiliary_low_preprocessing_on p Subset.rfl H hSame hSmall hNC

theorem exists_synchronised_low_preprocessing (G H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Finset V) (hInd : G.IsIndepSet (W : Set V))
    (hSame : ∀ w ∈ W,∀ x,H.Adj w x ↔ G.Adj w x)
    (hSmall : ∀ w ∈ W,H.degree w < H.maxDegree)
    (hNC : ¬H.EdgeColorable H.maxDegree) :
    ∃ T R : SimpleGraph V,DeletionRun W G T ∧ DeletionRun W H R ∧ T ≤ G ∧ R ≤ H ∧
      R.maxDegree = H.maxDegree ∧ ¬R.EdgeColorable R.maxDegree ∧
      (∀ w ∈ W,∀ x,R.Adj w x ↔ T.Adj w x) ∧
      R.induce ((W : Set V)ᶜ) = H.induce ((W : Set V)ᶜ) ∧
      let A := W.filter (fun w => 0 < T.degree w)
      T.IsIndepSet (A : Set V) ∧
      (∀ w ∈ A,0 < T.degree w) ∧
      ∀ w ∈ A,∀ x,T.Adj w x → neighboursIn T A x < T.degree w := by
  obtain ⟨T,hRun,hLe,hStrict⟩ := exists_auxiliary_low_preprocessing G W
  obtain ⟨R,hReplay,hRLe,hMax,hUncol,hSync,hInduce⟩ :=
    replay_auxiliary_low_preprocessing hRun H hSame hSmall hNC
  refine ⟨T,R,hRun,hReplay,hLe,hRLe,hMax,hUncol,hSync,hInduce,?_⟩
  dsimp only
  let A := W.filter (fun w => 0 < T.degree w)
  have hAW : A ⊆ W := filter_subset _ _
  refine ⟨?_,fun w hw => (mem_filter.mp hw).2,?_⟩
  · intro u hu v hv huv hAdj
    exact hInd (hAW hu) (hAW hv) huv (hLe hAdj)
  · intro w hw x hAdj
    exact (neighboursIn_mono T hAW x).trans_lt (hStrict w (hAW hw) x hAdj)

end OverfullWork.CMSTrimmingRound
