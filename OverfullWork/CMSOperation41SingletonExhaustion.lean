module

public import OverfullWork.CMSOperation41EmptyActiveChoice
public import OverfullWork.CMSOperation41ExactRecords
public import OverfullWork.CMSOperation41ActiveBands
public import OverfullWork.WeakVALSingleEdgeDeletion

@[expose] public section


/-! If the inherited singleton reaches degree one, Algorithm 1 removes
its last edge without using a trimming layer. The support then loses
just this vertex, as also happens when a layer uses its last two edges. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing RobustExpansion
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge SimpleGraph.instDecidableMapAdj
attribute [-instance] SimpleGraph.instDecidableRelAdjDeleteEdgesOfDecidablePredSym2MemSetOfDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Once an internal charge is allowed, each such round spends an edge
of the same singleton. The capped degree pays for all these rounds. -/
theorem singleton_internal_charge_count_le (degree : ℕ → ℕ) (charged : ℕ → Prop)
    (m cap : ℕ) (hMono : ∀ i < m,degree (i+1) ≤ degree i)
    (hCharge : ∀ i < m,charged i → degree i ≤ cap ∧ degree (i+1)+1 ≤ degree i) :
    ((range m).filter charged).card ≤ cap := by
  have hTotal (j : ℕ) (hj : j ≤ m) :
      min cap (degree j)+((range j).filter charged).card ≤ cap := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j < m := by omega
      have hBefore := ih hj'.le
      rw [card_filter,sum_range_succ,←card_filter]
      by_cases h : charged j
      · obtain ⟨hSmall,hDrop⟩ := hCharge j hj' h
        have hNext : degree (j+1) ≤ cap := by omega
        have hStep : min cap (degree (j+1))+1 ≤ min cap (degree j) := by
          rw [min_eq_right hSmall,min_eq_right hNext]
          exact hDrop
        rw [if_pos h,←add_assoc,add_right_comm]
        exact (Nat.add_le_add_right hStep _).trans hBefore
      · simp only [if_neg h,add_zero]
        exact (Nat.add_le_add_right (min_le_min_left cap (hMono j hj')) _).trans hBefore
  have h := hTotal m le_rfl
  omega

/-- Before the first prefix where the singleton has degree at most one,
only the prescribed layers have spent its degree. -/
theorem inherited_singleton_prefix_before_exhaustion (S T P : ℕ → SimpleGraph V) (m : ℕ) (w : V)
    (hClean : ∀ i < m,DeletionRun {w} (S i) (T i))
    (hPrescribed : ∀ i < m,P i ≤ T i)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i)) :
    ∃ j ≤ m,(j = m ∨ (S j).degree w ≤ 1) ∧
      (∀ i < j,T i = S i ∧ 2 ≤ (S i).degree w) ∧
      ∀ i ≤ j,(S i).degree w+(∑ k ∈ range i,(P k).degree w) = (S 0).degree w := by
  have hPick : ∃ j ≤ m,(j = m ∨ (S j).degree w ≤ 1) := ⟨m,le_rfl,Or.inl rfl⟩
  let j := Nat.find hPick
  obtain ⟨hj,hexit⟩ := Nat.find_spec hPick
  have hHigh (i : ℕ) (hi : i < j) : 2 ≤ (S i).degree w := by
    by_contra! h
    have he : (S i).degree w ≤ 1 := by omega
    exact Nat.find_min hPick hi ⟨hi.le.trans hj,Or.inr he⟩
  obtain ⟨hBalance,hNoClean⟩ := inherited_active_prefix_degree_balance {w} S T P j
    (fun i hi => hClean i (hi.trans_le hj)) (fun i hi => hPrescribed i (hi.trans_le hj))
    (fun i hi => hNext i (hi.trans_le hj)) (by
      intro i hi v hv
      apply Or.inl
      rw [mem_singleton.mp hv,card_singleton]
      exact hHigh i hi)
  exact ⟨j,hj,hexit,fun i hi => ⟨hNoClean i hi,hHigh i hi⟩,
    fun i hi => hBalance i hi w (mem_singleton_self _)⟩

theorem support_after_exhausting_singleton (degree next : V → ℕ) (w : V)
    (hPos : 0 < degree w) (hZero : next w = 0)
    (hSupport : ∀ v,v ≠ w → (0 < next v ↔ 0 < degree v)) :
    let S := univ.filter (fun v => 0 < degree v)
    let T := univ.filter (fun v => 0 < next v)
    T = S.erase w ∧ (Odd S.card → Even T.card) := by
  intro S T
  have hEq : T = S.erase w := by
    ext v
    simp only [T,S,mem_filter,mem_univ,true_and,mem_erase]
    by_cases h : v = w
    · subst v
      simp [hZero]
    · exact (hSupport v h).trans (and_iff_right h).symm
  refine ⟨hEq,?_⟩
  intro hOdd
  have hMem : w ∈ S := mem_filter.mpr ⟨mem_univ _,hPos⟩
  have hCard := card_erase_add_one hMem
  obtain ⟨k,hk⟩ := hOdd
  exact ⟨k,by rw [hEq]; omega⟩

set_option maxHeartbeats 2700000 in
theorem cleanup_exhausted_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (w : V)
    (hOne : G.degree w = 1) (hNC : ¬G.EdgeColorable G.maxDegree) (hNo : ¬G.HasOverfullSubgraph)
    (hOther : ∀ x,G.Adj w x → 2 ≤ G.degree x) :
    ∃ (x : V) (H : SimpleGraph V),G.Adj w x ∧ H = G.deleteEdges {s(w,x)} ∧
      DeletionRun {w} G H ∧ H ≤ G ∧ H.maxDegree = G.maxDegree ∧
      ¬H.EdgeColorable H.maxDegree ∧ ¬H.HasOverfullSubgraph ∧
      (∀ v,H.degree v+(if v=w ∨ v=x then 1 else 0) = G.degree v) ∧
      (univ.filter (fun v => 0 < H.degree v)) = (univ.filter (fun v => 0 < G.degree v)).erase w ∧
      (∀ r t,IsRobustAt G r t → IsRobustAt H (r-1) t) ∧
      (∀ b : ℕ,(∀ u v,G.Adj u v → G.maxDegree ≤ G.degree u+G.degree v+b) →
        ∀ u v,H.Adj u v → H.maxDegree ≤ H.degree u+H.degree v+(b+1)) := by
  obtain ⟨x,hEdge,_⟩ := (degree_eq_one_iff_existsUnique_adj (G := G)).mp hOne
  let H := G.deleteEdges {s(w,x)}
  have hx := G.degree_le_maxDegree x
  have hBad : G.degree w+G.degree x ≤ G.maxDegree+1 := by omega
  obtain ⟨hMax,hUncol,hNoH⟩ := WeakVALSingleEdgeDeletion.preserved_obstruction G w x hBad hNC hNo
  have hNeighbours : PrunedCore.neighboursIn G {w} x = 1 := by
    rw [RobustExpansion.neighboursIn_eq_filter_card,filter_singleton,if_pos hEdge.symm,card_singleton]
  have hClean : DeletionRun {w} G H :=
    DeletionRun.step (DeletionRun.refl G) (mem_singleton_self _) hEdge (by rw [hOne,hNeighbours])
  have hDegree (v : V) : H.degree v+(if v=w ∨ v=x then 1 else 0) = G.degree v :=
    WeakVALSingleEdgeDeletion.degree_delete_add G hEdge v
  have hZero : H.degree w = 0 := by
    have h := hDegree w
    rw [if_pos (Or.inl rfl),hOne] at h
    omega
  have hSupp (v : V) (hv : v ≠ w) : 0 < H.degree v ↔ 0 < G.degree v := by
    by_cases hvx : v = x
    · subst v
      have h := hDegree x
      have hx₂ := hOther x hEdge
      simp only [or_true,if_true] at h
      omega
    · have h := hDegree v
      simp only [hv,hvx,or_self,if_false,add_zero] at h
      rw [h]
  have hSuppEq := (support_after_exhausting_singleton (fun v => G.degree v) (fun v => H.degree v)
    w (by omega) hZero hSupp).1
  have hHEq : H = sdiff G (edge w x) := by
    ext a b
    simp only [H,deleteEdges_adj,sdiff_adj,edge_adj,Set.mem_singleton_iff,Sym2.eq_iff]
    have hh : G.Adj a b → a ≠ b := fun h => h.ne
    tauto
  refine ⟨x,H,hEdge,rfl,hClean,deleteEdges_le _,hMax,hUncol,hNoH,hDegree,hSuppEq,?_,?_⟩
  · intro r t hR
    rw [hHEq]
    have hR' := RobustExpansion.isRobustAt_sdiff G (edge w x) r 1 t hR (fun v => by
      rw [DegreeTwoRealization.degree_edge_exact w x v hEdge.ne]
      split_ifs <;> omega)
    have hDec : SimpleGraph.Sdiff.adjDecidable V G (edge w x) =
        (fun a b => Classical.propDecidable ((sdiff G (edge w x)).Adj a b)) := Subsingleton.elim _ _
    rwa [hDec] at hR'
  · intro b hWeak u v hAdj
    have hu : u ≠ w := by
      rintro rfl
      have h := (H.degree_pos_iff_exists_adj _).mpr ⟨v,hAdj⟩
      omega
    have hv : v ≠ w := by
      rintro rfl
      have h := (H.degree_pos_iff_exists_adj _).mpr ⟨u,hAdj.symm⟩
      omega
    have hSum := hWeak u v (deleteEdges_le _ hAdj)
    have huD := hDegree u
    have hvD := hDegree v
    simp only [hu,hv,false_or] at huD hvD
    rw [hMax]
    by_cases h : u = x
    · have h' : v ≠ x := fun he => hAdj.ne (h.trans he.symm)
      simp only [if_pos h,if_neg h',add_zero] at huD hvD
      omega
    · simp only [if_neg h,add_zero] at huD
      split_ifs at hvD <;> omega

omit [Fintype V] in
/-- A second critical choice after the odd support loses its singleton
selects a pair, provided there is still no stopping record. -/
theorem critical_pair_after_odd_support_loses_singleton (S U : Finset V) (w : V)
    (hw : w ∈ U) (hU : U ⊆ S) (hOdd : Odd S.card)
    (degree : V → ℕ) (d budget : ℕ) (hBudget : 1 ≤ budget) :
    let T := S.erase w
    let U' := U.erase w
    Odd (T \ U').card →
    (∀ v ∈ T,degree v ≤ d) →
    (∑ v ∈ T \ U',(d-degree v)) ≤ 1 →
    ¬HasAlmostOverfullRecord T d budget degree →
    ∃ a ∈ U',∃ b ∈ U',a ≠ b ∧ (∀ v ∈ U',degree a ≤ degree v) ∧
      ∀ v ∈ U',v ≠ a → degree b ≤ degree v := by
  intro T U' hOddOrd hBound hMass hNo
  have hEven : Even T.card := by
    have hCard := card_erase_add_one (hU hw)
    obtain ⟨k,hk⟩ := hOdd
    exact ⟨k,by change T.card+1 = S.card at hCard; omega⟩
  have hU' : U' ⊆ T := fun v hv => mem_erase.mpr ⟨(mem_erase.mp hv).1,hU (mem_erase.mp hv).2⟩
  obtain ⟨W,hW,hParity,hMin⟩ :=
    exists_critical_active_vertices T U' hU' d budget degree hBudget hBound hOddOrd hMass hNo
  have hSize := hParity.mp hEven
  rcases hMin with ⟨_,a,_,rfl,_⟩ | ⟨_,a,ha,b,hb,hne,_,hLeft,hRight⟩
  · simp at hSize
  · exact ⟨a,ha,b,hb,hne,hLeft,hRight⟩

end OverfullWork.CMSTrimmingRound
