module

public import OverfullWork.CMSOperation41DenseRecords
public import OverfullWork.CMSOperation41PackedHistory

@[expose] public section


/-! Operation 4.1 uses a common clock across the original and inherited
phases. The packing data of a round is recorded on the graph after its
cleanup, while the stopping test also applies before that cleanup. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

structure TrimmingPackingStep (initial : Finset V) (S T : VirtualTrimmingState V)
    (d test j cap : ℕ) where
  cleanupSet : Finset V
  cleaned : SimpleGraph V
  cleanup_subset : cleanupSet ⊆ initial
  cleanup_independent : S.graph.IsIndepSet (cleanupSet : Set V)
  cleanup : DeletionRun cleanupSet S.graph cleaned
  cleanup_below_target : ∀ w ∈ cleanupSet,S.graph.degree w < d
  no_almost : ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 < S.record initial j v))
    d test (S.record initial j)
  current : Finset V
  active : Finset V
  floor : ℕ
  selectionUsage : ℕ → Finset V
  selection : TrimmingStepSelection cleaned initial current active
    (auxiliaryPhysicalDegree cleaned initial S.prescribed S.credit j) d floor selectionUsage j cap
  free : Finset V
  endpoint_payment : ∀ i,let v := (selection.round.words.endpoint i).val
    v ∈ free ∨ (∃ w ∈ active,selection.round.words.prescribedGraph.Adj w v) ∨
      0 < selection.round.words.degreeCredit selection.round.omitted v
  next : T = (⟨cleaned,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).advance j
    selection.round.words.prescribedGraph (selection.round.words.degreeCredit selection.round.omitted) free

structure TrimmingPackingSegment (initial : Finset V) (D test cap j m : ℕ)
    (start finish : VirtualTrimmingState V) where
  states : ℕ → VirtualTrimmingState V
  starts : states 0 = start
  finishes : states m = finish
  steps : (i : Fin m) →
    TrimmingPackingStep initial (states i) (states (i.val+1)) (D-2*i.val) test (j+i.val) cap

theorem HasTrimmingRoundWithoutCleanup.to_packing_step_after_cleanup
    {S T : VirtualTrimmingState V} {initial current active support : Finset V}
    {G : SimpleGraph V} {W : Finset V} {d floor test j cap : ℕ}
    (h : HasTrimmingRoundWithoutCleanup S T initial current active support d floor test j cap)
    (hW : W ⊆ initial) (hInd : G.IsIndepSet (W : Set V)) (hClean : DeletionRun W G S.graph)
    (hSmall : ∀ w ∈ W,G.degree w < d)
    (hNo : ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 <
      (⟨G,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).record initial j v))
      d test ((⟨G,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).record initial j)) :
    ∃ R : TrimmingPackingStep initial ⟨G,S.prescribed,S.credit,S.used⟩ T d test j cap,
      R.cleaned = S.graph := by
  rcases h with ⟨_,F,hF⟩
  refine ⟨{
    cleanupSet := W
    cleaned := S.graph
    cleanup_subset := hW
    cleanup_independent := hInd
    cleanup := hClean
    cleanup_below_target := hSmall
    no_almost := hNo
    current := current
    active := active
    floor := floor
    selectionUsage := S.used
    selection := F
    free := F.freeEndpoints
    endpoint_payment := ?_
    next := hF },rfl⟩
  intro i
  rcases F.endpoint_payment i with hFree | hOther
  · exact Or.inl (mem_filter.mpr ⟨mem_image.mpr ⟨i,mem_univ _,rfl⟩,hFree⟩)
  · exact Or.inr hOther

theorem HasTrimmingRoundWithoutCleanup.to_packing_step
    {S T : VirtualTrimmingState V} {initial current active support : Finset V}
    {d floor test j cap : ℕ}
    (h : HasTrimmingRoundWithoutCleanup S T initial current active support d floor test j cap)
    (hSupport : univ.filter (fun v => 0 < S.record initial j v) = support) :
    ∃ R : TrimmingPackingStep initial S T d test j cap, R.cleaned = S.graph :=
  h.to_packing_step_after_cleanup (empty_subset _) (by simp) (DeletionRun.refl S.graph)
    (by simp)
    (by change ¬HasAlmostOverfullRecord _ d test (S.record initial j); rw [hSupport]; exact h.1)

/-- Supply the real cleanup at the first round that follows a boundary. -/
def TrimmingPackingStep.withCleanup
    {initial W : Finset V} {S T : VirtualTrimmingState V} {G : SimpleGraph V}
    {d test j cap : ℕ} (R : TrimmingPackingStep initial S T d test j cap)
    (hSame : R.cleaned = S.graph) (hW : W ⊆ initial) (hInd : G.IsIndepSet (W : Set V))
    (hClean : DeletionRun W G S.graph)
    (hSmall : ∀ w ∈ W,G.degree w < d)
    (hNo : ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 <
      (⟨G,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).record initial j v))
      d test ((⟨G,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).record initial j)) :
    TrimmingPackingStep initial ⟨G,S.prescribed,S.credit,S.used⟩ T d test j cap where
  cleanupSet := W
  cleaned := R.cleaned
  cleanup_subset := hW
  cleanup_independent := hInd
  cleanup := hSame.symm ▸ hClean
  cleanup_below_target := hSmall
  no_almost := hNo
  current := R.current
  active := R.active
  floor := R.floor
  selectionUsage := R.selectionUsage
  selection := R.selection
  free := R.free
  endpoint_payment := R.endpoint_payment
  next := R.next

/-- Append segments with the same boundary state. Every row keeps its
prescription and its absolute projection index. -/
def TrimmingPackingSegment.append
    {initial : Finset V} {D test cap j m n : ℕ} {S T R : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap j m S T)
    (K : TrimmingPackingSegment initial (D-2*m) test cap (j+m) n T R) :
    TrimmingPackingSegment initial D test cap j (m+n) S R := by
  let states (i : ℕ) := if i < m then H.states i else K.states (i-m)
  have hLeft (i : ℕ) (hi : i ≤ m) : states i = H.states i := by
    by_cases h : i < m
    · simp only [states,if_pos h]
    · have he : i = m := le_antisymm hi (Nat.le_of_not_gt h)
      subst i
      simp only [states,lt_irrefl,if_false,Nat.sub_self,K.starts,H.finishes]
  have hRight (i : ℕ) (hi : m ≤ i) : states i = K.states (i-m) := if_neg (Nat.not_lt.mpr hi)
  refine ⟨states,(hLeft 0 (Nat.zero_le _)).trans H.starts,?_,?_⟩
  · rw [hRight _ (Nat.le_add_right _ _),Nat.add_sub_cancel_left,K.finishes]
  intro i
  by_cases hi : i.val < m
  · rw [hLeft _ hi.le,hLeft _ (Nat.succ_le_of_lt hi)]
    exact H.steps ⟨i,hi⟩
  · have hm : m ≤ i.val := Nat.le_of_not_gt hi
    have hkn : i.val-m < n := Nat.sub_lt_left_of_lt_add hm i.isLt
    have hIdx : m+(i.val-m) = i.val := Nat.add_sub_of_le hm
    have hNext : i.val+1-m = i.val-m+1 := by omega
    rw [hRight _ hm,hRight _ (hm.trans (Nat.le_succ _)),hNext]
    have hD : D-2*m-2*(i.val-m) = D-2*i.val := by
      rw [Nat.sub_sub,←Nat.mul_add,hIdx]
    have hj : j+m+(i.val-m) = j+i.val := by rw [Nat.add_assoc,hIdx]
    simpa only [hD,hj] using K.steps ⟨i.val-m,hkn⟩

/-- The degree-sum estimate with the same budget at every saved prefix
of a segment, measured in its absolute round indices. -/
def TrimmingPackingSegment.HasWeakDegreeSums
    {initial : Finset V} {D test cap j m : ℕ} {S T : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap j m S T) (budget : ℕ) : Prop :=
  ∀ i ≤ m,(H.states i).HasWeakDegreeSum initial (j+i) (D-2*i) budget

theorem TrimmingPackingSegment.HasWeakDegreeSums.mono
    {initial : Finset V} {D test cap j m budget bound : ℕ} {S T : VirtualTrimmingState V}
    {H : TrimmingPackingSegment initial D test cap j m S T}
    (h : H.HasWeakDegreeSums budget) (hle : budget ≤ bound) :
    H.HasWeakDegreeSums bound := fun i hi => (h i hi).mono hle

theorem TrimmingPackingSegment.HasWeakDegreeSums.append
    {initial : Finset V} {D test cap j m n budget : ℕ} {S T F : VirtualTrimmingState V}
    {H : TrimmingPackingSegment initial D test cap j m S T}
    {K : TrimmingPackingSegment initial (D-2*m) test cap (j+m) n T F}
    (hH : H.HasWeakDegreeSums budget) (hK : K.HasWeakDegreeSums budget) :
    (H.append K).HasWeakDegreeSums budget := by
  intro i hi
  change (if i < m then H.states i else K.states (i-m)).HasWeakDegreeSum initial (j+i) (D-2*i) budget
  by_cases hm : i < m
  · rw [if_pos hm]
    exact hH i hm.le
  have hLe := Nat.le_of_not_gt hm
  have hIndex : m+(i-m) = i := Nat.add_sub_of_le hLe
  have hTarget : D-2*m-2*(i-m) = D-2*i := by rw [Nat.sub_sub,←Nat.mul_add,hIndex]
  have hClock : j+m+(i-m) = j+i := by rw [Nat.add_assoc,hIndex]
  rw [if_neg hm]
  simpa only [hTarget,hClock] using hK (i-m) (by omega)

theorem TrimmingPackingSegment.HasWeakDegreeSums.of_unchanged_suffix
    {initial : Finset V} {D test cap j m budget : ℕ} {S S' T : VirtualTrimmingState V}
    {H : TrimmingPackingSegment initial D test cap j m S T}
    {K : TrimmingPackingSegment initial D test cap j m S' T}
    (h : H.HasWeakDegreeSums budget) (hStart : S'.HasWeakDegreeSum initial j D budget)
    (hStates : ∀ i ≤ m,i ≠ 0 → K.states i = H.states i) :
    K.HasWeakDegreeSums budget := by
  intro i hi
  by_cases hZero : i = 0
  · subst i
    simpa only [K.starts,Nat.mul_zero,Nat.sub_zero,Nat.add_zero] using hStart
  · rw [hStates i hi hZero]
    exact h i hi

/-- A boundary cleanup belongs to the next round when that round
exists. It leaves the absolute round index and the saved arrays intact. -/
def TrimmingPackingSegment.prependCleanup
    {initial W : Finset V} {D test cap j m : ℕ} {S T : VirtualTrimmingState V}
    {G : SimpleGraph V} (H : TrimmingPackingSegment initial D test cap j m S T)
    (hm : 0 < m) (hFirst : (H.steps ⟨0,hm⟩).cleaned = S.graph)
    (hW : W ⊆ initial) (hInd : G.IsIndepSet (W : Set V))
    (hClean : DeletionRun W G S.graph)
    (hSmall : ∀ w ∈ W,G.degree w < D)
    (hNo : ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 <
      (⟨G,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).record initial j v))
      D test ((⟨G,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).record initial j)) :
    TrimmingPackingSegment initial D test cap j m ⟨G,S.prescribed,S.credit,S.used⟩ T := by
  let start : VirtualTrimmingState V := ⟨G,S.prescribed,S.credit,S.used⟩
  let states := Function.update H.states 0 start
  have hOld (i : ℕ) (hi : i ≠ 0) : states i = H.states i := Function.update_of_ne hi _ _
  refine ⟨states,Function.update_self _ _ _,(hOld m hm.ne').trans H.finishes,?_⟩
  intro i
  rw [hOld _ (Nat.succ_ne_zero _)]
  by_cases h : i.val = 0
  · have hi : i = ⟨0,hm⟩ := Fin.ext h
    subst i
    let hStep := H.steps ⟨0,hm⟩
    have hSource : H.states 0 = S := H.starts
    have hSame : hStep.cleaned = (H.states 0).graph := hFirst.trans (congrArg VirtualTrimmingState.graph hSource).symm
    have hRun : DeletionRun W G (H.states 0).graph := congrArg VirtualTrimmingState.graph hSource ▸ hClean
    have hS : (⟨G,(H.states 0).prescribed,(H.states 0).credit,(H.states 0).used⟩ :
        VirtualTrimmingState V) = start := by rw [hSource]
    rw [show states 0 = start from Function.update_self _ _ _]
    have hNo' : ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 <
        (⟨G,(H.states 0).prescribed,(H.states 0).credit,(H.states 0).used⟩ :
          VirtualTrimmingState V).record initial (j+0) v))
        (D-2*0) test ((⟨G,(H.states 0).prescribed,(H.states 0).credit,(H.states 0).used⟩ :
          VirtualTrimmingState V).record initial (j+0)) := by
      rw [hS]
      simpa only [Nat.mul_zero,Nat.sub_zero,Nat.add_zero] using hNo
    exact hS ▸ hStep.withCleanup hSame hW hInd hRun hSmall hNo'
  · rw [hOld _ h]
    exact H.steps i

theorem OriginalTrimmingHistory.to_packing_segment
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial low : Finset V}
    {threshold floor cap test m : ℕ}
    (H : OriginalTrimmingHistory G initial low threshold floor cap test m)
    (hLow : low ⊆ initial) (hInd : G.IsIndepSet (low : Set V))
    (hSmall : ∀ w ∈ low,G.degree w < G.maxDegree-2*m) :
    ∃ K : TrimmingPackingSegment initial G.maxDegree test cap 0 m
      ⟨G,H.prescribed,H.credit,H.free⟩ ⟨H.graph m,H.prescribed,H.credit,H.free⟩,
      K.states = fun i => ⟨H.graph i,H.prescribed,H.credit,H.free⟩ := by
  let states (i : ℕ) : VirtualTrimmingState V := ⟨H.graph i,H.prescribed,H.credit,H.free⟩
  have hSource (i : ℕ) (hi : i ≤ m) : H.graph i ≤ G :=
    (virtual_trimming_prefix_le H.graph H.cleaned H.prescribed m
      (fun k hk => DeletionRun.le_source (H.cleanup k hk)) H.graph_next 0 i (Nat.zero_le _) hi).trans
      H.graph_zero.le
  have hStep (i : Fin m) : Nonempty (TrimmingPackingStep initial (states i) (states (i.val+1))
      (G.maxDegree-2*i.val) test (0+i.val) cap) := by
    have hEq : (fun v => H.degree i v-(sdiff (H.graph i) (H.cleaned i)).degree v) =
        auxiliaryPhysicalDegree (H.cleaned i) initial H.prescribed H.credit i := by
      funext v
      rw [H.degree_exact i i.isLt.le,auxiliary_physical_degree_after_cleanup (H.graph i) (H.cleaned i)
        initial H.prescribed H.credit i (DeletionRun.le_source (H.cleanup i i.isLt))]
    let Selected (degree : V → ℕ) := ∃ used : ℕ → Finset V,
      ∃ F : TrimmingStepSelection (H.cleaned i) initial
          (H.exceptional i ∩ univ.filter (fun v => 0 < degree v))
          (originalCleanActive low (H.exceptional i) (H.cleaned i)) degree
          (G.maxDegree-2*i.val) floor used i.val cap,
        H.prescribed i = F.round.words.prescribedGraph ∧
        H.credit i = F.round.words.degreeCredit F.round.omitted ∧
        H.special i = F.special ∧ H.internal i = F.internalCharge ∧
        ∀ e,let v := (F.round.words.endpoint e).val
          v ∈ H.free i ∨ (∃ w ∈ originalCleanActive low (H.exceptional i) (H.cleaned i),
            (H.prescribed i).Adj w v) ∨ 0 < H.credit i v
    have hSelected : Selected (fun v => H.degree i v-(sdiff (H.graph i) (H.cleaned i)).degree v) :=
      H.selection i i.isLt
    rw [hEq] at hSelected
    obtain ⟨used,F,hP,hCredit,_,_,hPay⟩ := hSelected
    let W := H.exceptional i ∩ low
    have hIndependent : (H.graph i).IsIndepSet (W : Set V) := by
      intro a ha b hb hne hab
      exact hInd (mem_inter.mp ha).2 (mem_inter.mp hb).2 hne (hSource i i.isLt.le hab)
    rw [Nat.zero_add]
    refine ⟨{
      cleanupSet := W
      cleaned := H.cleaned i
      cleanup_subset := inter_subset_right.trans hLow
      cleanup_independent := hIndependent
      cleanup := H.cleanup i i.isLt
      cleanup_below_target := fun w hw =>
        ((degree_le_of_le (hSource i i.isLt.le) (v := w)).trans_lt
          (hSmall w (mem_inter.mp hw).2)).trans_le
          (Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 i.isLt.le) _)
      no_almost := ?_
      current := _
      active := _
      floor := floor
      selectionUsage := used
      selection := F
      free := H.free i
      endpoint_payment := ?_
      next := ?_ }⟩
    · simpa only [states,VirtualTrimmingState.record,←H.degree_exact i i.isLt.le] using H.no_stop i i.isLt
    · simpa only [←hP,←hCredit] using hPay
    · dsimp only [states,VirtualTrimmingState.advance]
      rw [←hP,←hCredit,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self,
        H.graph_next i i.isLt]
  exact ⟨⟨states,by simp only [states,H.graph_zero],rfl,fun i => (hStep i).some⟩,rfl⟩

theorem InheritedPairHistory.to_packing_segment
    {start : VirtualTrimmingState V} {initial current active support : Finset V}
    {D floor loss threshold test j cap total m : ℕ}
    (H : InheritedPairHistory start initial current active support D floor loss threshold test j cap total m) :
    ∃ K : TrimmingPackingSegment initial D test cap j m start (H.states m),
      K.states = H.states ∧ ∀ i : Fin m,(K.steps i).cleaned = (K.states i).graph := by
  have hRow (i : Fin m) : ∃ R : TrimmingPackingStep initial (H.states i) (H.states (i.val+1))
      (D-2*i.val) test (j+i.val) cap,R.cleaned = (H.states i).graph :=
    (H.rounds i i.isLt).to_packing_step (H.positions i i.isLt.le).support_eq
  exact ⟨⟨H.states,H.starts,rfl,fun i => (hRow i).choose⟩,rfl,fun i => (hRow i).choose_spec⟩

theorem InheritedSingletonHistory.to_packing_segment
    {start : VirtualTrimmingState V} {initial current support : Finset V} {w : V}
    {D floor loss threshold test j cap m : ℕ}
    (H : InheritedSingletonHistory start initial current support w D floor loss threshold test j cap m)
    (hInitial : w ∈ initial) (hSupport : w ∈ support) :
    ∃ K : TrimmingPackingSegment initial D test cap j m start (H.states m),
      K.states = H.states ∧ ∀ i : Fin m,(K.steps i).cleaned = (K.states i).graph := by
  have hRow (i : Fin m) : ∃ R : TrimmingPackingStep initial (H.states i) (H.states (i.val+1))
      (D-2*i.val) test (j+i.val) cap,R.cleaned = (H.states i).graph := by
    apply (H.rounds i i.isLt).to_packing_step
    have hLive : 0 < (H.states i).graph.degree w :=
      (Nat.succ_pos _).trans_le (H.active_drop i i.isLt)
    ext v
    by_cases h : v = w
    · subst v
      refine iff_of_true (mem_filter.mpr ⟨mem_univ _,?_⟩) hSupport
      simpa only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hInitial] using hLive
    · have hErase := Finset.ext_iff.mp (H.positions i i.isLt.le).support_except v
      exact ⟨fun hv => (mem_erase.mp (hErase.mp (mem_erase.mpr ⟨h,hv⟩))).2,
        fun hv => (mem_erase.mp (hErase.mpr (mem_erase.mpr ⟨h,hv⟩))).2⟩
  exact ⟨⟨H.states,H.starts,rfl,fun i => (hRow i).choose⟩,rfl,fun i => (hRow i).choose_spec⟩

/-- A later update leaves each earlier prescription, credit and
projection reservation unchanged. Read all three from the last state. -/
theorem TrimmingPackingSegment.final_arrays
    {initial : Finset V} {D test cap j m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap j m start finish) (i : Fin m) :
    finish.prescribed (j+i.val) = (H.steps i).selection.round.words.prescribedGraph ∧
    finish.credit (j+i.val) = (H.steps i).selection.round.words.degreeCredit
      (H.steps i).selection.round.omitted ∧
    finish.used (j+i.val) = (H.steps i).free := by
  let R := H.steps i
  let P := R.selection.round.words.prescribedGraph
  let c := R.selection.round.words.degreeCredit R.selection.round.omitted
  have hAt (k : ℕ) (hk : k ≤ m) (hi : i.val < k) :
      (H.states k).prescribed (j+i.val) = P ∧
      (H.states k).credit (j+i.val) = c ∧ (H.states k).used (j+i.val) = R.free := by
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases he : i.val = k
      · have hIdx : i = ⟨k,Nat.lt_of_succ_le hk⟩ := Fin.ext he
        subst i
        refine ⟨?_,?_,?_⟩
        · simpa only [VirtualTrimmingState.advance,Function.update_self,P] using
            congrArg (fun s => s.prescribed (j+k)) R.next
        · simpa only [VirtualTrimmingState.advance,Function.update_self,c] using
            congrArg (fun s => s.credit (j+k)) R.next
        · simpa only [VirtualTrimmingState.advance,Function.update_self] using
            congrArg (fun s => s.used (j+k)) R.next
      · have hPrev := ih (Nat.le_of_succ_le hk) (by omega)
        have hNe : j+i.val ≠ j+k := by omega
        rw [(H.steps ⟨k,Nat.lt_of_succ_le hk⟩).next]
        simpa only [VirtualTrimmingState.advance,Function.update_of_ne hNe] using hPrev
  have h := hAt m le_rfl i.isLt
  rw [H.finishes] at h
  exact h

/-- Two states of the same history agree on the entries already set
at the earlier state. -/
theorem TrimmingPackingSegment.record_eq_final
    {initial : Finset V} {D test cap j m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap j m start finish)
    (a k : ℕ) (ha : a ≤ k) (hk : k ≤ m) (i : ℕ) (hi : i < j+a) :
    (H.states k).prescribed i = (H.states a).prescribed i ∧
    (H.states k).credit i = (H.states a).credit i ∧
    (H.states k).used i = (H.states a).used i := by
  induction k with
  | zero =>
    have he : a = 0 := Nat.eq_zero_of_le_zero ha
    subst a
    exact ⟨rfl,rfl,rfl⟩
  | succ k ih =>
    by_cases he : a = k+1
    · subst a
      exact ⟨rfl,rfl,rfl⟩
    · have hPrev : a ≤ k := by omega
      have hNe : i ≠ j+k := by omega
      rw [(H.steps ⟨k,Nat.lt_of_succ_le hk⟩).next]
      simpa only [VirtualTrimmingState.advance,Function.update_of_ne hNe]
        using ih hPrev (Nat.le_of_succ_le hk)

def TrimmingPackingSegment.cleanedGraph
    {initial : Finset V} {D test cap j m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap j m start finish) (i : ℕ) : SimpleGraph V :=
  if hi : i < m then (H.steps ⟨i,hi⟩).cleaned else (H.states i).graph

def TrimmingPackingSegment.cleanupSet
    {initial : Finset V} {D test cap j m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap j m start finish) (i : ℕ) : Finset V :=
  if hi : i < m then (H.steps ⟨i,hi⟩).cleanupSet else ∅

theorem TrimmingPackingSegment.cleanup_below_target
    {initial : Finset V} {D test cap j m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap j m start finish) :
    ∀ i < m,∀ w ∈ H.cleanupSet i,(H.states i).graph.degree w < D-2*i := by
  intro i hi w hw
  rw [TrimmingPackingSegment.cleanupSet,dif_pos hi] at hw
  exact (H.steps ⟨i,hi⟩).cleanup_below_target w hw

def TrimmingPackingSegment.layoutSize
    {initial : Finset V} {D test cap j m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap j m start finish) (i : Fin m) : ℕ :=
  (H.steps i).selection.round.size

def TrimmingPackingSegment.layoutWords
    {initial : Finset V} {D test cap j m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap j m start finish) (i : Fin m) :
    TrimmingReplacementWords (H.cleanedGraph i.val) initial (Fin (H.layoutSize i)) :=
  cast (congrArg (fun Q => TrimmingReplacementWords Q initial (Fin (H.layoutSize i)))
    (dif_pos i.isLt).symm) (H.steps i).selection.round.words

def TrimmingPackingSegment.layoutOmitted
    {initial : Finset V} {D test cap j m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap j m start finish) (i : Fin m) :
    Finset ↥(initialᶜ : Finset V) :=
  (H.steps i).selection.round.omitted

private theorem replacement_words_cast_fields
    {G T : SimpleGraph V} {U : Finset V} {I : Type*} [Fintype I]
    (h : G = T) (w : TrimmingReplacementWords G U I) (omitted : Finset ↥(Uᶜ : Finset V)) :
    let x := cast (congrArg (fun Q => TrimmingReplacementWords Q U I) h) w
    x.endpoint = w.endpoint ∧ x.body = w.body ∧ x.gaps = w.gaps ∧
      x.coreIncidentGaps = w.coreIncidentGaps ∧
      x.prescribedGraph = w.prescribedGraph ∧ x.degreeCredit omitted = w.degreeCredit omitted := by
  subst T
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- All structural inputs to the simultaneous packing come from
the history, with its final arrays agreeing with the layout data. -/
theorem TrimmingPackingSegment.packing_inputs
    {G : SimpleGraph V} [dG : DecidableRel G.Adj] {initial : Finset V} {test cap m : ℕ}
    {start finish : VirtualTrimmingState V} (hG : start.graph = G)
    (H : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish) :
    let S (i : ℕ) := (H.states i).graph
    let T := H.cleanedGraph
    let W := H.cleanupSet
    let f := H.layoutSize
    let words := H.layoutWords
    let omitted := H.layoutOmitted
    let P := prescribedTrimmingHistory initial T f words
    let credit := trimmingCreditHistory initial T f words omitted
    S 0 = G ∧ (∀ i < m,W i ⊆ initial) ∧ (∀ i < m,DeletionRun (W i) (S i) (T i)) ∧
      (∀ i < m,S (i+1) = sdiff (T i) (P i)) ∧
      (∀ i < m,(S i).IsIndepSet (W i : Set V)) ∧
      (∀ (i : Fin m) k, (words i).body k = [] →
        s(((words i).endpoint (k,false)).val,((words i).endpoint (k,true)).val) ∈ (words i).gaps) ∧
      (∀ i : Fin m,
        let len := initialᶜ.card-(omitted i).card+∑ k,((words i).body k).length
        3 ≤ len ∧ (Even len ∨ (words i).gaps.Nonempty)) ∧
      (∀ i : Fin m,(omitted i).card+(words i).coreIncidentGaps.card ≤ 1) ∧
      (∀ i < m,∀ v,
        auxiliaryPhysicalDegree (T i) initial P credit i v+credit i v ≤ G.maxDegree-2*i) ∧
      (∀ i < m,
        let D := auxiliaryPhysicalDegree (S i) initial P credit i
        ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 < D v)) (G.maxDegree-2*i) test D) ∧
      (∀ i : Fin m,f i ≤ initial.card+1 ∧ ∀ k,(words i).endpoint k ∉ omitted i) ∧
      (∀ i ≤ m,∀ Q,auxiliaryPhysicalDegree Q initial P credit i =
        auxiliaryPhysicalDegree Q initial (H.states i).prescribed (H.states i).credit i) ∧
      (∀ (i : Fin m) k, let v := ((words i).endpoint k).val
        v ∈ finish.used i.val ∨ (∃ w ∈ initial,(P i.val).Adj v w) ∨ 0 < credit i.val v) ∧
      ∀ i < m,P i = finish.prescribed i ∧ credit i = finish.credit i := by
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  intro S T W f words omitted P credit
  have hW (i : Fin m) : W i.val = (H.steps i).cleanupSet := dif_pos i.isLt
  have hT (i : Fin m) : T i.val = (H.steps i).cleaned := dif_pos i.isLt
  have hWords (i : Fin m) :
      (words i).endpoint = (H.steps i).selection.round.words.endpoint ∧
      (words i).body = (H.steps i).selection.round.words.body ∧
      (words i).gaps = (H.steps i).selection.round.words.gaps ∧
      (words i).coreIncidentGaps = (H.steps i).selection.round.words.coreIncidentGaps ∧
      (words i).prescribedGraph = (H.steps i).selection.round.words.prescribedGraph ∧
      (words i).degreeCredit (omitted i) =
        (H.steps i).selection.round.words.degreeCredit (omitted i) :=
    replacement_words_cast_fields (hT i).symm _ _
  have hData (i : Fin m) : P i.val = (H.steps i).selection.round.words.prescribedGraph ∧
      credit i.val = (H.steps i).selection.round.words.degreeCredit (omitted i) := by
    obtain ⟨_,_,_,_,hP,hC⟩ := hWords i
    refine ⟨?_,?_⟩
    · simpa only [P,prescribedTrimmingHistory,dif_pos i.isLt] using hP
    · funext v
      simpa only [credit,trimmingCreditHistory,dif_pos i.isLt] using congrFun hC v
  have hFields (i : ℕ) (hi : i < m) : P i = finish.prescribed i ∧ credit i = finish.credit i := by
    have h := H.final_arrays ⟨i,hi⟩
    simp only [Nat.zero_add] at h
    have h' := hData ⟨i,hi⟩
    exact ⟨h'.1.trans h.1.symm,h'.2.trans h.2.1.symm⟩
  have hRead (i : ℕ) (hi : i ≤ m) (Q : SimpleGraph V) :
      auxiliaryPhysicalDegree Q initial P credit i =
        auxiliaryPhysicalDegree Q initial (H.states i).prescribed (H.states i).credit i := by
    funext v
    unfold auxiliaryPhysicalDegree
    split
    · rfl
    · congr 1
      apply sum_congr rfl
      intro k _
      have he := hFields k (k.isLt.trans_le hi)
      have hp := H.record_eq_final i m hi le_rfl k (by simpa only [Nat.zero_add] using k.isLt)
      rw [H.finishes] at hp
      rw [he.1,he.2,hp.1,hp.2.1]
  refine ⟨(congrArg VirtualTrimmingState.graph H.starts).trans hG,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hRead,?_,hFields⟩
  · intro i hi
    rw [hW ⟨i,hi⟩]
    exact (H.steps ⟨i,hi⟩).cleanup_subset
  · intro i hi
    rw [hW ⟨i,hi⟩,hT ⟨i,hi⟩]
    exact (H.steps ⟨i,hi⟩).cleanup
  · intro i hi
    rw [hT ⟨i,hi⟩,(hData ⟨i,hi⟩).1]
    exact congrArg VirtualTrimmingState.graph (H.steps ⟨i,hi⟩).next
  · intro i hi
    rw [hW ⟨i,hi⟩]
    exact (H.steps ⟨i,hi⟩).cleanup_independent
  · intro i
    obtain ⟨hEndpoint,hBody,hGaps,_,_,_⟩ := hWords i
    rw [hEndpoint,hBody,hGaps]
    exact (H.steps i).selection.round.empty_body_is_gap
  · intro i
    obtain ⟨_,hBody,hGaps,_,_,_⟩ := hWords i
    rw [hBody,hGaps]
    exact ⟨(H.steps i).selection.round.minimum_length,(H.steps i).selection.round.even_or_gap⟩
  · intro i
    rw [(hWords i).2.2.2.1]
    exact (H.steps i).selection.round.core_credit_bound
  · intro i hi v
    rw [hRead i hi.le,(hData ⟨i,hi⟩).2,hT ⟨i,hi⟩]
    simpa only [Nat.zero_add,omitted,TrimmingPackingSegment.layoutOmitted] using
      (H.steps ⟨i,hi⟩).selection.round.degree_cap v
  · intro i hi
    have h := (H.steps ⟨i,hi⟩).no_almost
    simpa only [hRead i hi.le (S i),S,VirtualTrimmingState.record,Nat.zero_add] using h
  · intro i
    rw [(hWords i).1]
    exact ⟨(H.steps i).selection.size_bound,(H.steps i).selection.round.endpoints_retained⟩
  · intro i k
    have hF := H.final_arrays i
    simp only [Nat.zero_add] at hF
    dsimp only
    rw [(hWords i).1,hF.2.2,(hData i).1,(hData i).2]
    rcases (H.steps i).endpoint_payment k with hFree | ⟨w,_,hEdge⟩ | hCredit
    · exact Or.inl hFree
    · have hTouch := (H.steps i).selection.round.words.prescribedGraph_meets_exceptional_set
        (H.steps i).selection.round.empty_body_is_gap _ _ hEdge
      have hv := mem_compl.mp ((H.steps i).selection.round.words.endpoint k).property
      exact Or.inr (Or.inl ⟨w,hTouch.resolve_right hv,hEdge.symm⟩)
    · exact Or.inr (Or.inr hCredit)

/-- A cleanup at a stopping boundary does not consume a packing
round. Its corrected record uses the same prescription arrays. -/
structure TrimmingPackingTermination (initial : Finset V) (S : VirtualTrimmingState V)
    (d test j cap : ℕ) (atLimit : Prop) where
  cleanupSet : Finset V
  cleaned : SimpleGraph V
  cleanup_subset : cleanupSet ⊆ initial
  cleanup_independent : S.graph.IsIndepSet (cleanupSet : Set V)
  cleanup : DeletionRun cleanupSet S.graph cleaned
  cleanup_below_target : ∀ w ∈ cleanupSet,S.graph.degree w < d
  free_load : ∀ v,projectionLoad (range j) S.used v ≤ cap
  stop : let degree := auxiliaryPhysicalDegree cleaned initial S.prescribed S.credit j
    atLimit ∨ HasAlmostOverfullRecord (univ.filter (fun v => 0 < degree v)) d test degree

def TrimmingPackingTermination.noCleanup
    {initial : Finset V} {S : VirtualTrimmingState V} {d test j cap : ℕ} {atLimit : Prop}
    (hLoad : ∀ v,projectionLoad (range j) S.used v ≤ cap)
    (h : atLimit ∨
      HasAlmostOverfullRecord (univ.filter (fun v => 0 < S.record initial j v)) d test (S.record initial j)) :
    TrimmingPackingTermination initial S d test j cap atLimit :=
  ⟨∅,S.graph,empty_subset _,by simp,DeletionRun.refl _,by simp,hLoad,h⟩

theorem TrimmingPackingTermination.weak_degree_sum
    {initial : Finset V} {S : VirtualTrimmingState V} {d test j cap budget : ℕ} {atLimit : Prop}
    (last : TrimmingPackingTermination initial S d test j cap atLimit)
    (h : S.HasWeakDegreeSum initial j d budget) :
    (⟨last.cleaned,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).HasWeakDegreeSum
      initial j d (budget+2*initial.card) := by
  apply h.after_cleanup last.cleanup
  intro v
  have hBalance : last.cleaned.degree v+(sdiff S.graph last.cleaned).degree v = S.graph.degree v := by
    simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,add_comm] using
      MaximumMatching.degree_sdiff_add_of_le S.graph last.cleaned (DeletionRun.le_source last.cleanup) v
  have hLoss := independent_auxiliary_preprocessing_degree_loss last.cleanup last.cleanup_independent v
  have hCard := card_le_card last.cleanup_subset
  omega

def TrimmingPackingSegment.empty (initial : Finset V) (D test cap j : ℕ) (S : VirtualTrimmingState V) :
    TrimmingPackingSegment initial D test cap j 0 S S :=
  ⟨fun _ => S,rfl,rfl,fun i => i.elim0⟩

theorem TrimmingPackingSegment.empty_weak
    {initial : Finset V} {D test cap j budget : ℕ} {S : VirtualTrimmingState V}
    (h : S.HasWeakDegreeSum initial j D budget) :
    (TrimmingPackingSegment.empty initial D test cap j S).HasWeakDegreeSums budget := by
  intro i hi
  have he : i = 0 := Nat.eq_zero_of_le_zero hi
  subst i
  exact h

def TrimmingPackingSegment.single
    {initial : Finset V} {D test cap j : ℕ} {S T : VirtualTrimmingState V}
    (R : TrimmingPackingStep initial S T D test j cap) :
    TrimmingPackingSegment initial D test cap j 1 S T := by
  refine ⟨fun i => if i = 0 then S else T,rfl,rfl,?_⟩
  intro i
  have h : i.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
  simpa only [h,if_true,zero_add,Nat.add_zero,Nat.mul_zero,Nat.sub_zero,Nat.one_ne_zero,if_false] using R

theorem TrimmingPackingSegment.single_weak
    {initial : Finset V} {D test cap j budget : ℕ} {S T : VirtualTrimmingState V}
    (R : TrimmingPackingStep initial S T D test j cap)
    (hStart : S.HasWeakDegreeSum initial j D budget)
    (hEnd : T.HasWeakDegreeSum initial (j+1) (D-2) budget) :
    (TrimmingPackingSegment.single R).HasWeakDegreeSums budget := by
  intro i hi
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · exact hStart
  · rw [(TrimmingPackingSegment.single R).finishes]
    simpa only [Nat.mul_one] using hEnd

def TrimmingPackingTermination.HasProfile
    {initial : Finset V} {S : VirtualTrimmingState V} {d test j cap : ℕ} {atLimit : Prop}
    (last : TrimmingPackingTermination initial S d test j cap atLimit) (width : ℕ) : Prop :=
  HasRoundLimitProfile (auxiliaryPhysicalDegree last.cleaned initial S.prescribed S.credit j)
    d test width atLimit

/-- At a switch, test the old graph first. When the run continues, put
the cleanup in its first row. When it stops at once, keep the cleanup
as a boundary witness with no artificial layer. -/
theorem TrimmingPackingSegment.run_after_cleanup
    {initial W : Finset V} {D test cap j total m budget width : ℕ} {S T : VirtualTrimmingState V}
    (K : TrimmingPackingSegment initial D test cap j m S T)
    (hFirst : ∀ i : Fin m,(K.steps i).cleaned = (K.states i).graph)
    (G : SimpleGraph V) (hW : W ⊆ initial) (hInd : G.IsIndepSet (W : Set V))
    (hClean : DeletionRun W G S.graph) (hm : m ≤ total)
    (hSmall : ∀ w ∈ W,G.degree w < D)
    (hWeak : (⟨G,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).HasWeakDegreeSum initial j D budget)
    (hRunWeak : K.HasWeakDegreeSums budget)
    (hStartLoad : ∀ v,projectionLoad (range j) S.used v ≤ cap)
    (hEndLoad : ∀ v,projectionLoad (range (j+m)) T.used v ≤ cap)
    (hLast : HasRoundLimitProfile (T.record initial (j+m)) (D-2*m) test width (m = total)) :
    let start : VirtualTrimmingState V := ⟨G,S.prescribed,S.credit,S.used⟩
    ∃ n ≤ total,∃ finish : VirtualTrimmingState V,
      ∃ F : TrimmingPackingSegment initial D test cap j n start finish,
      F.HasWeakDegreeSums budget ∧
      ∃ last : TrimmingPackingTermination initial finish (D-2*n) test (j+n) cap (n = total),
        last.HasProfile width := by
  intro start
  by_cases hPre : HasAlmostOverfullRecord (univ.filter (fun v => 0 < start.record initial j v))
      D test (start.record initial j)
  · have hPre' : HasRoundLimitProfile (start.record initial (j+0)) (D-2*0) test width (0 = total) :=
      Or.inr (by simpa only [Nat.mul_zero,Nat.sub_zero,Nat.add_zero] using hPre)
    exact ⟨0,Nat.zero_le _,start,TrimmingPackingSegment.empty initial D test cap j start,
      TrimmingPackingSegment.empty_weak hWeak,
      TrimmingPackingTermination.noCleanup hStartLoad hPre'.stop,hPre'⟩
  by_cases hZero : m = 0
  · subst m
    have hST : S = T := K.starts.symm.trans K.finishes
    subst T
    exact ⟨0,Nat.zero_le _,start,TrimmingPackingSegment.empty initial D test cap j start,
      TrimmingPackingSegment.empty_weak hWeak,
      ⟨W,S.graph,hW,hInd,hClean,hSmall,hStartLoad,hLast.stop⟩,hLast⟩
  have hPos : 0 < m := Nat.pos_of_ne_zero hZero
  have hGraph := (hFirst ⟨0,hPos⟩).trans (congrArg VirtualTrimmingState.graph K.starts)
  let F := K.prependCleanup hPos hGraph hW hInd hClean hSmall hPre
  have hNew := hRunWeak.of_unchanged_suffix (K := F) hWeak (by
    intro i _ hi
    change Function.update K.states 0 start i = K.states i
    exact Function.update_of_ne hi _ _)
  exact ⟨m,hm,T,F,hNew,TrimmingPackingTermination.noCleanup hEndLoad hLast.stop,hLast⟩

theorem TrimmingPackingTermination.append_segment
    {initial : Finset V} {D test cap j m n total width : ℕ} {F : VirtualTrimmingState V}
    (hEnd : TrimmingPackingTermination initial F (D-2*m-2*n) test (j+m+n) cap (n = total-m))
    (hProfile : hEnd.HasProfile width)
    (hm : m ≤ total) :
    ∃ last : TrimmingPackingTermination initial F (D-2*(m+n)) test (j+(m+n)) cap (m+n = total),
      last.HasProfile width := by
  have h : HasRoundLimitProfile (auxiliaryPhysicalDegree hEnd.cleaned initial F.prescribed F.credit
      (j+(m+n))) (D-2*(m+n)) test width (m+n = total) := by
    have he : (n = total-m) = (m+n = total) := propext (by omega)
    simpa only [TrimmingPackingTermination.HasProfile,Nat.sub_sub,←Nat.mul_add,Nat.add_assoc,he] using hProfile
  exact ⟨⟨hEnd.cleanupSet,hEnd.cleaned,hEnd.cleanup_subset,
    hEnd.cleanup_independent,hEnd.cleanup,
    by simpa only [Nat.sub_sub,←Nat.mul_add] using hEnd.cleanup_below_target,
    by simpa only [Nat.add_assoc] using hEnd.free_load,h.stop⟩,h⟩

set_option maxHeartbeats 3000000 in
theorem HasShortTrimmingAfterExhaustion.to_packing_segment
    {S : VirtualTrimmingState V} {initial current support : Finset V}
    {w : V} {d floor loss threshold test j cap left budget : ℕ}
    (h : HasShortTrimmingAfterExhaustion S initial current support w d floor loss threshold test j cap left)
    (hw : w ∈ initial) (hLeft : 1 ≤ left)
    (hWindow : floor+2 ≤ d-2*left)
    (hWeak : S.HasWeakDegreeSum initial j d budget)
    (hStartLoad : ∀ v,projectionLoad (range j) S.used v ≤ cap) :
    ∃ n ≤ left,∃ finish : VirtualTrimmingState V,
      ∃ K : TrimmingPackingSegment initial d test cap j n S finish,
      K.HasWeakDegreeSums (budget+2*loss+2*current.card+22) ∧
      ∃ last : TrimmingPackingTermination initial finish (d-2*n) test (j+n) cap (n = left),
        last.HasProfile (d-2*left-floor+loss+current.card+8) := by
  obtain ⟨hSmall,T,hClean,hCleanLoss,k,hk,R,hRound,hReady,hEnd⟩ := h
  let base : VirtualTrimmingState V := ⟨T,S.prescribed,S.credit,S.used⟩
  let B := budget+2*loss+2*current.card+22
  let width := d-2*left-floor+loss+current.card+8
  have hBase : base.HasWeakDegreeSum initial j d (budget+2) :=
    hWeak.after_cleanup hClean (fun v => (hCleanLoss v).1)
  have hReadyWeak := hRound.weak_degree_sum hReady hBase
  have hWiden : S.HasWeakDegreeSum initial j d B := hWeak.mono (by dsimp only [B]; omega)
  have hStepBound : budget+2+2 ≤ B := by dsimp only [B]; omega
  have hTail :
      ∃ n ≤ left-k,∃ finish : VirtualTrimmingState V,
        ∃ K : TrimmingPackingSegment initial (d-2*k) test cap (j+k) n R finish,
        (∀ i : Fin n,(K.steps i).cleaned = (K.states i).graph) ∧
        K.HasWeakDegreeSums B ∧
        (∀ v,projectionLoad (range (j+k+n)) finish.used v ≤ cap) ∧
        HasRoundLimitProfile (finish.record initial (j+k+n)) (d-2*k-2*n) test width
          (n = left-k) := by
    rcases hEnd with hAlmost | ⟨A,hPair,n,hn,H,hStop⟩
    · refine ⟨0,Nat.zero_le _,R,TrimmingPackingSegment.empty _ _ _ _ _ R,
        (fun i => i.elim0),TrimmingPackingSegment.empty_weak (hReadyWeak.mono hStepBound),
        hReady.free_load,Or.inr ?_⟩
      simpa only [Nat.mul_zero,Nat.sub_zero,Nat.add_zero,hReady.support_eq] using hAlmost
    · obtain ⟨K,hStates,hStart⟩ := H.to_packing_segment
      have hCapWeak : budget+2+2+2*(loss+current.card+4+5) ≤ B := by dsimp only [B]; omega
      have hK : K.HasWeakDegreeSums B := by
        intro i hi
        rw [hStates]
        exact (H.weak_degree_sum_prefix hReady.current_initial hPair hReady.core_support
          hReadyWeak i hi).mono hCapWeak
      let P := H.positions n le_rfl
      refine ⟨n,hn,H.states n,K,hStart,hK,P.free_load,?_⟩
      rcases hStop with hLimit | hAlmost
      · have hkL : k ≤ left := hk.trans hLeft
        have hd : d-2*k-2*n = d-2*left := by omega
        have hDense := P.dense_record hReady.current_initial hPair hReady.support_even (hd ▸ hWindow)
        exact Or.inl ⟨hLimit,by simpa only [width,hd,Nat.add_assoc] using hDense⟩
      · exact Or.inr (by simpa only [P.support_eq] using hAlmost)
  obtain ⟨n,hn,F,K,hFirst,hTailWeak,hEndLoad,hLast⟩ := hTail
  have hW : ({w} : Finset V) ⊆ initial := singleton_subset_iff.mpr hw
  have hInd : S.graph.IsIndepSet (({w} : Finset V) : Set V) := by
    intro x hx y hy hne _
    exact hne ((mem_singleton.mp hx).trans (mem_singleton.mp hy).symm)
  have hBelow : ∀ z ∈ ({w} : Finset V),S.graph.degree z < d := by
    intro z hz
    have he : z = w := mem_singleton.mp hz
    subst z
    exact hSmall
  rcases hRound with ⟨rfl,rfl⟩ | ⟨rfl,hNeutral,_,_⟩
  · exact K.run_after_cleanup hFirst S.graph hW hInd hClean hn hBelow hWiden hTailWeak
      hStartLoad hEndLoad hLast
  by_cases hPre : HasAlmostOverfullRecord (univ.filter (fun v => 0 < S.record initial j v))
      d test (S.record initial j)
  · have hPre' : HasRoundLimitProfile (S.record initial (j+0)) (d-2*0) test width (0 = left) :=
      Or.inr (by simpa only [Nat.mul_zero,Nat.sub_zero,Nat.add_zero] using hPre)
    exact ⟨0,Nat.zero_le _,S,TrimmingPackingSegment.empty _ _ _ _ _ S,
      TrimmingPackingSegment.empty_weak hWiden,
      TrimmingPackingTermination.noCleanup hStartLoad hPre'.stop,hPre'⟩
  obtain ⟨row,_⟩ := hNeutral.to_packing_step_after_cleanup hW hInd hClean hBelow hPre
  let first := TrimmingPackingSegment.single row
  let hEnd' : TrimmingPackingTermination initial F (d-2*1-2*n) test (j+1+n) cap (n = left-1) :=
    TrimmingPackingTermination.noCleanup hEndLoad hLast.stop
  have hFirstWeak : first.HasWeakDegreeSums B :=
    TrimmingPackingSegment.single_weak row hWiden (by
      simpa only [Nat.mul_one] using hReadyWeak.mono hStepBound)
  exact ⟨1+n,by omega,F,first.append K,hFirstWeak.append hTailWeak,
    hEnd'.append_segment hLast hLeft⟩

set_option maxHeartbeats 3800000 in
theorem HasCompletedShortTrimmingPhase.to_packing_segment_after_cleanup
    {start : VirtualTrimmingState V} {initial current active W : Finset V}
    {D floor loss threshold test j cap total budget : ℕ}
    (h : HasCompletedShortTrimmingPhase start initial current active D floor loss threshold test j cap total)
    (E : CriticalTrimmingEntry start.graph initial current active (start.record initial j) D floor loss)
    (hWindow : floor+2 ≤ D-2*total)
    (G : SimpleGraph V) (hW : W ⊆ initial) (hInd : G.IsIndepSet (W : Set V))
    (hClean : DeletionRun W G start.graph)
    (hSmall : ∀ w ∈ W,G.degree w < D)
    (hBeforeWeak : (⟨G,start.prescribed,start.credit,start.used⟩ : VirtualTrimmingState V).HasWeakDegreeSum
      initial j D budget)
    (hWeak : start.HasWeakDegreeSum initial j D budget)
    (hStartLoad : ∀ v,projectionLoad (range j) start.used v ≤ cap) :
    let base : VirtualTrimmingState V := ⟨G,start.prescribed,start.credit,start.used⟩
    ∃ n ≤ total,∃ finish : VirtualTrimmingState V,
      ∃ K : TrimmingPackingSegment initial D test cap j n base finish,
      K.HasWeakDegreeSums (budget+4*loss+4*initial.card+30) ∧
      ∃ last : TrimmingPackingTermination initial finish (D-2*n) test (j+n) cap (n = total),
        last.HasProfile (D-2*total-floor+loss+initial.card+8) := by
  intro base
  let B := budget+4*loss+4*initial.card+30
  let width := D-2*total-floor+loss+initial.card+8
  have hWiden : base.HasWeakDegreeSum initial j D B := hBeforeWeak.mono (by dsimp only [B]; omega)
  have hCard : current.card ≤ initial.card := card_le_card E.current_initial
  have hCore : initialᶜ ⊆ univ.filter (fun v => 0 < start.record initial j v) := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _,lt_of_lt_of_le (by decide) (E.core_room v (mem_compl.mp hv))⟩
  obtain ⟨m,hm,hMode⟩ := h
  rcases hMode with ⟨hPair,H,hStop⟩ | ⟨w,hA,H,hStop⟩
  · obtain ⟨K,hStates,hFirst⟩ := H.to_packing_segment
    have hRunWeak : K.HasWeakDegreeSums B := by
      intro i hi
      rw [hStates]
      exact (H.weak_degree_sum_prefix E.current_initial hPair hCore hWeak i hi).mono (by
        dsimp only [B]
        omega)
    refine K.run_after_cleanup hFirst G hW hInd hClean hm hSmall hWiden hRunWeak
      hStartLoad (H.positions m le_rfl).free_load
      (width := width) ?_
    rcases hStop with rfl | hAlmost
    · have hDense := (H.positions m le_rfl).dense_record E.current_initial hPair
        (E.active_parity.mpr hPair) hWindow
      exact Or.inl ⟨rfl,hDense.mono (by dsimp only [width]; omega)⟩
    · exact Or.inr (by simpa only [(H.positions m le_rfl).support_eq] using hAlmost)
  have hw : w ∈ current := E.active_current (hA.symm ▸ mem_singleton_self w)
  have hwI := E.current_initial hw
  have hwS : w ∈ univ.filter (fun v => 0 < start.record initial j v) :=
    mem_filter.mpr ⟨mem_univ _,E.current_positive w hw⟩
  obtain ⟨K,hStates,hFirst⟩ := H.to_packing_segment hwI hwS
  have hSingleton := H.weak_degree_sum_prefix E.current_initial hw hCore hWeak
  have hRunWeak : K.HasWeakDegreeSums B := by
    intro i hi
    rw [hStates]
    exact (hSingleton i hi).mono (by dsimp only [B]; omega)
  have hEndLoad := (H.positions m le_rfl).free_load
  rcases hStop with hLimit | hAlmost | ⟨hBefore,hPos,hExhaust⟩
  · subst m
    have hDense := (H.positions total le_rfl).dense_record E.current_initial hw hWindow
    exact K.run_after_cleanup (width := width) hFirst G hW hInd hClean hm hSmall hWiden hRunWeak
      hStartLoad hEndLoad (Or.inl ⟨rfl,hDense.mono (by dsimp only [width]; omega)⟩)
  · exact K.run_after_cleanup hFirst G hW hInd hClean hm hSmall hWiden hRunWeak
      hStartLoad hEndLoad (Or.inr hAlmost)
  by_cases hPre : HasAlmostOverfullRecord (univ.filter (fun v => 0 < base.record initial j v))
      D test (base.record initial j)
  · have hPre' : HasRoundLimitProfile (base.record initial (j+0)) (D-2*0) test width (0 = total) :=
      Or.inr (by simpa only [Nat.mul_zero,Nat.sub_zero,Nat.add_zero] using hPre)
    exact ⟨0,Nat.zero_le _,base,TrimmingPackingSegment.empty _ _ _ _ _ base,
      TrimmingPackingSegment.empty_weak hWiden,
      TrimmingPackingTermination.noCleanup hStartLoad hPre'.stop,hPre'⟩
  have hGraph := (hFirst ⟨0,hPos⟩).trans (congrArg VirtualTrimmingState.graph K.starts)
  let first := K.prependCleanup hPos hGraph hW hInd hClean hSmall hPre
  have hFirstWeak := hRunWeak.of_unchanged_suffix (K := first) hWiden (by
    intro i _ hi
    change Function.update K.states 0 base i = K.states i
    exact Function.update_of_ne hi _ _)
  have hd : D-2*m-2*(total-m) = D-2*total := by omega
  obtain ⟨n,hn,F,tail,hTailWeak,last,hProfile⟩ :=
    hExhaust.to_packing_segment hwI (Nat.sub_pos_of_lt hBefore) (hd ▸ hWindow)
      (hSingleton m le_rfl) hEndLoad
  have hWidth : D-2*m-2*(total-m)-floor+loss+current.card+8 ≤ width := by
    rw [hd]
    dsimp only [width]
    omega
  exact ⟨m+n,by omega,F,first.append tail,hFirstWeak.append (hTailWeak.mono (by
    dsimp only [B]
    omega)),last.append_segment (hProfile.mono hWidth) hm⟩

set_option maxHeartbeats 4000000 in
/-- Compile the original and inherited phases into one zero-based
history of actual cleanups and prescriptions, ending at a round limit
or at a certified almost-overfull record. -/
theorem cms_operation_4_1_packing_history
    (G : SimpleGraph V) [DecidableRel G.Adj] (η : ℝ) (hη : 0 ≤ η) (hSmall : η ≤ 1/64)
    (hVAL : ∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v)
    (test : ℕ) (hTest : 1 ≤ test) :
    let n := Fintype.card V
    let initial := initialExceptionalSet G η
    let shift := η*(n:ℝ)
    let cap := ⌊shift⌋₊
    let long := ⌊(G.maxDegree:ℝ)/3-shift⌋₊
    let short := ⌊(G.maxDegree:ℝ)/3-2*shift⌋₊
    64 ≤ shift → 6 ≤ η^2*(n:ℝ) → 24*shift ≤ (G.maxDegree:ℝ) →
    (initial.card:ℝ) ≤ η^2*(n:ℝ) →
    ∃ m ≤ long,∃ start finish : VirtualTrimmingState V,
      start.graph = G ∧
      ∃ K : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish,
      K.HasWeakDegreeSums (⌊2*shift⌋₊-2*initial.card) ∧
      ∃ last : TrimmingPackingTermination initial finish (G.maxDegree-2*m) test m cap
        (m = long ∨ short ≤ m), last.HasProfile ⌊6*shift⌋₊ := by
  intro n initial shift cap long short hShift hSize hDense hFew
  let low := initialLowSet G η
  let threshold := ⌈shift⌉₊
  let originalBudget := max (threshold+low.card) (4*low.card+2*(initial.card+1))
  let entryBudget := originalBudget+2*low.card
  let loss := 3*low.card+initial.card+1
  let totalBudget := entryBudget+4*loss+4*initial.card+30
  let bound := ⌊2*shift⌋₊-2*initial.card
  have hLow : low ⊆ initial := filter_subset _ _
  have hCard := card_le_card hLow
  have hCardR : (low.card:ℝ) ≤ initial.card := by exact_mod_cast hCard
  have hInd := initial_low_set_independent G η hη hVAL
  have hCeil : shift ≤ (threshold:ℝ) := Nat.le_ceil _
  have hCeil' : (threshold:ℝ) ≤ shift+1 := (Nat.ceil_lt_add_one (by linarith only [hShift])).le
  have hFew' : (initial.card:ℝ) ≤ shift/64 := by
    have h := mul_le_mul_of_nonneg_right hSmall (show 0 ≤ shift by linarith only [hShift])
    dsimp only [shift] at h ⊢
    nlinarith only [h,hFew]
  have hOriginalBudget : originalBudget = threshold+low.card := by
    apply max_eq_left
    exact_mod_cast (show 4*(low.card:ℝ)+2*((initial.card:ℝ)+1) ≤ (threshold:ℝ)+low.card by
      linarith only [hCardR,hFew',hShift,hCeil])
  have hTotal : totalBudget ≤ bound := by
    have hTot : (totalBudget+2*initial.card:ℕ) ≤ ⌊2*shift⌋₊ := by
      apply Nat.le_floor
      dsimp only [totalBudget,entryBudget,loss]
      rw [hOriginalBudget]
      push_cast
      linarith only [hCardR,hFew',hShift,hCeil']
    dsimp only [bound]
    omega
  have hShort : short ≤ long := by
    apply Nat.floor_mono
    linarith only [hShift]
  have hFloor : (long:ℝ) ≤ (G.maxDegree:ℝ)/3-shift :=
    Nat.floor_le (by linarith only [hShift,hDense])
  have hLongPos : 0 < long := by
    change 1 ≤ long
    apply Nat.le_floor
    push_cast
    linarith only [hShift,hDense]
  have hTriple : 3*long ≤ G.maxDegree := by
    exact_mod_cast (show (3:ℝ)*long ≤ (G.maxDegree:ℝ) by linarith only [hFloor,hShift])
  have hLongBand : long+threshold+low.card ≤ G.maxDegree-2*long := by
    have h := (show (3:ℝ)*long+(threshold:ℝ)+low.card ≤ G.maxDegree by
      linarith only [hFloor,hShift,hCeil',hCardR,hFew'])
    have hh : 3*long+threshold+low.card ≤ G.maxDegree := by exact_mod_cast h
    omega
  obtain ⟨_,_,hReserve⟩ :=
    critical_phase_rounded_reserves n G.maxDegree initial.card η hη hSmall hShift hDense hFew
  change 5*initial.card+cap+4+(5*initial.card+12) ≤ long at hReserve
  have hThreshold : 2 ≤ threshold := by
    exact_mod_cast (show (2:ℝ) ≤ threshold by linarith only [hShift,hCeil])
  have hWidth (r : ℕ) (hrS : short ≤ r) (hrL : r ≤ long) :
      G.maxDegree-2*r-long+loss+initial.card+8 ≤ ⌊6*shift⌋₊ := by
    have hLongLt : (G.maxDegree:ℝ)/3-shift < (long:ℝ)+1 :=
      Nat.lt_floor_add_one ((G.maxDegree:ℝ)/3-shift)
    have hShortLt : (G.maxDegree:ℝ)/3-2*shift < (short:ℝ)+1 :=
      Nat.lt_floor_add_one ((G.maxDegree:ℝ)/3-2*shift)
    have hr : (short:ℝ) ≤ r := by exact_mod_cast hrS
    have hSub : 2*r ≤ G.maxDegree := by omega
    have hSub' : long ≤ G.maxDegree-2*r := by omega
    apply Nat.le_floor
    dsimp only [loss]
    push_cast [Nat.cast_sub hSub,Nat.cast_sub hSub']
    linarith only [hr,hLongLt,hShortLt,hFew',hCardR,hShift]
  have hLowDegree (w : V) (hw : w ∈ low) : G.degree w < G.maxDegree-2*long := by
    have hv : (G.degree w:ℝ) < (G.maxDegree:ℝ)/3-shift := (mem_filter.mp hw).2
    have h : (G.degree w:ℝ)+2*(long:ℝ) < G.maxDegree := by linarith only [hv,hFloor,hShift]
    have hNat : G.degree w+2*long < G.maxDegree := by exact_mod_cast h
    omega
  have hOrd (v : V) (hv : v ∉ initial) : G.maxDegree ≤ G.degree v+threshold := by
    have hv' : (G.maxDegree:ℝ)-G.degree v ≤ shift := by
      by_contra! hn
      exact hv (mem_filter.mpr ⟨mem_univ _,hn⟩)
    exact_mod_cast (show (G.maxDegree:ℝ) ≤ (G.degree v:ℝ)+threshold by linarith only [hv',hCeil])
  obtain ⟨m,hm,H,hBoundary⟩ :=
    cms_operation_4_1_original_and_short_phases G η hη hSmall hVAL test hTest hShift hSize hDense hFew
  change m ≤ long at hm
  have hBelow (w : V) (hw : w ∈ low) : G.degree w < G.maxDegree-2*m :=
    (hLowDegree w hw).trans_le (Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 hm) _)
  have hRoom : 2*m ≤ G.maxDegree := by
    have hmR : (m:ℝ) ≤ long := by exact_mod_cast hm
    have hD0 : 0 ≤ (G.maxDegree:ℝ) := Nat.cast_nonneg _
    exact_mod_cast (show (2:ℝ)*m ≤ G.maxDegree by linarith only [hmR,hFloor,hShift,hD0])
  obtain ⟨original,hStates⟩ := H.to_packing_segment hLow hInd hBelow
  let start : VirtualTrimmingState V := ⟨G,H.prescribed,H.credit,H.free⟩
  let finish : VirtualTrimmingState V := ⟨H.graph m,H.prescribed,H.credit,H.free⟩
  have hOriginalWeak : original.HasWeakDegreeSums originalBudget := by
    intro i hi u v he
    have hRead := H.degree_exact i hi
    rw [hStates] at he ⊢
    simpa only [←hRead,Nat.zero_add,VirtualTrimmingState.record] using
      H.weak_degree_sum hInd hVAL hOrd hRoom i hi u v he
  have hBound : original.HasWeakDegreeSums bound := hOriginalWeak.mono (by
    apply le_trans _ hTotal
    dsimp only [totalBudget,entryBudget]
    omega)
  have hFinishWeak : finish.HasWeakDegreeSum initial m (G.maxDegree-2*m) originalBudget := by
    simpa only [original.finishes,Nat.zero_add] using hOriginalWeak m le_rfl
  rcases hBoundary with hLimit | hAlmost | ⟨T,hClean,hNext⟩
  · have hDenseRecord : HasDenseRoundLimitRecord (H.degree m) (G.maxDegree-2*m) ⌊6*shift⌋₊ := by
      subst m
      have hHigh (v : V) (hv : v ∈ initial) (hNot : v ∉ low) : long ≤ G.degree v := by
        apply Nat.floor_le_of_le
        by_contra! hv'
        exact hNot (mem_filter.mpr ⟨hv,hv'⟩)
      have hStartDegree (v : V) (hv : v ∈ low) :
          (G.degree v:ℝ) < (G.maxDegree:ℝ)/3-shift := (mem_filter.mp hv).2
      have hMargin : 5*initial.card+cap+4+(4*initial.card+2) ≤ long := by omega
      have hLocal := H.dense_record_at_long_limit ((G.maxDegree:ℝ)/3-shift) hLow hInd hLongPos
        (by omega : 1 ≤ threshold) hStartDegree hOrd hHigh hMargin hLongBand
      change HasDenseRoundLimitRecord (H.degree long) (G.maxDegree-2*long)
        (G.maxDegree-2*long-long+2*low.card+initial.card+1) at hLocal
      refine hLocal.mono (le_trans ?_ (hWidth long hShort le_rfl))
      dsimp only [loss]
      omega
    have hRead : H.degree m = finish.record initial m := H.degree_exact m le_rfl
    refine ⟨m,hm,start,finish,rfl,original,hBound,
      TrimmingPackingTermination.noCleanup H.free_load (Or.inl (Or.inl hLimit)),?_⟩
    rw [hRead] at hDenseRecord
    exact Or.inl ⟨Or.inl hLimit,hDenseRecord⟩
  · have hRead : H.degree m = finish.record initial m := H.degree_exact m le_rfl
    rw [hRead] at hAlmost
    exact ⟨m,hm,start,finish,rfl,original,hBound,
      TrimmingPackingTermination.noCleanup H.free_load (Or.inr hAlmost),Or.inr hAlmost⟩
  let W := H.exceptional m ∩ low
  have hW : W ⊆ initial := inter_subset_right.trans hLow
  have hLe : H.graph m ≤ G :=
    (virtual_trimming_prefix_le H.graph H.cleaned H.prescribed m
      (fun i hi => DeletionRun.le_source (H.cleanup i hi)) H.graph_next 0 m (Nat.zero_le _) le_rfl).trans
      H.graph_zero.le
  have hIndependent : (H.graph m).IsIndepSet (W : Set V) := by
    intro a ha b hb hne hab
    exact hInd (mem_inter.mp ha).2 (mem_inter.mp hb).2 hne (hLe hab)
  have hCleanup (w : V) (hw : w ∈ W) : (H.graph m).degree w < G.maxDegree-2*m :=
    (degree_le_of_le hLe (v := w)).trans_lt (hBelow w (mem_inter.mp hw).2)
  rcases hNext with hAlmost | ⟨A,E,hShortOutcome⟩
  · exact ⟨m,hm,start,finish,rfl,original,hBound,
      ⟨W,T,hW,hIndependent,hClean,hCleanup,H.free_load,Or.inr hAlmost⟩,Or.inr hAlmost⟩
  rcases hShortOutcome with hLimit | hShortRun
  · have hLocal := E.dense_record
    change HasDenseRoundLimitRecord
      (auxiliaryPhysicalDegree T initial H.prescribed H.credit m) (G.maxDegree-2*m)
      (G.maxDegree-2*m-long+loss+1) at hLocal
    have hDenseRecord := hLocal.mono (le_trans (by omega) (hWidth m hLimit hm))
    exact ⟨m,hm,start,finish,rfl,original,hBound,
      ⟨W,T,hW,hIndependent,hClean,hCleanup,H.free_load,Or.inl (Or.inr hLimit)⟩,
      Or.inl ⟨Or.inr hLimit,hDenseRecord⟩⟩
  have hLoss (v : V) : (sdiff finish.graph T).degree v ≤ low.card := by
    have hBalance : (sdiff finish.graph T).degree v+T.degree v = finish.graph.degree v := by
      simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le finish.graph T (DeletionRun.le_source hClean) v
    have hAux := independent_auxiliary_preprocessing_degree_loss hClean hIndependent v
    change finish.graph.degree v ≤ T.degree v+W.card at hAux
    have hCardW : W.card ≤ low.card := card_le_card inter_subset_right
    omega
  have hEntry := hFinishWeak.after_cleanup hClean hLoss
  have hShortWindow : long+2 ≤ G.maxDegree-2*m-2*(short-m) := by
    have h : m+(short-m) = max m short := by omega
    rw [Nat.sub_sub,←Nat.mul_add,h]
    have hLongWindow : long+2 ≤ G.maxDegree-2*long := by omega
    exact hLongWindow.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 (max_le hm hShort)) _)
  obtain ⟨k,hk,F,tail,hTailWeak,last,hProfile⟩ :=
    hShortRun.to_packing_segment_after_cleanup E hShortWindow (H.graph m) hW hIndependent hClean hCleanup
      (hFinishWeak.mono (Nat.le_add_right _ _)) hEntry H.free_load
  change k ≤ short-m at hk
  change tail.HasWeakDegreeSums totalBudget at hTailWeak
  let WithClock (clock : ℕ) := ∃ K : TrimmingPackingSegment initial (G.maxDegree-2*m) test cap clock k finish F,
    K.HasWeakDegreeSums bound
  have hTailAtM : WithClock m := ⟨tail,hTailWeak.mono hTotal⟩
  have hAligned : WithClock (0+m) :=
    (congrArg WithClock (Nat.zero_add m)).mpr hTailAtM
  obtain ⟨hTail,hTailBound⟩ := hAligned
  have hSizeFinal : m+k ≤ long := by omega
  have hWidth' : G.maxDegree-2*m-2*(short-m)-long+loss+initial.card+8 ≤ ⌊6*shift⌋₊ := by
    have he : G.maxDegree-2*m-2*(short-m) = G.maxDegree-2*(max m short) := by omega
    rw [he]
    exact hWidth _ (le_max_right _ _) (max_le hm hShort)
  have hFinal : HasRoundLimitProfile
      (auxiliaryPhysicalDegree last.cleaned initial F.prescribed F.credit (m+k))
      (G.maxDegree-2*(m+k)) test ⌊6*shift⌋₊ (m+k = long ∨ short ≤ m+k) := by
    have hCover := (hProfile.mono hWidth')
    let degree := auxiliaryPhysicalDegree last.cleaned initial F.prescribed F.credit (m+k)
    change HasRoundLimitProfile degree (G.maxDegree-2*m-2*k) test ⌊6*shift⌋₊
      (k = short-m) at hCover
    change HasRoundLimitProfile degree (G.maxDegree-2*(m+k)) test ⌊6*shift⌋₊
      (m+k = long ∨ short ≤ m+k)
    unfold HasRoundLimitProfile at hCover ⊢
    rw [Nat.sub_sub,←Nat.mul_add] at hCover
    exact hCover.imp_left (fun ⟨hLimit,hDenseRecord⟩ => ⟨Or.inr (by omega),hDenseRecord⟩)
  exact ⟨m+k,hSizeFinal,start,F,rfl,original.append hTail,hBound.append hTailBound,⟨last.cleanupSet,last.cleaned,
    last.cleanup_subset,last.cleanup_independent,last.cleanup,
    by simpa only [Nat.sub_sub,←Nat.mul_add] using last.cleanup_below_target,last.free_load,hFinal.stop⟩,hFinal⟩

end OverfullWork.CMSTrimmingRound
