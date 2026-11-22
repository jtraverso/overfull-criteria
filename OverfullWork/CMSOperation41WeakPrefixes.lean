module

public import OverfullWork.CMSOperation41CriticalReselection

@[expose] public section


/-! The weak degree sum in the original phase of Operation 4.1.
Two original low vertices cannot be adjacent. If a low endpoint is
still exceptional, it was active in every earlier round of this edge's
history. Otherwise the special-vertex charges of two endpoints share
one count per round. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 5500000 in
/-- CMS Claim 4.2(3) on every original-phase prefix, with the losses
expressed in the finite sets used by the actual prescriptions. -/
theorem OriginalTrimmingHistory.weak_degree_sum
    {G : SimpleGraph V} [dG : DecidableRel G.Adj] {initial low : Finset V}
    {threshold floor cap test m : ℕ}
    (H : OriginalTrimmingHistory G initial low threshold floor cap test m)
    (hInd : G.IsIndepSet (low : Set V))
    (hVAL : ∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v)
    (hOrd : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+threshold) (hRoom : 2*m ≤ G.maxDegree) :
    ∀ j ≤ m,∀ u v,(H.graph j).Adj u v →
      G.maxDegree-2*j ≤ H.degree j u+H.degree j v+
        max (threshold+low.card) (4*low.card+2*(initial.card+1)) := by
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  let S := H.graph
  let T := H.cleaned
  let P := H.prescribed
  let U := H.exceptional
  let support (i : ℕ) := univ.filter (fun v => 0 < H.degree i v)
  let loss (i : ℕ) (v : V) := (sdiff (S i) (T i)).degree v
  have hClean (i : ℕ) (hi : i < m) : T i ≤ S i := DeletionRun.le_source (H.cleanup i hi)
  have hP (i : ℕ) (hi : i < m) : P i ≤ T i := by
    obtain ⟨_,R,hEq,_,_,_,_⟩ := H.selection i hi
    change H.prescribed i ≤ H.cleaned i
    rw [hEq]
    exact R.round.words.prescribedGraph_le
  have hNext (i : ℕ) (hi : i < m) : S (i+1) ≤ T i := by
    change H.graph (i+1) ≤ H.cleaned i
    rw [H.graph_next i hi]
    exact sdiff_le
  have hDecrease := virtual_trimming_prefix_le S T P m hClean H.graph_next
  have hNested := trimming_exceptional_sets_antitone U support H.degree G.maxDegree threshold m H.exceptional_next
  have hU (j : ℕ) (hj : j ≤ m) : U j ⊆ initial := H.exceptional_zero ▸ hNested j hj 0 (Nat.zero_le _)
  have hLoss (j : ℕ) (hj : j ≤ m) (v : V) : (∑ i ∈ range j,loss i v) ≤ low.card := by
    rw [←Fin.sum_univ_eq_sum_range (fun i => loss i v) j]
    exact cumulative_cleanup_degree_le_original_low_card G low S T (fun i => U i ∩ low) m
      H.graph_zero hInd H.cleanup (fun _ _ => Or.inl inter_subset_right) hNext j hj v
  have hSupport (i : ℕ) (hi : i < m) : support (i+1) ⊆ support i := by
    intro v hv
    have hp := (mem_filter.mp hv).2
    have h := H.degree_next i hi v
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hRetired := nonexceptional_degree_from_update_history G.maxDegree m threshold U support H.degree loss
    (by
      intro v _ hv
      rw [H.degree_zero]
      exact hOrd v (fun h => hv (by simpa only [U,H.exceptional_zero] using h)))
    hSupport H.exceptional_next
    (fun i hi v _ _ => by have h := H.degree_next i hi v; change _+loss i v+_ = _ at h; omega) hRoom
  have hBasic (j : ℕ) (hj : j ≤ m) (v : V) :
      G.degree v ≤ H.degree j v+2*j+(∑ i ∈ range j,loss i v) := by
    induction j with
    | zero => simp [H.degree_zero]
    | succ j ih =>
      have hlt := Nat.lt_of_succ_le hj
      have h := ih hlt.le
      have hStep := H.degree_next j hlt v
      change _+loss j v+_ = _ at hStep
      rw [sum_range_succ]
      omega
  have hOrdinary (j : ℕ) (hj : j ≤ m) (v : V) (hv : v ∉ U j) (hPos : 0 < (S j).degree v) :
      G.maxDegree-2*j ≤ H.degree j v+threshold+low.card := by
    by_cases hvI : v ∈ initial
    · have hDegree : H.degree j v = (S j).degree v := by
        rw [H.degree_exact j hj,auxiliaryPhysicalDegree,if_pos hvI]
      have h := hRetired j hj v (mem_filter.mpr ⟨mem_univ _,hDegree.symm ▸ hPos⟩) hv
      have hLost := hLoss j hj v
      omega
    · have hD := hOrd v hvI
      have hB := hBasic j hj v
      have hLost := hLoss j hj v
      omega
  have hNonlow (j : ℕ) (hj : j ≤ m) (v : V) (hv : v ∈ U j) (hn : v ∉ low)
      (hPos : 0 < (S j).degree v) :
      G.degree v ≤ H.degree j v+(2*low.card+(initial.card+1))+2*specialUseCount H.special j v := by
    let incident (i : ℕ) := (((sdiff (S i) (T i)) ⊔ P i).neighborFinset v ∩ low).card
    have hDebit (i : ℕ) (hi : i < j) :
        loss i v+(P i).degree v ≤ 2*incident i+
          (if H.special i = some v then 2 else 0)+(if H.internal i v then 1 else 0) := by
      have him := hi.trans_le hj
      obtain ⟨_,R,hEq,_,hSpecial,hInternal,_⟩ := H.selection i him
      have hvU := hNested j hj i hi.le hv
      have hCleanRecord :
          H.degree i v-(sdiff (H.graph i) (H.cleaned i)).degree v = (T i).degree v := by
        have h := auxiliary_physical_degree_after_cleanup (H.graph i) (H.cleaned i) initial
          H.prescribed H.credit i (hClean i him) v
        rw [auxiliaryPhysicalDegree,if_pos (hU i him.le hvU),←H.degree_exact i him.le] at h
        exact h.symm
      have hTPos := hPos.trans_le (degree_le_of_le
        ((hDecrease (i+1) j (Nat.succ_le_of_lt hi) hj).trans (hNext i him)) (v := v))
      have hvR : v ∈ H.exceptional i ∩
          univ.filter (fun x => 0 < H.degree i x-(sdiff (H.graph i) (H.cleaned i)).degree x) :=
        mem_inter.mpr ⟨hvU,mem_filter.mpr ⟨mem_univ _,hCleanRecord.symm ▸ hTPos⟩⟩
      have hCost := R.exceptional_cost (H.graph i) low hvR (inter_subset_left.trans (hU i him.le))
        (fun h => hn (mem_inter.mp (mem_filter.mp h).1).2)
        (fun _ h => (mem_inter.mp (mem_filter.mp h).1).2)
        (fun x hx => (mem_inter.mp ((cleanup_removed_edge_meets_active (H.cleanup i him) hx).resolve_left
          (fun h => hn (mem_inter.mp h).2))).2)
      have hDegrees : (P i).degree v = R.round.words.prescribedGraph.degree v :=
        congrArg (fun Q : SimpleGraph V => Q.degree v) hEq
      have hIncidence : incident i =
          (((sdiff (S i) (T i)) ⊔ R.round.words.prescribedGraph).neighborFinset v ∩ low).card :=
        congrArg (fun Q : SimpleGraph V => (((sdiff (S i) (T i)) ⊔ Q).neighborFinset v ∩ low).card) hEq
      rw [hDegrees,hIncidence,hSpecial,hInternal]
      exact hCost
    have hInternal := original_phase_internal_charge_bound low S T P U j (initial.card+1)
      (fun i => H.internal i v) (fun i hi => hClean i (hi.trans_le hj))
      (fun i hi => hP i (hi.trans_le hj)) (fun i hi => H.graph_next i (hi.trans_le hj))
      (fun k hk i hi => hNested k (hk.le.trans hj) i hi) (by
        intro i hi hCharge
        have him := hi.trans_le hj
        obtain ⟨_,R,hEq,_,_,hInt,_⟩ := H.selection i him
        rw [hInt] at hCharge
        obtain ⟨w,hw,_,hSmall,hOne,_⟩ := hCharge
        let current := H.exceptional i ∩
          univ.filter (fun x => 0 < H.degree i x-(sdiff (H.graph i) (H.cleaned i)).degree x)
        have hs : current.card ≤ initial.card := card_le_card (inter_subset_left.trans (hU i him.le))
        have hSmall' : (T i).degree w < current.card+2 := hSmall
        have hD : (P i).degree w = R.round.words.prescribedGraph.degree w :=
          congrArg (fun Q : SimpleGraph V => Q.degree w) hEq
        exact ⟨w,hw,Nat.lt_succ_iff.mp (hSmall'.trans_le (Nat.add_le_add_right hs 2)),(hD.trans hOne).ge⟩)
    have hTelescope (k : ℕ) (hk : k ≤ j) :
        G.degree v ≤ H.degree k v+2*(∑ i ∈ range k,incident i)+
          2*specialUseCount H.special k v+((range k).filter (fun i => H.internal i v)).card := by
      induction k with
      | zero => simp [H.degree_zero,specialUseCount]
      | succ k ih =>
        have hlt := Nat.lt_of_succ_le hk
        have hlm := hlt.trans_le hj
        have hOld := ih hlt.le
        have hCharge := hDebit k hlt
        have hBal := H.degree_next k hlm v
        change _+loss k v+(2-H.credit k v) = _ at hBal
        obtain ⟨_,R,hEq,hCredit,_,_,_⟩ := H.selection k hlm
        have hCreditP : (P k).degree v+H.credit k v = 2 := by
          change (H.prescribed k).degree v+H.credit k v = 2
          rw [hEq,hCredit]
          exact R.round.words.prescribed_degree_add_credit_on_exceptional _ (hU j hj hv)
        have hSpecial : specialUseCount H.special (k+1) v = specialUseCount H.special k v+
            (if H.special k = some v then 1 else 0) := by
          rw [specialUseCount,card_filter,sum_range_succ,specialUseCount,card_filter]
        have hCount : ((range (k+1)).filter (fun i => H.internal i v)).card =
            ((range k).filter (fun i => H.internal i v)).card+(if H.internal k v then 1 else 0) := by
          rw [card_filter,sum_range_succ,card_filter]
        rw [sum_range_succ,hSpecial,hCount]
        by_cases hSp : H.special k = some v <;> by_cases hInt : H.internal k v <;>
          simp only [hSp,hInt,if_true,if_false] at hCharge ⊢ <;> omega
    have hInc : (∑ i ∈ range j,incident i) ≤ low.card :=
      virtual_incident_deletions_into_le S T P j low v
        (fun i hi => hClean i (hi.trans_le hj)) (fun i hi => hP i (hi.trans_le hj))
        (fun i hi => H.graph_next i (hi.trans_le hj))
    have hAll := hTelescope j le_rfl
    omega
  intro j hj u v he
  have hOrigin : S j ≤ G := (hDecrease 0 j (Nat.zero_le _) hj).trans H.graph_zero.le
  have heG := hOrigin he
  have hWeak := hVAL u v heG
  have hu := ((S j).degree_pos_iff_exists_adj u).mpr ⟨v,he⟩
  have hv := ((S j).degree_pos_iff_exists_adj v).mpr ⟨u,he.symm⟩
  by_cases huU : u ∈ U j
  swap
  · have h := hOrdinary j hj u huU hu
    have hm := le_max_left (threshold+low.card) (4*low.card+2*(initial.card+1))
    omega
  by_cases hvU : v ∈ U j
  swap
  · have h := hOrdinary j hj v hvU hv
    have hm := le_max_left (threshold+low.card) (4*low.card+2*(initial.card+1))
    omega
  have hNoSpecial (x : V) (hxL : x ∈ low) (hxU : x ∈ U j) (hxPos : 0 < (S j).degree x) :
      ∀ y,specialUseCount H.special j y = 0 := by
    intro y
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hr,hs⟩ := mem_filter.mp hi
    have hlt := mem_range.mp hr
    have him := hlt.trans_le hj
    obtain ⟨_,R,_,_,hSpecial,_,_⟩ := H.selection i him
    have hxT : 0 < (T i).degree x :=
      hxPos.trans_le (degree_le_of_le ((hDecrease (i+1) j (Nat.succ_le_of_lt hlt) hj).trans
        (hNext i him)) (v := x))
    have hActive : (originalCleanActive low (U i) (T i)).Nonempty :=
      ⟨x,mem_filter.mpr ⟨mem_inter.mpr ⟨hNested j hj i hlt.le hxU,hxL⟩,hxT⟩⟩
    rw [hSpecial,R.special_only_when_empty hActive] at hs
    cases hs
  have hMax := le_max_right (threshold+low.card) (4*low.card+2*(initial.card+1))
  by_cases huLow : u ∈ low
  · have hvLow : v ∉ low := fun h => hInd huLow h heG.ne heG
    have hU := hBasic j hj u
    have hL := hLoss j hj u
    have hV := hNonlow j hj v hvU hvLow hv
    rw [hNoSpecial u huLow huU hu v] at hV
    omega
  by_cases hvLow : v ∈ low
  · have hV := hBasic j hj v
    have hL := hLoss j hj v
    have hU := hNonlow j hj u huU huLow hu
    rw [hNoSpecial v hvLow hvU hv u] at hU
    omega
  have hU := hNonlow j hj u huU huLow hu
  have hV := hNonlow j hj v hvU hvLow hv
  have hCharge := two_special_use_counts_le_rounds H.special j he.ne
  omega

/-- The degree-sum test on the virtual graph, with an explicit loss
budget. The saved ordinary incidences are counted by the record. -/
def VirtualTrimmingState.HasWeakDegreeSum (S : VirtualTrimmingState V)
    (initial : Finset V) (j d budget : ℕ) : Prop :=
  ∀ u v,S.graph.Adj u v → d ≤ S.record initial j u+S.record initial j v+budget

theorem VirtualTrimmingState.HasWeakDegreeSum.mono
    {S : VirtualTrimmingState V} {initial : Finset V} {j d budget bound : ℕ}
    (h : S.HasWeakDegreeSum initial j d budget) (hle : budget ≤ bound) :
    S.HasWeakDegreeSum initial j d bound := by
  intro u v he
  exact (h u v he).trans (Nat.add_le_add_left hle _)

theorem VirtualTrimmingState.HasWeakDegreeSum.after_cleanup
    {S : VirtualTrimmingState V} {initial W : Finset V} {j d budget loss : ℕ}
    (h : S.HasWeakDegreeSum initial j d budget) {T : SimpleGraph V}
    (hClean : DeletionRun W S.graph T)
    (hLoss : ∀ v,(sdiff S.graph T).degree v ≤ loss) :
    (⟨T,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).HasWeakDegreeSum
      initial j d (budget+2*loss) := by
  intro u v he
  have hLe := DeletionRun.le_source hClean
  have hBefore := h u v (hLe he)
  have hAfter (x : V) : (⟨T,S.prescribed,S.credit,S.used⟩ : VirtualTrimmingState V).record initial j x =
      S.record initial j x-(sdiff S.graph T).degree x :=
    auxiliary_physical_degree_after_cleanup S.graph T initial S.prescribed S.credit j hLe x
  rw [hAfter u,hAfter v]
  have hu := hLoss u
  have hv := hLoss v
  omega

theorem InheritedPairHistory.weak_degree_sum_prefix
    {start : VirtualTrimmingState V} {initial current active support : Finset V}
    {D floor loss threshold test j cap total m : ℕ}
    (H : InheritedPairHistory start initial current active support D floor loss threshold test j cap total m)
    (hInitial : current ⊆ initial) (hPair : active.card = 2) (hCore : initialᶜ ⊆ support)
    {budget : ℕ} (hEntry : start.HasWeakDegreeSum initial j D budget) :
    ∀ i ≤ m,(H.states i).HasWeakDegreeSum initial (j+i) (D-2*i) (budget+2*(loss+5)) := by
  intro i hi
  let K : InheritedPairHistory start initial current active support D floor loss threshold test j cap total i :=
    ⟨H.states,H.starts,fun k hk => H.rounds k (hk.trans_le hi),fun k hk => H.positions k (hk.trans hi),
      fun k hk => H.exceptional k (hk.trans_le hi)⟩
  intro u v he
  simpa only [K,Nat.add_assoc] using
    K.weak_degree_sum hInitial hPair budget hEntry u v he (fun x hx => hCore (mem_compl.mpr hx))

theorem InheritedSingletonHistory.weak_degree_sum_prefix
    {start : VirtualTrimmingState V} {initial current support : Finset V} {w : V}
    {D floor loss threshold test j cap m : ℕ}
    (H : InheritedSingletonHistory start initial current support w D floor loss threshold test j cap m)
    (hInitial : current ⊆ initial) (hw : w ∈ current) (hCore : initialᶜ ⊆ support)
    {budget : ℕ} (hEntry : start.HasWeakDegreeSum initial j D budget) :
    ∀ i ≤ m,(H.states i).HasWeakDegreeSum initial (j+i) (D-2*i) (budget+2*(loss+current.card+4)) := by
  intro i hi
  let K : InheritedSingletonHistory start initial current support w D floor loss threshold test j cap i :=
    ⟨H.states,H.starts,fun k hk => H.rounds k (hk.trans_le hi),fun k hk => H.positions k (hk.trans hi),
      fun k hk => H.exceptional k (hk.trans_le hi),fun k hk => H.active_drop k (hk.trans_le hi)⟩
  intro u v he
  simpa only [K,Nat.add_assoc] using K.weak_degree_sum hInitial hw hCore budget hEntry u v he

set_option maxHeartbeats 1600000 in
/-- A neutral transition spends no degree at either exceptional
endpoint. An ordinary endpoint pays at most the residual deficit. -/
theorem CriticalReselectionRound.weak_degree_sum
    {S T : VirtualTrimmingState V} {initial current support : Finset V}
    {d floor loss threshold test j cap k budget : ℕ}
    (hRound : CriticalReselectionRound S T initial current support d floor threshold test j cap k)
    (hPos : CriticalReselectionPosition T initial current support (d-2*k) floor loss (j+k) cap)
    (hEntry : S.HasWeakDegreeSum initial j d budget) :
    T.HasWeakDegreeSum initial (j+k) (d-2*k) (budget+2) := by
  rcases hRound with ⟨rfl,rfl⟩ | ⟨rfl,⟨_,R,hT⟩,_,hKeep⟩
  · exact hEntry.mono (Nat.le_add_right _ _)
  have hOrd (x : V) (hx : x ∉ current) (hPositive : 0 < T.graph.degree x) :
      d-2 ≤ T.record initial (j+1) x+2 := by
    have hs : x ∈ support := by
      by_cases hI : x ∈ initial
      · rw [←hPos.support_eq]
        exact mem_filter.mpr ⟨mem_univ _,by
          simpa only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hI] using hPositive⟩
      · exact hPos.core_support (mem_compl.mpr hI)
    have h := single_le_sum (f := fun z => d-2-T.record initial (j+1) z)
      (fun _ _ => Nat.zero_le _) (mem_sdiff.mpr ⟨hs,hx⟩)
    have hMass : (∑ z ∈ sdiff support current,(d-2-T.record initial (j+1) z)) ≤ 2 := by
      simpa only [Nat.mul_one] using hPos.ordinary_deficit
    omega
  have hLe : T.graph ≤ S.graph := by rw [hT]; exact sdiff_le
  intro u v he
  by_cases hu : u ∈ current
  · by_cases hv : v ∈ current
    · have h := hEntry u v (hLe he)
      rw [Nat.mul_one,hKeep u hu,hKeep v hv]
      omega
    · have h := hOrd v hv ((T.graph.degree_pos_iff_exists_adj v).mpr ⟨u,he.symm⟩)
      rw [Nat.mul_one]
      omega
  · have h := hOrd u hu ((T.graph.degree_pos_iff_exists_adj u).mpr ⟨v,he⟩)
    rw [Nat.mul_one]
    omega

end OverfullWork.CMSTrimmingRound
