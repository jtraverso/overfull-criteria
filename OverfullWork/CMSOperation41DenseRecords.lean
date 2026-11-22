module

public import OverfullWork.CMSOperation41WeakPrefixes

@[expose] public section


/-! Degree and parity certificates for the two stopping limits of Operation 4.1. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Degree data needed at a dense stopping graph. The exceptional
survivors are kept within the positive support. -/
def HasDenseRoundLimitRecord (degree : V → ℕ) (d width : ℕ) : Prop :=
  let active := univ.filter (fun v => 0 < degree v)
  ∃ W ⊆ active,
    (∀ w ∈ W,degree w < d) ∧
    (W.card ≤ 1 ∨ (Even active.card ∧ W.card ≤ 2)) ∧
    ∀ v ∈ active,v ∉ W → d ≤ degree v+width

set_option maxHeartbeats 2800000 in
/-- CMS Case 1.1. At the original long limit at most one low vertex
survives, and every other positive degree has an explicit floor. -/
theorem OriginalTrimmingHistory.dense_record_at_long_limit
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial low : Finset V} {threshold cap test : ℕ}
    (limit : ℝ) (H : OriginalTrimmingHistory G initial low threshold ⌊limit⌋₊ cap test ⌊limit⌋₊)
    (hLow : low ⊆ initial) (hInd : G.IsIndepSet (low : Set V)) (hPositive : 0 < ⌊limit⌋₊)
    (hThreshold : 1 ≤ threshold) (hStart : ∀ v ∈ low,(G.degree v:ℝ) < limit)
    (hOrd : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+threshold)
    (hFloor : ∀ v ∈ initial,v ∉ low → ⌊limit⌋₊ ≤ G.degree v)
    (hMargin : 5*initial.card+cap+4+(4*initial.card+2) ≤ ⌊limit⌋₊)
    (hRange : ⌊limit⌋₊+threshold+low.card ≤ G.maxDegree-2*⌊limit⌋₊) :
    HasDenseRoundLimitRecord (H.degree ⌊limit⌋₊) (G.maxDegree-2*⌊limit⌋₊)
      (G.maxDegree-2*⌊limit⌋₊-⌊limit⌋₊+2*low.card+initial.card+1) := by
  let m := ⌊limit⌋₊
  let d := G.maxDegree-2*m
  let W := H.exceptional m ∩ low
  let loss (i : ℕ) (v : V) := (sdiff (H.graph i) (H.cleaned i)).degree v
  have hLe (i : ℕ) (hi : i < m) : H.cleaned i ≤ H.graph i := DeletionRun.le_source (H.cleanup i hi)
  have hNext (i : ℕ) (hi : i < m) : H.graph (i+1) ≤ H.cleaned i := by
    rw [H.graph_next i hi]
    exact sdiff_le
  have hSub : H.graph m ≤ G := (virtual_trimming_prefix_le H.graph H.cleaned H.prescribed m
    hLe H.graph_next 0 m (Nat.zero_le _) le_rfl).trans H.graph_zero.le
  have hSum (v : V) : (∑ i ∈ range m,loss i v) ≤ low.card := by
    rw [←Fin.sum_univ_eq_sum_range (fun i => loss i v) m]
    exact cumulative_cleanup_degree_le_original_low_card G low H.graph H.cleaned
      (fun i => H.exceptional i ∩ low) m H.graph_zero hInd H.cleanup
      (fun _ _ => Or.inl inter_subset_right) hNext m le_rfl v
  have hSpent (j : ℕ) (hj : j ≤ m) (v : V) :
      G.degree v ≤ H.degree j v+2*j+(∑ i ∈ range j,loss i v) := by
    induction j with
    | zero => simp [H.degree_zero]
    | succ j ih =>
      have hlt := Nat.lt_of_succ_le hj
      have hPrev := ih hlt.le
      have hStep := H.degree_next j hlt v
      change _+loss j v+_ = _ at hStep
      rw [sum_range_succ]
      omega
  have hRaw := H.next_round_reserves hLow hInd hOrd hFloor hMargin hRange
  have hN := H.low_survivors_at_long_limit limit hLow hPositive hStart
  change m+threshold+low.card ≤ d at hRange
  refine ⟨W,?_,?_,Or.inl hN,?_⟩
  · intro v hv
    have hvE := (mem_inter.mp hv).1
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hPositive.ne'
    rw [show m = j+1 from hj,H.exceptional_next j (by omega)] at hvE
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [congrArg (fun i => H.degree i v) (show m = j+1 from hj)]
    exact (mem_filter.mp (mem_inter.mp (mem_filter.mp hvE).1).2).2
  · intro w hw
    have hwl := (mem_inter.mp hw).2
    have hD : H.degree m w = (H.graph m).degree w := by
      rw [H.degree_exact m le_rfl,auxiliaryPhysicalDegree,if_pos (hLow hwl)]
    have hG : G.degree w ≤ m := Nat.le_floor (hStart w hwl).le
    have hW := (degree_le_of_le hSub (v := w)).trans hG
    change H.degree m w < d
    rw [hD]
    exact hW.trans_lt (by omega)
  · intro v hv hw
    have hPos : 0 < H.degree m v := (mem_filter.mp hv).2
    change d ≤ H.degree m v+(d-m+2*low.card+initial.card+1)
    by_cases hvI : v ∈ initial
    · have hEq : H.degree m v = (H.graph m).degree v := by
        rw [H.degree_exact m le_rfl,auxiliaryPhysicalDegree,if_pos hvI]
      have hG := (hRaw.2 v hvI hw (hEq ▸ hPos)).2
      change m ≤ (H.graph m).degree v+2*low.card+initial.card+1 at hG
      rw [←hEq] at hG
      omega
    · have hG := hOrd v hvI
      have hT := hSpent m le_rfl v
      have hL := hSum v
      dsimp only [d]
      omega

theorem HasDenseRoundLimitRecord.mono {degree : V → ℕ} {d width width' : ℕ}
    (h : HasDenseRoundLimitRecord degree d width) (hWidth : width ≤ width') :
    HasDenseRoundLimitRecord degree d width' := by
  obtain ⟨W,hSupport,hLow,hParity,hFloor⟩ := h
  exact ⟨W,hSupport,hLow,hParity,fun v hv hW =>
    (hFloor v hv hW).trans (Nat.add_le_add_left hWidth _)⟩

/-- Either the stopping limit supplies a dense degree certificate,
or the degree record supplies an almost-overfull set. -/
def HasRoundLimitProfile (degree : V → ℕ) (d test width : ℕ) (atLimit : Prop) : Prop :=
  (atLimit ∧ HasDenseRoundLimitRecord degree d width) ∨
    HasAlmostOverfullRecord (univ.filter (fun v => 0 < degree v)) d test degree

theorem HasRoundLimitProfile.stop {degree : V → ℕ} {d test width : ℕ} {atLimit : Prop}
    (h : HasRoundLimitProfile degree d test width atLimit) :
    atLimit ∨ HasAlmostOverfullRecord (univ.filter (fun v => 0 < degree v)) d test degree :=
  h.imp_left And.left

theorem HasRoundLimitProfile.mono {degree : V → ℕ} {d test width width' : ℕ} {atLimit : Prop}
    (h : HasRoundLimitProfile degree d test width atLimit) (hWidth : width ≤ width') :
    HasRoundLimitProfile degree d test width' atLimit :=
  h.imp_left (fun ⟨hLimit,hDense⟩ => ⟨hLimit,hDense.mono hWidth⟩)

private theorem ordinary_record_floor {support current : Finset V} {degree : V → ℕ} {d : ℕ}
    (hDeficit : (∑ v ∈ support \ current,(d-degree v)) ≤ 1)
    {v : V} (hv : v ∈ support) (hCurrent : v ∉ current) :
    d ≤ degree v+1 := by
  have h := single_le_sum (f := fun u => d-degree u) (fun _ _ => Nat.zero_le _)
    (mem_sdiff.mpr ⟨hv,hCurrent⟩)
  omega

/-- An immediate stop at the first critical choice has no degree
exception outside the uniform loss bound. -/
theorem CriticalTrimmingEntry.dense_record
    {T : SimpleGraph V} [DecidableRel T.Adj] {initial current active : Finset V}
    {degree : V → ℕ} {d floor loss : ℕ}
    (E : CriticalTrimmingEntry T initial current active degree d floor loss) :
    HasDenseRoundLimitRecord degree d (d-floor+loss+1) := by
  refine ⟨∅,empty_subset _,by simp,Or.inl (by simp),?_⟩
  intro v hv _
  by_cases hc : v ∈ current
  · have hExact := E.degree_exact v (E.current_initial hc)
    have hPositive : 0 < T.degree v := by
      rw [←hExact]
      exact (mem_filter.mp hv).2
    have hFloor := E.degree_floor v (E.current_initial hc) hPositive
    omega
  · have hFloor := ordinary_record_floor E.ordinary_deficit hv hc
    omega

/-- The inherited pair can account for two low vertices because
its positive support is even and remains fixed. -/
theorem InheritedPairPosition.dense_record
    {origin : SimpleGraph V} {initial current active support : Finset V}
    {S : VirtualTrimmingState V} {d floor loss j left cap : ℕ}
    (P : InheritedPairPosition origin initial current active support S d floor loss j left cap)
    (hCurrent : current ⊆ initial) (hPair : active.card = 2)
    (hEven : Even support.card) (hWindow : floor+2 ≤ d) :
    HasDenseRoundLimitRecord (S.record initial j) d (d-floor+loss+4) := by
  let W := active ∩ current ∩ support
  unfold HasDenseRoundLimitRecord
  rw [P.support_eq]
  have hCard : W.card ≤ 2 := by
    rw [←hPair]
    exact card_le_card (inter_subset_left.trans inter_subset_left)
  refine ⟨W,inter_subset_right,?_,Or.inr ⟨hEven,hCard⟩,?_⟩
  · intro v hv
    exact (P.exceptional_upper v (mem_inter.mp (mem_inter.mp hv).1).2).trans_le hWindow
  · intro v hv hW
    by_cases hc : v ∈ current
    · have ha : v ∉ active := fun h => hW (mem_inter.mpr ⟨mem_inter.mpr ⟨h,hc⟩,hv⟩)
      have h := P.inactive_balance v hc ha
      have hCount := card_le_card (inter_subset_right :
        origin.neighborFinset v ∩ active ⊆ active)
      have hExact : S.record initial j v = S.graph.degree v := by
        simp only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos (hCurrent hc)]
      omega
    · have h := ordinary_record_floor P.ordinary_deficit hv hc
      omega

/-- At the singleton limit the active vertex may have become
isolated. Its contribution is restricted to the actual support. -/
theorem InheritedSingletonPosition.dense_record
    {origin : SimpleGraph V} {initial current support : Finset V} {w : V}
    {S : VirtualTrimmingState V} {d floor loss j cap : ℕ}
    (P : InheritedSingletonPosition origin initial current support w S d floor loss j cap)
    (hCurrent : current ⊆ initial) (hw : w ∈ current) (hWindow : floor+2 ≤ d) :
    HasDenseRoundLimitRecord (S.record initial j) d (d-floor+loss+current.card+3) := by
  let alive := univ.filter (fun v => 0 < S.record initial j v)
  let W := {w} ∩ alive
  have hCard : W.card ≤ 1 := (card_le_card (inter_subset_left : W ⊆ {w})).trans (by simp)
  refine ⟨W,inter_subset_right,?_,Or.inl hCard,?_⟩
  · intro v hv
    have he : v = w := mem_singleton.mp (mem_inter.mp hv).1
    subst v
    exact (P.exceptional_upper w hw).trans_le hWindow
  · intro v hv hW
    have he : v ≠ w := fun he => hW (mem_inter.mpr ⟨mem_singleton.mpr he,hv⟩)
    by_cases hc : v ∈ current
    · have h := P.inactive_floor v hc he
      have hExact : S.record initial j v = S.graph.degree v := by
        simp only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos (hCurrent hc)]
      omega
    · have hMem : v ∈ alive.erase w := mem_erase.mpr ⟨he,hv⟩
      rw [show alive.erase w = support.erase w from P.support_except] at hMem
      have h := ordinary_record_floor P.ordinary_deficit (mem_erase.mp hMem).2 hc
      omega

end OverfullWork.CMSTrimmingRound
