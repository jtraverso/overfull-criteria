module

public import OverfullWork.CMSOperation41InheritedSingleton

@[expose] public section


/-! Normalize the exhausted singleton, spend at most one ordinary
round, and restart with a pair using the same history. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

structure CriticalReselectionPosition (S : VirtualTrimmingState V)
    (initial current support : Finset V) (d floor loss j cap : ℕ) : Prop where
  current_initial : current ⊆ initial
  current_support : current ⊆ support
  core_support : initialᶜ ⊆ support
  support_eq : univ.filter (fun v => 0 < S.record initial j v) = support
  support_even : Even support.card
  ordinary_odd : Odd (support \ current).card
  ordinary_deficit : (∑ v ∈ support \ current,(d-S.record initial j v)) ≤ 2
  degree_cap : ∀ v,S.record initial j v ≤ d
  exceptional_upper : ∀ v ∈ current,S.record initial j v < floor+2
  degree_floor : ∀ v ∈ initial,0 < S.graph.degree v → floor ≤ S.graph.degree v+loss
  free_size : ∀ i < j,(S.used i).card ≤ 2*(initial.card+1)
  free_load : ∀ v,projectionLoad (range j) S.used v ≤ cap

set_option maxHeartbeats 3200000 in
/-- The last-edge cleanup pays one degree unit and retains the prior
projection history. -/
theorem InheritedSingletonPosition.prepare_critical_reselection
    {origin : SimpleGraph V} {initial current support : Finset V} {w : V}
    {S : VirtualTrimmingState V} {d floor loss j cap : ℕ}
    (state : InheritedSingletonPosition origin initial current support w S d floor loss j cap)
    (hInitial : current ⊆ initial) (hCurrent : current ⊆ support)
    (hCore : initialᶜ ⊆ support) (hw : w ∈ current)
    (hOdd : Odd support.card) (hOrdinary : Odd (support \ current).card)
    (hTarget : floor+3 ≤ d) (hFloor : loss+current.card+5 ≤ floor)
    (hStop : S.graph.degree w ≤ 1) :
    ∃ T : SimpleGraph V,
      DeletionRun {w} S.graph T ∧
      (∀ v,(sdiff S.graph T).degree v ≤ 1 ∧
        auxiliaryPhysicalDegree T initial S.prescribed S.credit j v+
          (sdiff S.graph T).degree v = S.record initial j v) ∧
      CriticalReselectionPosition ⟨T,S.prescribed,S.credit,S.used⟩
        initial (current.erase w) (support.erase w) d floor (loss+current.card+4) j cap := by
  obtain ⟨T,hRun,hCleanup,hSupport,_,hEven,hCut,hMass⟩ :=
    state.cleanup_at_exhaustion hInitial hCurrent hCore hw hOdd (by omega) hFloor hStop
  let Q : VirtualTrimmingState V := ⟨T,S.prescribed,S.credit,S.used⟩
  let alive := univ.filter (fun v => 0 < Q.record initial j v)
  have hLe := DeletionRun.le_source hRun
  change alive = support.erase w at hSupport
  have hMass' : (∑ v ∈ support.erase w \ current.erase w,(d-Q.record initial j v)) ≤ 2 := by
    rw [←hSupport]
    exact hMass
  refine ⟨T,hRun,hCleanup,⟨?_,?_,?_,hSupport,?_,?_,hMass',?_,?_,?_,state.free_size,state.free_load⟩⟩
  · exact (erase_subset _ _).trans hInitial
  · intro v hv
    obtain ⟨hn,hm⟩ := mem_erase.mp hv
    exact mem_erase.mpr ⟨hn,hCurrent hm⟩
  · intro v hv
    refine mem_erase.mpr ⟨?_,hCore hv⟩
    intro h
    subst v
    exact (mem_compl.mp hv) (hInitial hw)
  · rw [←hSupport]
    exact hEven
  · rw [←hSupport]
    exact hCut ▸ hOrdinary
  · intro v
    have h := (hCleanup v).2
    change Q.record initial j v+(sdiff S.graph T).degree v = S.record initial j v at h
    change Q.record initial j v ≤ d
    exact (Nat.le.intro h).trans (state.degree_bound v)
  · intro v hv
    have h := (hCleanup v).2
    change Q.record initial j v+(sdiff S.graph T).degree v = S.record initial j v at h
    change Q.record initial j v < floor+2
    exact (Nat.le.intro h).trans_lt (state.exceptional_upper v (mem_erase.mp hv).2)
  · intro v hv hp
    by_cases h : v ∈ current.erase w
    · have hBefore := state.inactive_floor v (mem_erase.mp h).2 (mem_erase.mp h).1
      have hAfter : T.degree v+(sdiff S.graph T).degree v = S.graph.degree v := by
        simpa only [add_comm,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
          MaximumMatching.degree_sdiff_add_of_le S.graph T hLe v
      have hl := (hCleanup v).1
      change floor ≤ T.degree v+(loss+current.card+4)
      omega
    · have hRead : Q.record initial j v = T.degree v := by
        simp only [Q,VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hv]
      have hLive : v ∈ support.erase w := hSupport ▸ mem_filter.mpr ⟨mem_univ _,hRead.symm ▸ hp⟩
      have hDef := single_le_sum (f := fun u => d-Q.record initial j u)
        (fun _ _ => Nat.zero_le _) (mem_sdiff.mpr ⟨hLive,h⟩)
      rw [hRead] at hDef
      change floor ≤ T.degree v+(loss+current.card+4)
      omega

/-- Selecting the two smallest surviving exceptional degrees produces
the entry record expected by the fixed-pair iterator. -/
theorem CriticalReselectionPosition.pair_entry
    {S : VirtualTrimmingState V} {initial current support : Finset V}
    {d floor loss j cap : ℕ}
    (state : CriticalReselectionPosition S initial current support d floor loss j cap)
    (hD : 3 ≤ d) (hMass : (∑ v ∈ support \ current,(d-S.record initial j v)) ≤ 1)
    {a b : V} (ha : a ∈ current) (hb : b ∈ current) (hne : a ≠ b)
    (hMin : ∀ v ∈ current,S.record initial j a ≤ S.record initial j v)
    (hSecond : ∀ v ∈ current,v ≠ a → S.record initial j b ≤ S.record initial j v) :
    CriticalTrimmingEntry S.graph initial current {a,b} (S.record initial j) d floor loss := by
  have hSize : ({a,b} : Finset V).card = 2 := card_pair hne
  have hOdd : Odd current.card := by
    apply Nat.not_even_iff_odd.mp
    intro he
    obtain ⟨r,hr⟩ := he
    obtain ⟨s,hs⟩ := state.support_even
    obtain ⟨t,ht⟩ := state.ordinary_odd
    have hCut := card_sdiff_add_card_eq_card state.current_support
    omega
  refine ⟨state.current_initial,?_,insert_subset_iff.mpr ⟨ha,singleton_subset_iff.mpr hb⟩,
    Or.inr hSize,?_,Or.inr ⟨hOdd,a,ha,b,hb,hne,rfl,hMin,hSecond⟩,state.exceptional_upper,
    ?_,?_,state.degree_cap,?_,?_,state.degree_floor⟩
  · intro v hv
    have h : v ∈ univ.filter (fun v => 0 < S.record initial j v) := by
      rw [state.support_eq]
      exact state.current_support hv
    exact (mem_filter.mp h).2
  · rw [state.support_eq,hSize]
    exact iff_of_true state.support_even rfl
  · rw [state.support_eq]
    exact state.ordinary_odd
  · rw [state.support_eq]
    exact hMass
  · intro v hv
    simp only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hv]
  · intro v hv
    have h := single_le_sum (f := fun u => d-S.record initial j u)
      (fun _ _ => Nat.zero_le _) (mem_sdiff.mpr ⟨state.core_support (mem_compl.mpr hv),
        fun h => hv (state.current_initial h)⟩)
    omega

def HasReselectedPairOrStop (S : VirtualTrimmingState V) (initial current support : Finset V)
    (d floor loss j test : ℕ) : Prop :=
  HasAlmostOverfullRecord support d test (S.record initial j) ∨
    ∃ A,A.card = 2 ∧ CriticalTrimmingEntry S.graph initial current A (S.record initial j) d floor loss

def CriticalReselectionRound (S T : VirtualTrimmingState V) (initial current support : Finset V)
    (d floor threshold test j cap k : ℕ) : Prop :=
  (k = 0 ∧ T = S) ∨
    (k = 1 ∧ HasTrimmingRoundWithoutCleanup S T initial current ∅ support d floor test j cap ∧
      nextTrimmingExceptional current support (T.record initial (j+1)) (d-2) threshold = current ∧
      (∀ v ∈ current,T.record initial (j+1) v = S.record initial j v))

set_option maxHeartbeats 4100000 in
/-- Build the restart directly in the existing virtual history. If
a neutral round is required it retains its exact prescription, the
same exceptional degrees, and the revised projection budget. -/
theorem CriticalReselectionPosition.select_pair_or_stop
    {S : VirtualTrimmingState V} {initial current support : Finset V}
    {d floor loss j cap : ℕ}
    (state : CriticalReselectionPosition S initial current support d floor loss j cap)
    (threshold test : ℕ) (hThreshold : 2 ≤ threshold) (hTest : 1 ≤ test)
    (hCap : 0 < cap) (hSize : 4 ≤ initialᶜ.card) (hRate : j*(2*(initial.card+1)) ≤ cap*cap)
    (hWindow : floor+1+threshold ≤ d-2)
    (hMargin : 5*initial.card+cap+4+loss ≤ floor) :
    ∃ k ≤ 1,∃ T : VirtualTrimmingState V,
      CriticalReselectionRound S T initial current support d floor threshold test j cap k ∧
      CriticalReselectionPosition T initial current support (d-2*k) floor loss (j+k) cap ∧
      HasReselectedPairOrStop T initial current support (d-2*k) floor loss (j+k) test := by
  let degree := S.record initial j
  let alive := univ.filter (fun v => 0 < degree v)
  have hSupport : alive = support := state.support_eq
  have hExact (v : V) (hv : v ∈ initial) : degree v = S.graph.degree v := by
    simp only [degree,VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hv]
  have hCore (v : V) (hv : v ∉ initial) : 2 ≤ degree v := by
    have h := single_le_sum (f := fun u => d-degree u) (fun _ _ => Nat.zero_le _)
      (mem_sdiff.mpr ⟨state.core_support (mem_compl.mpr hv),fun h => hv (state.current_initial h)⟩)
    have hMass : (∑ x ∈ support \ current,(d-degree x)) ≤ 2 := state.ordinary_deficit
    omega
  have hProj (v : V) (hv : v ∈ initial) (hp : 0 < S.graph.degree v) :
      5*initial.card+cap+4 ≤ S.graph.degree v := by
    have h := state.degree_floor v hv hp
    omega
  have hCur : current ⊆ alive := by rw [hSupport]; exact state.current_support
  have hEven : Even alive.card := by rw [hSupport]; exact state.support_even
  have hOdd : Odd (alive \ current).card := by rw [hSupport]; exact state.ordinary_odd
  have hMass : (∑ v ∈ alive \ current,(d-degree v)) ≤ 2 := by rw [hSupport]; exact state.ordinary_deficit
  have hD : 3 ≤ d := by omega
  rcases exists_critical_continuation_after_singleton S.graph initial current degree d floor threshold test
    S.used j cap cap (2*(initial.card+1)) hCap state.free_size hRate
    state.current_initial state.exceptional_upper hWindow hThreshold hExact hCore hProj
    hSize hD state.degree_cap hTest hCur hEven hOdd hMass with hResult | hRound
  · have hEnd : HasReselectedPairOrStop S initial current support d floor loss j test := by
      rcases hResult with hStop | ⟨hDeficit,a,ha,b,hb,hne,hMin,hSecond⟩
      · left
        change HasAlmostOverfullRecord alive d test degree at hStop
        rw [hSupport] at hStop
        exact hStop
      · change (∑ v ∈ alive \ current,(d-degree v)) ≤ 1 at hDeficit
        rw [hSupport] at hDeficit
        exact Or.inr ⟨{a,b},card_pair hne,state.pair_entry hD hDeficit ha hb hne hMin hSecond⟩
    refine ⟨0,by decide,S,Or.inl ⟨rfl,rfl⟩,?_⟩
    simpa only [Nat.mul_zero,Nat.sub_zero,Nat.add_zero] using And.intro state hEnd
  obtain ⟨R,hNo,hNext,hAlive,hKeep,hSame,hZero,hResult⟩ := hRound
  let T := S.advance j R.round.words.prescribedGraph (R.round.words.degreeCredit R.round.omitted) R.freeEndpoints
  let record := T.record initial (j+1)
  let intended (v : V) := degree v-(2-R.round.words.degreeCredit R.round.omitted v)
  have hRead : record = intended := by
    funext v
    have h0 := (R.advance_without_cleanup S.prescribed S.credit (fun _ => rfl) hCore).2 v
    have h : record v+(2-R.round.words.degreeCredit R.round.omitted v) = degree v := by
      simpa only [record,T,VirtualTrimmingState.record,VirtualTrimmingState.advance,Function.update_self] using h0.2
    change record v = degree v-(2-R.round.words.degreeCredit R.round.omitted v)
    omega
  have hNoStop : ¬HasAlmostOverfullRecord support d test degree := by
    rw [←hSupport]
    exact hNo
  have hAlive' : univ.filter (fun v => 0 < record v) = support := by
    rw [hRead,←hSupport]
    exact hAlive
  have hSame' (v : V) (hv : v ∈ current) : record v = degree v := by
    rw [hRead]
    exact hSame v hv
  have hDeficitZero : (∑ v ∈ support \ current,(d-2-record v)) = 0 := by
    rw [hRead,←hSupport]
    exact hZero
  have hKeep' : nextTrimmingExceptional current support record (d-2) threshold = current := by
    rw [hRead,←hSupport]
    exact hKeep
  obtain ⟨hFSize,hFPrior,hFLoad,_⟩ := R.append_free_projections state.free_load
  change R.freeEndpoints.card ≤ 2*(initial.card+1) at hFSize
  change ∀ i < j,T.used i = S.used i at hFPrior
  change ∀ v,projectionLoad (range (j+1)) T.used v ≤ cap at hFLoad
  have hFree (i : ℕ) (hi : i < j+1) : (T.used i).card ≤ 2*(initial.card+1) := by
    by_cases he : i = j
    · subst i
      simpa only [T,VirtualTrimmingState.advance,Function.update_self] using hFSize
    · rw [hFPrior i (by omega)]
      exact state.free_size i (by omega)
  have hPost : CriticalReselectionPosition T initial current support (d-2) floor loss (j+1) cap := by
    refine ⟨state.current_initial,state.current_support,state.core_support,hAlive',state.support_even,
      state.ordinary_odd,by change (∑ v ∈ support \ current,(d-2-record v)) ≤ 2; rw [hDeficitZero]; decide,
      ?_,?_,?_,hFree,hFLoad⟩
    · intro v
      change record v ≤ d-2
      rw [hRead]
      exact (hNext v).1
    · intro v hv
      change record v < floor+2
      rw [hSame' v hv]
      exact state.exceptional_upper v hv
    · intro v hv hp
      have hG : record v = T.graph.degree v := by
        simp only [record,VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hv]
      by_cases hc : v ∈ current
      · have hSameG : T.graph.degree v = S.graph.degree v :=
          hG.symm.trans ((hSame' v hc).trans (hExact v hv))
        rw [hSameG]
        exact state.degree_floor v hv (hSameG ▸ hp)
      · have hs : v ∈ support := hAlive' ▸ mem_filter.mpr ⟨mem_univ _,hG.symm ▸ hp⟩
        have h := single_le_sum (f := fun x => d-2-record x) (fun _ _ => Nat.zero_le _)
          (mem_sdiff.mpr ⟨hs,hc⟩)
        rw [hDeficitZero,hG] at h
        omega
  have hEnd : HasReselectedPairOrStop T initial current support (d-2) floor loss (j+1) test := by
    rcases hResult with hStop | ⟨_,a,ha,b,hb,hne,hMin,hSecond⟩
    · left
      change HasAlmostOverfullRecord support (d-2) test record
      rw [hRead,←hSupport]
      exact hStop
    · have hMin' : ∀ v ∈ current,record a ≤ record v := by rw [hRead]; exact hMin
      have hSecond' : ∀ v ∈ current,v ≠ a → record b ≤ record v := by rw [hRead]; exact hSecond
      have hMass' : (∑ v ∈ support \ current,(d-2-record v)) ≤ 1 := by rw [hDeficitZero]; decide
      have hD' : 3 ≤ d-2 := by omega
      exact Or.inr ⟨{a,b},card_pair hne,hPost.pair_entry hD' hMass' ha hb hne hMin' hSecond'⟩
  refine ⟨1,le_rfl,T,Or.inr ⟨rfl,⟨hNoStop,R,rfl⟩,hKeep',hSame'⟩,?_⟩
  simpa only [Nat.mul_one] using And.intro hPost hEnd

/-- The history that follows an exhausted singleton up to a terminal
record. A selected pair may have zero remaining rounds. -/
def HasShortTrimmingAfterExhaustion (S : VirtualTrimmingState V) (initial current support : Finset V)
    (w : V) (d floor loss threshold test j cap left : ℕ) : Prop :=
    let U := current.erase w
    let support' := support.erase w
    let loss' := loss+current.card+4
    S.graph.degree w < d ∧ ∃ T : SimpleGraph V,
      DeletionRun {w} S.graph T ∧
      (∀ v,(sdiff S.graph T).degree v ≤ 1 ∧
        auxiliaryPhysicalDegree T initial S.prescribed S.credit j v+
          (sdiff S.graph T).degree v = S.record initial j v) ∧
      ∃ k ≤ 1,∃ R : VirtualTrimmingState V,
        CriticalReselectionRound ⟨T,S.prescribed,S.credit,S.used⟩ R initial U support'
          d floor threshold test j cap k ∧
        CriticalReselectionPosition R initial U support' (d-2*k) floor loss' (j+k) cap ∧
        (HasAlmostOverfullRecord support' (d-2*k) test (R.record initial (j+k)) ∨
          ∃ A, A.card = 2 ∧ ∃ m ≤ left-k,
            ∃ H : InheritedPairHistory R initial U A support' (d-2*k) floor loss'
              threshold test (j+k) cap (left-k) m,
              m = left-k ∨ HasAlmostOverfullRecord support' (d-2*k-2*m)
                test ((H.states m).record initial ((j+k)+m)))

set_option maxHeartbeats 3500000 in
/-- Once the singleton is exhausted before the short limit, finish
the remaining short range. The only extra round before a new pair
is the neutral round that pays the ordinary deficit. -/
theorem InheritedSingletonPosition.continue_after_exhaustion
    {origin : SimpleGraph V} {initial current support : Finset V} {w : V}
    {S : VirtualTrimmingState V} {d floor loss j cap : ℕ}
    (state : InheritedSingletonPosition origin initial current support w S d floor loss j cap)
    (threshold test left : ℕ) (hLeft : 1 ≤ left)
    (hThreshold : 2 ≤ threshold) (hTest : 1 ≤ test)
    (hCap : 0 < cap) (hSize : 4 ≤ initialᶜ.card)
    (hRate : (j+left)*(2*(initial.card+1)) ≤ cap*cap)
    (hInitial : current ⊆ initial) (hCurrent : current ⊆ support)
    (hCore : initialᶜ ⊆ support) (hw : w ∈ current)
    (hOdd : Odd support.card) (hOrdinary : Odd (support \ current).card)
    (hWindow : floor+1+threshold ≤ d-2*left)
    (hRoom : 5*initial.card+cap+4+(loss+current.card+8) ≤ floor)
    (hPairRoom : left+6+(loss+current.card+4) ≤ floor)
    (hStop : S.graph.degree w ≤ 1) :
    HasShortTrimmingAfterExhaustion S initial current support w d floor loss threshold test j cap left := by
  unfold HasShortTrimmingAfterExhaustion
  intro U support' loss'
  have hLocal : floor+1+threshold ≤ d-2 := hWindow.trans
    (Nat.sub_le_sub_left (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hLeft) _)
  have hTarget : floor+3 ≤ d := by omega
  have hFloor : loss+current.card+5 ≤ floor := by omega
  have hProjection : 5*initial.card+cap+4+loss' ≤ floor := by dsimp only [loss']; omega
  have hRate' := (Nat.mul_le_mul_right (2*(initial.card+1)) (Nat.le_add_right j left)).trans hRate
  obtain ⟨T,hRun,hClean,hPosition⟩ :=
    state.prepare_critical_reselection hInitial hCurrent hCore hw hOdd hOrdinary hTarget hFloor hStop
  change CriticalReselectionPosition ⟨T,S.prescribed,S.credit,S.used⟩ initial U support'
    d floor loss' j cap at hPosition
  obtain ⟨k,hk,R,hReselection,hReady,hEnd⟩ :=
    hPosition.select_pair_or_stop threshold test hThreshold hTest hCap hSize hRate' hLocal hProjection
  refine ⟨by omega,T,hRun,hClean,k,hk,R,hReselection,hReady,?_⟩
  rcases hEnd with hEnd | ⟨A,hPair,E⟩
  · exact Or.inl hEnd
  right
  have hkL : k ≤ left := hk.trans hLeft
  have hSpan : k+(left-k) = left := Nat.add_sub_of_le hkL
  have hBand : floor+1+threshold ≤ d-2*k-2*(left-k) := by
    rw [Nat.sub_sub,←Nat.mul_add,hSpan]
    exact hWindow
  have hRatePair : (j+k+(left-k))*(2*(initial.card+1)) ≤ cap*cap := by
    rwa [Nat.add_assoc,hSpan]
  have hStartRoom : left-k+6+loss' ≤ floor := by
    dsimp only [loss']
    exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.sub_le left k) _) _).trans hPairRoom
  have hEntry := E.start_inherited_pair hStartRoom hReady.free_size hReady.free_load
  rw [hReady.support_eq] at hEntry
  have hMargin : 5*initial.card+cap+4+(loss'+4) ≤ floor := by dsimp only [loss']; omega
  obtain ⟨m,hm,H,hLast⟩ := exists_inherited_pair_trimming_history R initial U A support'
    (d-2*k) floor loss' threshold test (j+k) cap (left-k) hEntry
    hTest hCap hSize hRatePair hReady.current_initial hReady.current_support hReady.core_support
    E.active_current hPair hBand hMargin
  exact ⟨A,hPair,m,hm,H,hLast⟩

/-- The complete inherited phase keeps the actual histories on both
sides of a possible change of active set. -/
def HasCompletedShortTrimmingPhase (start : VirtualTrimmingState V)
    (initial current active : Finset V) (D floor loss threshold test j cap total : ℕ) : Prop :=
  let support := univ.filter (fun v => 0 < start.record initial j v)
  ∃ m ≤ total,
    (active.card = 2 ∧ ∃ H : InheritedPairHistory start initial current active support
      D floor loss threshold test j cap total m,
      m = total ∨ HasAlmostOverfullRecord support (D-2*m) test ((H.states m).record initial (j+m))) ∨
    (∃ w,active = {w} ∧ ∃ H : InheritedSingletonHistory start initial current support w
      D floor loss threshold test j cap m,
      m = total ∨
        HasAlmostOverfullRecord (univ.filter (fun v => 0 < (H.states m).record initial (j+m) v))
          (D-2*m) test ((H.states m).record initial (j+m)) ∨
        (m < total ∧ 0 < m ∧ HasShortTrimmingAfterExhaustion (H.states m) initial current support w
          (D-2*m) floor loss threshold test (j+m) cap (total-m)))

set_option maxHeartbeats 3500000 in
/-- Run from a critical entry all the way to the short limit or an
almost-overfull record, including the restart if a singleton runs
out of edges first. -/
theorem CriticalTrimmingEntry.complete_short_phase
    {start : VirtualTrimmingState V} {initial current active : Finset V}
    {D floor loss j cap : ℕ}
    (E : CriticalTrimmingEntry start.graph initial current active (start.record initial j) D floor loss)
    (threshold test total : ℕ) (hThreshold : 2 ≤ threshold)
    (hTest : 1 ≤ test) (hCap : 0 < cap) (hSize : 4 ≤ initialᶜ.card)
    (hRate : (j+total)*(2*(initial.card+1)) ≤ cap*cap)
    (hRoom : 5*initial.card+cap+4+(loss+current.card+8) ≤ floor)
    (hPairRoom : total+6+(loss+current.card+4) ≤ floor)
    (hWindow : floor+1+threshold ≤ D-2*total)
    (hSize₀ : ∀ i < j,(start.used i).card ≤ 2*(initial.card+1))
    (hLoad₀ : ∀ v,projectionLoad (range j) start.used v ≤ cap) :
    HasCompletedShortTrimmingPhase start initial current active D floor loss threshold test j cap total := by
  let support := univ.filter (fun v => 0 < start.record initial j v)
  have hEntry : total+6+loss ≤ floor := by omega
  have hRoom' : 5*initial.card+cap+4+(loss+current.card+4) ≤ floor := by omega
  obtain ⟨m,hm,hRun⟩ := E.exists_inherited_run threshold test total hTest hCap hSize
    hRate hEntry hWindow hRoom' hSize₀ hLoad₀
  refine ⟨m,hm,?_⟩
  rcases hRun with ⟨w,hW,H,hExit⟩ | hPair
  · right
    refine ⟨w,hW,H,?_⟩
    rcases hExit with hLimit | hSmall | hStop
    · exact Or.inl hLimit
    · by_cases he : m = total
      · exact Or.inl he
      have hlt : m < total := lt_of_le_of_ne hm he
      have hw : w ∈ current := E.active_current (hW.symm ▸ mem_singleton_self w)
      have hPos : 0 < m := by
        by_contra! hZero
        have hm0 : m = 0 := Nat.eq_zero_of_le_zero hZero
        subst m
        rw [H.starts] at hSmall
        have hExact := E.degree_exact w (E.current_initial hw)
        have hPositive := E.current_positive w hw
        rw [hExact] at hPositive
        have hFloor := E.degree_floor w (E.current_initial hw) hPositive
        omega
      refine Or.inr (Or.inr ⟨hlt,hPos,?_⟩)
      have hCurrent : current ⊆ support := fun v hv =>
        mem_filter.mpr ⟨mem_univ _,E.current_positive v hv⟩
      have hCore : initialᶜ ⊆ support := by
        intro v hv
        have h := E.core_room v (mem_compl.mp hv)
        exact mem_filter.mpr ⟨mem_univ _,by omega⟩
      have hOdd : Odd support.card := by
        apply Nat.not_even_iff_odd.mp
        intro h
        have hh := E.active_parity.mp h
        rw [hW,card_singleton] at hh
        cases hh
      have hr : (j+m+(total-m))*(2*(initial.card+1)) ≤ cap*cap := by
        rwa [Nat.add_assoc,Nat.add_sub_of_le hm]
      have hBand : floor+1+threshold ≤ D-2*m-2*(total-m) := by
        rwa [Nat.sub_sub,←Nat.mul_add,Nat.add_sub_of_le hm]
      have hPair : total-m+6+(loss+current.card+4) ≤ floor :=
        (Nat.add_le_add_right (Nat.add_le_add_right (Nat.sub_le total m) _) _).trans hPairRoom
      exact (H.positions m le_rfl).continue_after_exhaustion threshold test (total-m) (by omega)
        hThreshold hTest hCap hSize hr E.current_initial hCurrent hCore hw hOdd E.ordinary_odd
        hBand hRoom hPair hSmall
    · exact Or.inr (Or.inl hStop)
  · exact Or.inl hPair

set_option maxHeartbeats 3500000 in
/-- Start at the original graph and construct the original prefix and,
when it starts below the short limit, the full inherited phase. -/
theorem cms_operation_4_1_original_and_short_phases
    (G : SimpleGraph V) [DecidableRel G.Adj] (η : ℝ) (hη : 0 ≤ η) (hSmall : η ≤ 1/64)
    (hVAL : ∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v)
    (test : ℕ) (hTest : 1 ≤ test) :
    let n := Fintype.card V
    let initial := initialExceptionalSet G η
    let low := initialLowSet G η
    let shift := η*(n:ℝ)
    let threshold := ⌈shift⌉₊
    let cap := ⌊shift⌋₊
    let long := ⌊(G.maxDegree:ℝ)/3-shift⌋₊
    let short := ⌊(G.maxDegree:ℝ)/3-2*shift⌋₊
    64 ≤ shift → 6 ≤ η^2*(n:ℝ) → 24*shift ≤ (G.maxDegree:ℝ) →
    (initial.card:ℝ) ≤ η^2*(n:ℝ) →
    ∃ m ≤ long,∃ H : OriginalTrimmingHistory G initial low threshold long cap test m,
      m = long ∨
      HasAlmostOverfullRecord (univ.filter (fun v => 0 < H.degree m v))
        (G.maxDegree-2*m) test (H.degree m) ∨
      ∃ T : SimpleGraph V,
        let S : VirtualTrimmingState V := ⟨T,H.prescribed,H.credit,H.free⟩
        let support := univ.filter (fun v => 0 < S.record initial m v)
        let current := H.exceptional m ∩ support
        DeletionRun (H.exceptional m ∩ low) (H.graph m) T ∧
          (HasAlmostOverfullRecord support (G.maxDegree-2*m) test (S.record initial m) ∨
            ∃ A,
              CriticalTrimmingEntry T initial current A (S.record initial m) (G.maxDegree-2*m)
                long (3*low.card+initial.card+1) ∧
              (short ≤ m ∨ HasCompletedShortTrimmingPhase S initial current A (G.maxDegree-2*m)
                long (3*low.card+initial.card+1) threshold test m cap (short-m))) := by
  intro n initial low shift threshold cap long short hShift hSize hDense hFew
  have hLow : low.card ≤ initial.card := card_le_card (filter_subset _ _)
  have hShift' : 0 ≤ shift := by linarith only [hShift]
  have hShiftLe : shift ≤ n := by
    have h := mul_le_mul_of_nonneg_right (show η ≤ 1 by linarith only [hSmall])
      (Nat.cast_nonneg (α := ℝ) n)
    simpa only [shift,one_mul] using h
  have hFew' : (initial.card:ℝ) ≤ shift/64 := by
    have h := mul_le_mul_of_nonneg_right hSmall hShift'
    dsimp only [shift] at h ⊢
    nlinarith only [h,hFew]
  have hJoin : (initial.card:ℝ)+(initialᶜ.card:ℝ) = n := by exact_mod_cast card_add_card_compl initial
  have hCore : 4 ≤ initialᶜ.card := by
    exact_mod_cast (show (4:ℝ) ≤ initialᶜ.card by linarith only [hJoin,hShift,hFew',hShiftLe])
  have hCap : 0 < cap := by
    change 1 ≤ cap
    apply Nat.le_floor
    exact_mod_cast (show (1:ℝ) ≤ shift by linarith only [hShift])
  have hThreshold : 2 ≤ threshold := by
    have hCeil : shift ≤ (threshold:ℝ) := Nat.le_ceil _
    exact_mod_cast (show (2:ℝ) ≤ threshold by linarith only [hShift,hCeil])
  have hNV : Nonempty V := Fintype.card_pos_iff.mp
    (by exact_mod_cast (show 0 < (n:ℝ) by linarith only [hShift,hShiftLe]))
  have hG : (G.maxDegree:ℝ) ≤ n := by exact_mod_cast G.maxDegree_lt_card_verts.le
  have hShort : (short:ℝ) ≤ (G.maxDegree:ℝ)/3-2*shift := Nat.floor_le (by linarith only [hDense,hShift])
  have hRounds : 3*short ≤ n := by
    exact_mod_cast (show (3:ℝ)*short ≤ n by linarith only [hG,hShort,hShift])
  have hRate := free_projection_budget_at_trimming_limit n short initial.card η hRounds
    (show 12 ≤ shift by linarith only [hShift]) hSize hFew
  obtain ⟨hWindow,hPair,hProjection⟩ :=
    critical_phase_rounded_reserves n G.maxDegree initial.card η hη hSmall hShift hDense hFew
  change long+1+threshold ≤ G.maxDegree-2*short at hWindow
  change short+6+(5*initial.card+12) ≤ long at hPair
  change 5*initial.card+cap+4+(5*initial.card+12) ≤ long at hProjection
  obtain ⟨m,hm,H,hBoundary⟩ :=
    cms_operation_4_1_first_critical_selection G η hη hSmall hVAL test hTest hShift hSize hDense hFew
  refine ⟨m,hm,H,?_⟩
  rcases hBoundary with hLimit | hAlmost | ⟨T,hRun,hNext⟩
  · exact Or.inl hLimit
  · exact Or.inr (Or.inl hAlmost)
  right
  right
  refine ⟨T,hRun,?_⟩
  rcases hNext with hAlmost | ⟨A,E,_⟩
  · exact Or.inl hAlmost
  right
  refine ⟨A,E,?_⟩
  by_cases hAtLimit : short ≤ m
  · exact Or.inl hAtLimit
  right
  let S : VirtualTrimmingState V := ⟨T,H.prescribed,H.credit,H.free⟩
  let current := H.exceptional m ∩ univ.filter (fun v => 0 < S.record initial m v)
  let loss := 3*low.card+initial.card+1
  change CriticalTrimmingEntry S.graph initial current A (S.record initial m) (G.maxDegree-2*m)
    long loss at E
  have hCurrent : current.card ≤ initial.card := card_le_card E.current_initial
  have hBefore : m ≤ short := (Nat.lt_of_not_ge hAtLimit).le
  have hSpan : m+(short-m) = short := Nat.add_sub_of_le hBefore
  have hRate' : (m+(short-m))*(2*(initial.card+1)) ≤ cap*cap := by
    rw [hSpan]
    exact hRate
  have hBand : long+1+threshold ≤ G.maxDegree-2*m-2*(short-m) := by
    rwa [Nat.sub_sub,←Nat.mul_add,hSpan]
  have hRoom : 5*initial.card+cap+4+(loss+current.card+8) ≤ long := by
    dsimp only [loss]
    omega
  have hPairRoom : short-m+6+(loss+current.card+4) ≤ long := by
    dsimp only [loss]
    omega
  exact E.complete_short_phase threshold test (short-m) hThreshold hTest hCap hCore hRate'
    hRoom hPairRoom hBand H.free_size H.free_load

end OverfullWork.CMSTrimmingRound
