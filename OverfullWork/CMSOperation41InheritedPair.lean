module

public import OverfullWork.CMSOperation41CriticalLoss

@[expose] public section


/-! Continue with a fixed inherited pair until the short limit or
an almost-overfull record. Its two endpoints spend one edge per
round. All other exceptional losses are paid by distinct incidences
with the pair. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

structure VirtualTrimmingState (V : Type*) where
  graph : SimpleGraph V
  prescribed : ℕ → SimpleGraph V
  credit : ℕ → V → ℕ
  used : ℕ → Finset V

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def VirtualTrimmingState.record (S : VirtualTrimmingState V)
    (initial : Finset V) (j : ℕ) : V → ℕ :=
  auxiliaryPhysicalDegree S.graph initial S.prescribed S.credit j

def VirtualTrimmingState.advance (S : VirtualTrimmingState V) (j : ℕ)
    (P : SimpleGraph V) (credit : V → ℕ) (free : Finset V) : VirtualTrimmingState V :=
  ⟨sdiff S.graph P,Function.update S.prescribed j P,
    Function.update S.credit j credit,Function.update S.used j free⟩

noncomputable def TrimmingStepSelection.freeEndpoints
    {T : SimpleGraph V} [DecidableRel T.Adj] {initial current active : Finset V}
    {degree : V → ℕ} {d floor j cap : ℕ} {used : ℕ → Finset V}
    (R : TrimmingStepSelection T initial current active degree d floor used j cap) : Finset V :=
  (univ.image (fun e => (R.round.words.endpoint e).val)).filter
    (fun v => projectionLoad (range j) used v < cap)

def HasTrimmingRoundWithoutCleanup (S T : VirtualTrimmingState V)
    (initial current active support : Finset V) (d floor test j cap : ℕ) : Prop :=
  ¬HasAlmostOverfullRecord support d test (S.record initial j) ∧
    ∃ R : TrimmingStepSelection S.graph initial current active (S.record initial j) d floor S.used j cap,
      T = S.advance j R.round.words.prescribedGraph
        (R.round.words.degreeCredit R.round.omitted) R.freeEndpoints

/-- For an inactive vertex, the left side of the inequality decreases
by twice the number of its deleted neighbours in the pair. More than
that many degree units cannot be spent in the round. -/
structure InheritedPairPosition (origin : SimpleGraph V)
    (initial current active support : Finset V) (S : VirtualTrimmingState V)
    (d floor loss j left cap : ℕ) : Prop where
  degree_bound : ∀ v,S.record initial j v ≤ d
  support_eq : univ.filter (fun v => 0 < S.record initial j v) = support
  exceptional_upper : ∀ v ∈ current,S.record initial j v < floor+2
  ordinary_deficit : (∑ v ∈ support \ current,(d-S.record initial j v)) ≤ 1
  active_room : ∀ w ∈ active,left+6 ≤ S.graph.degree w
  inactive_balance : ∀ v ∈ current,v ∉ active →
    floor+2*(S.graph.neighborFinset v ∩ active).card ≤
      S.graph.degree v+loss+2*(origin.neighborFinset v ∩ active).card
  free_size : ∀ i < j,(S.used i).card ≤ 2*(initial.card+1)
  free_load : ∀ v,projectionLoad (range j) S.used v ≤ cap

theorem neighbour_finset_inter_add_sdiff
    (S P : SimpleGraph V) (hLe : P ≤ S) (A : Finset V) (v : V) :
    ((sdiff S P).neighborFinset v ∩ A).card+(P.neighborFinset v ∩ A).card =
      (S.neighborFinset v ∩ A).card := by
  let L := (sdiff S P).neighborFinset v ∩ A
  let R := P.neighborFinset v ∩ A
  have hDis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro x hL hR
    exact ((mem_neighborFinset _ _ _).mp (mem_inter.mp hL).1).2
      ((mem_neighborFinset _ _ _).mp (mem_inter.mp hR).1)
  have hUnion : L ∪ R = S.neighborFinset v ∩ A := by
    ext x
    simp only [L,R,mem_union,mem_inter,mem_neighborFinset,sdiff_adj]
    have h := @hLe v x
    tauto
  rw [←hUnion,card_union_of_disjoint hDis]

set_option maxHeartbeats 4500000 in
/-- One more pair round supplies the next position with the very
same reserve for inactive vertices. The active degree reserve
decreases by one together with the remaining round count. -/
theorem InheritedPairPosition.continue_or_stop
    {origin : SimpleGraph V} {initial current active support : Finset V}
    {S : VirtualTrimmingState V} {d floor loss j left cap : ℕ}
    (state : InheritedPairPosition origin initial current active support S d floor loss j (left+1) cap)
    (threshold test : ℕ) (hTest : 1 ≤ test) (hCap : 0 < cap)
    (hSize : 4 ≤ initialᶜ.card) (hRate : j*(2*(initial.card+1)) ≤ cap*cap)
    (hInitial : current ⊆ initial) (hCurrent : current ⊆ support)
    (hCoreSupport : initialᶜ ⊆ support) (hActive : active ⊆ current) (hPair : active.card = 2)
    (hWindow : floor+1+threshold ≤ d-2)
    (hRoom : 5*initial.card+cap+4+(loss+4) ≤ floor) :
    HasAlmostOverfullRecord support d test (S.record initial j) ∨
      ∃ T : VirtualTrimmingState V,
        HasTrimmingRoundWithoutCleanup S T initial current active support d floor test j cap ∧
        InheritedPairPosition origin initial current active support T (d-2) floor loss (j+1) left cap ∧
        nextTrimmingExceptional current support (T.record initial (j+1)) (d-2) threshold = current := by
  by_cases hStop : HasAlmostOverfullRecord support d test (S.record initial j)
  · exact Or.inl hStop
  let degree := S.record initial j
  have hOldExact (v : V) (hv : v ∈ initial) : degree v = S.graph.degree v := by
    simp only [degree,VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hv]
  have hOrd (v : V) (hv : v ∈ support) (hn : v ∉ current) : d ≤ degree v+1 := by
    have h := single_le_sum (f := fun u => d-degree u) (fun _ _ => Nat.zero_le _)
      (mem_sdiff.mpr ⟨hv,hn⟩)
    have hm := state.ordinary_deficit
    change (∑ u ∈ support \ current,(d-degree u)) ≤ 1 at hm
    omega
  have hCore (v : V) (hv : v ∉ initial) : 2 ≤ degree v := by
    have h := hOrd v (hCoreSupport (mem_compl.mpr hv)) (fun h => hv (hInitial h))
    omega
  have hHigh (v : V) (hv : v ∈ active) : 6 ≤ S.graph.degree v := by
    have h := state.active_room v hv
    omega
  have hProj (v : V) (hv : v ∈ initial) (ha : v ∉ active) (hp : 0 < S.graph.degree v) :
      5*initial.card+cap+4 ≤ S.graph.degree v := by
    by_cases h : v ∈ current
    · have hbal := state.inactive_balance v h ha
      have hn : (origin.neighborFinset v ∩ active).card ≤ 2 := hPair ▸ card_le_card inter_subset_right
      omega
    · have hSupp : v ∈ support := by
        rw [←state.support_eq]
        exact mem_filter.mpr ⟨mem_univ _,by rw [←hOldExact v hv] at hp; exact hp⟩
      have hDeg := hOrd v hSupp h
      rw [hOldExact v hv] at hDeg
      omega
  have hNo : ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 < degree v)) d test degree := by
    change ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 < S.record initial j v)) d test (S.record initial j)
    rwa [state.support_eq]
  have hInSupport : current ⊆ univ.filter (fun v => 0 < degree v) := by
    change current ⊆ univ.filter (fun v => 0 < S.record initial j v)
    rwa [state.support_eq]
  have hCoreIn : initialᶜ ⊆ univ.filter (fun v => 0 < degree v) := by
    change initialᶜ ⊆ univ.filter (fun v => 0 < S.record initial j v)
    rwa [state.support_eq]
  rcases exists_trimming_step_selection S.graph initial current active hInitial hActive
    (fun v hv => by have h := hHigh v hv; omega) (Or.inr ⟨hPair,hHigh⟩)
    degree d floor test (by omega) state.degree_bound hOldExact
    (fun v hv => by have h := state.exceptional_upper v hv; change degree v < floor+2 at h; omega)
    hSize S.used j cap cap (2*(initial.card+1)) hCap state.free_size hRate hInSupport hCoreIn
    hTest hNo hProj with hSelect | hSwitch
  · obtain ⟨R⟩ := hSelect
    let T := S.advance j R.round.words.prescribedGraph (R.round.words.degreeCredit R.round.omitted) R.freeEndpoints
    let record := T.record initial (j+1)
    have hRead (v : V) : record v ≤ d-2 ∧
        record v+(2-R.round.words.degreeCredit R.round.omitted v) = degree v := by
      have h := (R.advance_without_cleanup S.prescribed S.credit (fun _ => rfl) hCore).2 v
      simpa only [record,T,VirtualTrimmingState.record,VirtualTrimmingState.advance,Function.update_self] using h
    have hDegree (v : V) :
        T.graph.degree v+R.round.words.prescribedGraph.degree v = S.graph.degree v := by
      change (sdiff S.graph R.round.words.prescribedGraph).degree v+
        R.round.words.prescribedGraph.degree v = S.graph.degree v
      simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le S.graph R.round.words.prescribedGraph
          R.round.words.prescribedGraph_le v
    have hMass : (∑ v ∈ support \ current,(d-2-record v)) ≤ 1 := by
      have h := ordinary_deficit_balance_after_trimming_round (support \ current) degree record
        (fun _ => 0) (R.round.words.degreeCredit R.round.omitted) d (by omega)
        (fun v _ => state.degree_bound v) (fun v _ => (hRead v).1)
        (fun v _ => R.round.words.degree_credit_le_two R.round.omitted v)
        (fun v _ => by simpa only [add_zero] using (hRead v).2)
      have hm := state.ordinary_deficit
      change (∑ v ∈ support \ current,(d-degree v)) ≤ 1 at hm
      simp only [sum_const_zero,add_zero] at h
      omega
    have hRoomActive (w : V) (hw : w ∈ active) : left+6 ≤ T.graph.degree w := by
      have hUnit := R.pair_progress hPair hHigh w hw
      have h := state.active_room w hw
      have hn := hDegree w
      omega
    have hInactive (v : V) (hv : v ∈ current) (ha : v ∉ active) :
        floor+2*(T.graph.neighborFinset v ∩ active).card ≤
          T.graph.degree v+loss+2*(origin.neighborFinset v ∩ active).card := by
      have hEdges : (T.graph.neighborFinset v ∩ active).card+
          (R.round.words.prescribedGraph.neighborFinset v ∩ active).card =
          (S.graph.neighborFinset v ∩ active).card :=
        neighbour_finset_inter_add_sdiff S.graph R.round.words.prescribedGraph
          R.round.words.prescribedGraph_le active v
      have hCost := R.inactive_pair_degree_charge hPair hInitial v hv ha
      dsimp only at hCost
      have h := state.inactive_balance v hv ha
      have hDeg := hDegree v
      omega
    have hSurvive (v : V) (hv : v ∈ support) : 0 < record v := by
      by_cases hu : v ∈ current
      · have hExact : record v = T.graph.degree v := by
          simp only [record,VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos (hInitial hu)]
        rw [hExact]
        by_cases ha : v ∈ active
        · have h := hRoomActive v ha
          omega
        · have h := hInactive v hu ha
          have hn : (origin.neighborFinset v ∩ active).card ≤ 2 := hPair ▸ card_le_card inter_subset_right
          omega
      · have h := single_le_sum (f := fun u => d-2-record u) (fun _ _ => Nat.zero_le _)
          (mem_sdiff.mpr ⟨hv,hu⟩)
        omega
    have hSupport : univ.filter (fun v => 0 < record v) = support := by
      ext v
      constructor
      · intro h
        have hp := (mem_filter.mp h).2
        have hn := (hRead v).2
        rw [←state.support_eq]
        exact mem_filter.mpr ⟨mem_univ _,by change 0 < degree v; omega⟩
      · exact fun h => mem_filter.mpr ⟨mem_univ _,hSurvive v h⟩
    have hUpper (v : V) (hv : v ∈ current) : record v < floor+2 := by
      have h := state.exceptional_upper v hv
      change degree v < floor+2 at h
      have hn := (hRead v).2
      omega
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
    refine Or.inr ⟨T,⟨hStop,R,rfl⟩,
      ⟨fun v => (hRead v).1,hSupport,hUpper,hMass,hRoomActive,hInactive,hFree,hFLoad⟩,?_⟩
    apply le_antisymm ((filter_subset _ _).trans inter_subset_left)
    intro v hv
    have h := hUpper v hv
    exact mem_filter.mpr ⟨mem_inter.mpr ⟨hv,hCurrent hv⟩,by change threshold ≤ d-2-record v; omega⟩
  · have hZero : active.card = 0 := by rw [hSwitch.1,card_empty]
    omega

/-- Start the fixed pair from the critical entry, or from a later
entry with the same reserve after the singleton has been removed. -/
theorem CriticalTrimmingEntry.start_inherited_pair
    {S : VirtualTrimmingState V} {initial current active : Finset V}
    {d floor loss j left cap : ℕ}
    (E : CriticalTrimmingEntry S.graph initial current active (S.record initial j) d floor loss)
    (hEntry : left+6+loss ≤ floor)
    (hSize : ∀ i < j,(S.used i).card ≤ 2*(initial.card+1))
    (hLoad : ∀ v,projectionLoad (range j) S.used v ≤ cap) :
    InheritedPairPosition S.graph initial current active
      (univ.filter (fun v => 0 < S.record initial j v)) S d floor loss j left cap := by
  refine ⟨E.degree_cap,rfl,E.exceptional_upper,E.ordinary_deficit,?_,?_,hSize,hLoad⟩
  · intro w hw
    have hc := E.active_current hw
    have hi := E.current_initial hc
    have hp := E.current_positive w hc
    rw [E.degree_exact w hi] at hp
    have h := E.degree_floor w hi hp
    omega
  · intro v hv _
    have hi := E.current_initial hv
    have hp := E.current_positive v hv
    rw [E.degree_exact v hi] at hp
    exact Nat.add_le_add_right (E.degree_floor v hi hp) _

structure InheritedPairHistory (start : VirtualTrimmingState V)
    (initial current active support : Finset V)
    (D floor loss threshold test j cap total m : ℕ) where
  states : ℕ → VirtualTrimmingState V
  starts : states 0 = start
  rounds : ∀ i < m,HasTrimmingRoundWithoutCleanup (states i) (states (i+1))
    initial current active support (D-2*i) floor test (j+i) cap
  positions : ∀ i ≤ m,InheritedPairPosition start.graph initial current active support
    (states i) (D-2*i) floor loss (j+i) (total-i) cap
  exceptional : ∀ i < m,nextTrimmingExceptional current support
    ((states (i+1)).record initial (j+(i+1))) (D-2*(i+1)) threshold = current

set_option maxHeartbeats 3500000 in
/-- Construct all later pair rounds. The supplied longer history
remains in the initial arrays, and each new round retains its exact
prescription for the eventual simultaneous packing. -/
theorem exists_inherited_pair_trimming_history
    (start : VirtualTrimmingState V) (initial current active support : Finset V)
    (D floor loss threshold test j cap total : ℕ)
    (hEntry : InheritedPairPosition start.graph initial current active support start D floor loss j total cap)
    (hTest : 1 ≤ test) (hCap : 0 < cap) (hSize : 4 ≤ initialᶜ.card)
    (hRate : (j+total)*(2*(initial.card+1)) ≤ cap*cap)
    (hInitial : current ⊆ initial) (hCurrent : current ⊆ support)
    (hCoreSupport : initialᶜ ⊆ support) (hActive : active ⊆ current) (hPair : active.card = 2)
    (hWindow : floor+1+threshold ≤ D-2*total)
    (hRoom : 5*initial.card+cap+4+(loss+4) ≤ floor) :
    ∃ m ≤ total,∃ H : InheritedPairHistory start initial current active support
      D floor loss threshold test j cap total m,
      m = total ∨ HasAlmostOverfullRecord support (D-2*m) test ((H.states m).record initial (j+m)) := by
  let History (i : ℕ) := InheritedPairHistory start initial current active support
    D floor loss threshold test j cap total i
  have hZero : Nonempty (History 0) := by
    refine ⟨⟨fun _ => start,rfl,by simp,?_,by simp⟩⟩
    intro i hi
    have he : i = 0 := by omega
    subst i
    simpa only [Nat.mul_zero,Nat.sub_zero,Nat.add_zero] using hEntry
  have hGrow (i : ℕ) (hi : i ≤ total) :
      (∃ m ≤ i,∃ H : History m,
        HasAlmostOverfullRecord support (D-2*m) test ((H.states m).record initial (j+m))) ∨
        Nonempty (History i) := by
    induction i with
    | zero => exact Or.inr hZero
    | succ i ih =>
      have hi' : i ≤ total := (Nat.le_succ _).trans hi
      have hD : D-2*i-2 = D-2*(i+1) := by rw [Nat.mul_succ,Nat.sub_sub]
      have hIndex : j+i+1 = j+(i+1) := Nat.add_assoc _ _ _
      have hWindow' : floor+1+threshold ≤ (D-2*i)-2 := by
        rw [hD]
        exact hWindow.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 hi) _)
      let left := total-(i+1)
      have hLeft : total-i = left+1 := by
        dsimp only [left]
        rw [←Nat.sub_sub]
        exact (Nat.sub_add_cancel (Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hi))).symm
      rcases ih hi' with ⟨m,hm,H,hStop⟩ | hHistory
      · exact Or.inl ⟨m,hm.trans (Nat.le_succ _),H,hStop⟩
      obtain ⟨H⟩ := hHistory
      have hState := H.positions i le_rfl
      rw [hLeft] at hState
      have hr := (Nat.mul_le_mul_right (2*(initial.card+1))
        (Nat.add_le_add_left hi' j)).trans hRate
      rcases hState.continue_or_stop threshold test hTest hCap hSize hr hInitial hCurrent
        hCoreSupport hActive hPair hWindow' hRoom with hStop | ⟨T,hStep,hNext,hExceptional⟩
      · exact Or.inl ⟨i,Nat.le_succ _,H,hStop⟩
      let states := Function.update H.states (i+1) T
      have hPrior (k : ℕ) (hk : k ≤ i) : states k = H.states k :=
        Function.update_of_ne (by omega) _ _
      have hLast : states (i+1) = T := Function.update_self _ _ _
      rw [hD,hIndex] at hNext hExceptional
      refine Or.inr ⟨⟨states,(hPrior 0 (Nat.zero_le _)).trans H.starts,?_,?_,?_⟩⟩
      · intro k hk
        by_cases he : k = i
        · subst k
          rwa [hPrior i le_rfl,hLast]
        · have hk' : k < i := by omega
          rw [hPrior k hk'.le,hPrior (k+1) (by omega)]
          exact H.rounds k hk'
      · intro k hk
        by_cases he : k = i+1
        · subst k
          rwa [hLast]
        · have hk' : k ≤ i := by omega
          rw [hPrior k hk']
          exact H.positions k hk'
      · intro k hk
        by_cases he : k = i
        · subst k
          rwa [hLast]
        · have hk' : k < i := by omega
          rw [hPrior (k+1) (by omega)]
          exact H.exceptional k hk'
  rcases hGrow total le_rfl with ⟨m,hm,H,hStop⟩ | hFull
  · exact ⟨m,hm,H,Or.inr hStop⟩
  · obtain ⟨H⟩ := hFull
    exact ⟨total,le_rfl,H,Or.inl rfl⟩

/-- Begin the complete pair run at a certified critical entry. The
ordinary complement stays in the support by its entry degree bound. -/
theorem CriticalTrimmingEntry.exists_inherited_pair_run
    {start : VirtualTrimmingState V} {initial current active : Finset V}
    {D floor loss j cap : ℕ}
    (E : CriticalTrimmingEntry start.graph initial current active (start.record initial j) D floor loss)
    (threshold test total : ℕ) (hTest : 1 ≤ test) (hCap : 0 < cap) (hSize : 4 ≤ initialᶜ.card)
    (hRate : (j+total)*(2*(initial.card+1)) ≤ cap*cap)
    (hPair : active.card = 2) (hEntry : total+6+loss ≤ floor)
    (hWindow : floor+1+threshold ≤ D-2*total)
    (hRoom : 5*initial.card+cap+4+(loss+4) ≤ floor)
    (hSize₀ : ∀ i < j,(start.used i).card ≤ 2*(initial.card+1))
    (hLoad₀ : ∀ v,projectionLoad (range j) start.used v ≤ cap) :
    let support := univ.filter (fun v => 0 < start.record initial j v)
    ∃ m ≤ total,∃ H : InheritedPairHistory start initial current active support
      D floor loss threshold test j cap total m,
      m = total ∨ HasAlmostOverfullRecord support (D-2*m) test ((H.states m).record initial (j+m)) := by
  intro support
  have hCurrent : current ⊆ support := fun v hv =>
    mem_filter.mpr ⟨mem_univ _,E.current_positive v hv⟩
  have hCore : initialᶜ ⊆ support := fun v hv =>
    mem_filter.mpr ⟨mem_univ _,by have h := E.core_room v (mem_compl.mp hv); omega⟩
  exact exists_inherited_pair_trimming_history start initial current active support D floor loss
    threshold test j cap total (E.start_inherited_pair hEntry hSize₀ hLoad₀)
    hTest hCap hSize hRate E.current_initial hCurrent hCore E.active_current hPair hWindow hRoom

set_option maxHeartbeats 2600000 in
/-- The weak degree-sum bound propagates across a complete inherited
pair history. An active endpoint spends exactly one per round, and
an inactive exceptional endpoint has a constant cumulative budget. -/
theorem InheritedPairHistory.weak_degree_sum
    {start : VirtualTrimmingState V} {initial current active support : Finset V}
    {D floor loss threshold test j cap total m : ℕ}
    (H : InheritedPairHistory start initial current active support D floor loss threshold test j cap total m)
    (hInitial : current ⊆ initial) (hPair : active.card = 2)
    (budget : ℕ)
    (hEntry : ∀ u v,start.graph.Adj u v →
      D ≤ start.record initial j u+start.record initial j v+budget) :
    ∀ u v,(H.states m).graph.Adj u v →
      (∀ x,x ∉ initial → x ∈ support) →
      D-2*m ≤ (H.states m).record initial (j+m) u+(H.states m).record initial (j+m) v+
        budget+2*(loss+5) := by
  have hPrefix (i : ℕ) (hi : i ≤ m) :
      (H.states i).graph ≤ start.graph ∧
      ∀ w ∈ active,(H.states i).graph.degree w+i = start.graph.degree w := by
    induction i with
    | zero => rw [H.starts]; exact ⟨le_rfl,by simp⟩
    | succ i ih =>
      have hi' : i < m := by omega
      obtain ⟨hG,hA⟩ := ih hi'.le
      obtain ⟨_,R,hNext⟩ := H.rounds i hi'
      have hHigh (w : V) (hw : w ∈ active) : 6 ≤ (H.states i).graph.degree w := by
        have h := (H.positions i hi'.le).active_room w hw
        omega
      refine ⟨?_,?_⟩
      · rw [hNext]
        exact fun u v he => hG he.1
      · intro w hw
        have hUnit := R.pair_progress hPair hHigh w hw
        have hStep : (H.states (i+1)).graph.degree w+R.round.words.prescribedGraph.degree w =
            (H.states i).graph.degree w := by
          rw [hNext]
          change (sdiff (H.states i).graph R.round.words.prescribedGraph).degree w+
            R.round.words.prescribedGraph.degree w = (H.states i).graph.degree w
          simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
            MaximumMatching.degree_sdiff_add_of_le (H.states i).graph R.round.words.prescribedGraph
              R.round.words.prescribedGraph_le w
        have h := hA w hw
        omega
  have first := H.positions 0 (Nat.zero_le _)
  have last := H.positions m le_rfl
  have hBound (v : V) (hv : v ∈ current) :
      start.record initial j v ≤ (H.states m).record initial (j+m) v+m+loss+5 := by
    have hvI := hInitial hv
    simp only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hvI]
    by_cases ha : v ∈ active
    · have h := (hPrefix m le_rfl).2 v ha
      omega
    · have hBefore := first.exceptional_upper v hv
      rw [H.starts,Nat.add_zero,VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hvI] at hBefore
      have hAfter := last.inactive_balance v hv ha
      have hN : (start.graph.neighborFinset v ∩ active).card ≤ 2 := hPair ▸ card_le_card inter_subset_right
      omega
  intro u v hEdge hCore
  by_cases hBoth : u ∈ current ∧ v ∈ current
  · have hu := hBound u hBoth.1
    have hv := hBound v hBoth.2
    have he := hEntry u v ((hPrefix m le_rfl).1 hEdge)
    omega
  have hOrd (x : V) (hx : x ∉ current) (hPos : 0 < (H.states m).graph.degree x) :
      D-2*m ≤ (H.states m).record initial (j+m) x+1 := by
    have hs : x ∈ support := by
      by_cases h : x ∈ initial
      · rw [←last.support_eq]
        exact mem_filter.mpr ⟨mem_univ _,by
          simpa only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos h] using hPos⟩
      · exact hCore x h
    have he := single_le_sum (f := fun v => D-2*m-(H.states m).record initial (j+m) v)
      (fun _ _ => Nat.zero_le _) (mem_sdiff.mpr ⟨hs,hx⟩)
    have hm := last.ordinary_deficit
    omega
  rcases not_and_or.mp hBoth with hu | hv
  · have h := hOrd u hu (((H.states m).graph.degree_pos_iff_exists_adj _).mpr ⟨v,hEdge⟩)
    omega
  · have h := hOrd v hv (((H.states m).graph.degree_pos_iff_exists_adj _).mpr ⟨u,hEdge.symm⟩)
    omega

end OverfullWork.CMSTrimmingRound
