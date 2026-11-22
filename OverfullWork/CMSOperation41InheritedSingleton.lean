module

public import OverfullWork.CMSOperation41InheritedPair

@[expose] public section


/-! Continue the inherited singleton while its degree is at least
two. Its capped remaining degree pays for internal charges. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

structure InheritedSingletonPosition (origin : SimpleGraph V)
    (initial current support : Finset V) (w : V) (S : VirtualTrimmingState V)
    (d floor loss j cap : ℕ) : Prop where
  degree_bound : ∀ v,S.record initial j v ≤ d
  support_except : (univ.filter (fun v => 0 < S.record initial j v)).erase w = support.erase w
  exceptional_upper : ∀ v ∈ current,S.record initial j v < floor+2
  ordinary_deficit : (∑ v ∈ support \ current,(d-S.record initial j v)) ≤ 1
  inactive_balance : ∀ v ∈ current,v ≠ w →
    floor+2*(S.graph.neighborFinset v ∩ {w}).card+min (current.card+1) (S.graph.degree w) ≤
      S.graph.degree v+loss+2*(origin.neighborFinset v ∩ {w}).card+min (current.card+1) (origin.degree w)
  free_size : ∀ i < j,(S.used i).card ≤ 2*(initial.card+1)
  free_load : ∀ v,projectionLoad (range j) S.used v ≤ cap

theorem InheritedSingletonPosition.inactive_floor
    {origin : SimpleGraph V} {initial current support : Finset V} {w : V}
    {S : VirtualTrimmingState V} {d floor loss j cap : ℕ}
    (state : InheritedSingletonPosition origin initial current support w S d floor loss j cap)
    (v : V) (hv : v ∈ current) (hne : v ≠ w) :
    floor ≤ S.graph.degree v+loss+current.card+3 := by
  have h := state.inactive_balance v hv hne
  have hCard : (origin.neighborFinset v ∩ {w}).card ≤ 1 := by
    rw [←card_singleton w]
    exact card_le_card inter_subset_right
  have hCap := min_le_left (current.card+1) (origin.degree w)
  omega

set_option maxHeartbeats 2800000 in
theorem InheritedSingletonPosition.select_or_stop
    {origin : SimpleGraph V} {initial current support : Finset V} {w : V}
    {S : VirtualTrimmingState V} {d floor loss j cap : ℕ}
    (state : InheritedSingletonPosition origin initial current support w S d floor loss j cap)
    (test : ℕ) (hTest : 1 ≤ test) (hCap : 0 < cap)
    (hSize : 4 ≤ initialᶜ.card) (hRate : j*(2*(initial.card+1)) ≤ cap*cap)
    (hInitial : current ⊆ initial) (hCurrent : current ⊆ support)
    (hCoreSupport : initialᶜ ⊆ support) (hw : w ∈ current)
    (hWindow : floor+3 ≤ d)
    (hRoom : 5*initial.card+cap+4+(loss+current.card+3) ≤ floor) :
    let degree := S.record initial j
    let actual := univ.filter (fun v => 0 < degree v)
    HasAlmostOverfullRecord actual d test degree ∨ S.graph.degree w ≤ 1 ∨
      (actual = support ∧ ¬HasAlmostOverfullRecord support d test degree ∧
        (∀ v,v ∉ initial → 2 ≤ degree v) ∧
        Nonempty (TrimmingStepSelection S.graph initial current {w} degree d floor S.used j cap)) := by
  intro degree actual
  by_cases hStop : HasAlmostOverfullRecord actual d test degree
  · exact Or.inl hStop
  by_cases hSmall : S.graph.degree w ≤ 1
  · exact Or.inr (Or.inl hSmall)
  have hExact (v : V) (hv : v ∈ initial) : degree v = S.graph.degree v := by
    simp only [degree,VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hv]
  have hSupp : actual = support := by
    ext v
    by_cases he : v = w
    · subst v
      rw [show w ∈ actual ↔ 0 < degree w from by simp [actual],hExact w (hInitial hw)]
      exact iff_of_true (by omega) (hCurrent hw)
    · have hh := Finset.ext_iff.mp state.support_except v
      exact ⟨fun h => (mem_erase.mp (hh.mp (mem_erase.mpr ⟨he,h⟩))).2,
        fun h => (mem_erase.mp (hh.mpr (mem_erase.mpr ⟨he,h⟩))).2⟩
  have hOrd (v : V) (hv : v ∈ support) (hn : v ∉ current) : d ≤ degree v+1 := by
    have h := single_le_sum (f := fun u => d-degree u) (fun _ _ => Nat.zero_le _)
      (mem_sdiff.mpr ⟨hv,hn⟩)
    have hm := state.ordinary_deficit
    change (∑ u ∈ support \ current,(d-degree u)) ≤ 1 at hm
    omega
  have hCore (v : V) (hv : v ∉ initial) : 2 ≤ degree v := by
    have h := hOrd v (hCoreSupport (mem_compl.mpr hv)) (fun h => hv (hInitial h))
    omega
  have hProj (v : V) (hv : v ∈ initial) (ha : v ∉ ({w} : Finset V)) (hp : 0 < S.graph.degree v) :
      5*initial.card+cap+4 ≤ S.graph.degree v := by
    by_cases hc : v ∈ current
    · have h := state.inactive_floor v hc (by simpa using ha)
      omega
    · have hm : v ∈ actual := mem_filter.mpr ⟨mem_univ _,by rwa [hExact v hv]⟩
      have h := hOrd v (hSupp ▸ hm) hc
      rw [hExact v hv] at h
      omega
  have hMode : S.graph.IsIndepSet (↑({w} : Finset V) : Set V) ∧
      ∀ a ∈ ({w} : Finset V),∀ x,S.graph.Adj a x →
        PrunedCore.neighboursIn S.graph {w} x < S.graph.degree a := by
    constructor
    · rw [isIndepSet_iff]
      intro a ha b hb hn _
      have ha' : a = w := by simpa using ha
      have hb' : b = w := by simpa using hb
      exact hn (ha'.trans hb'.symm)
    · intro a ha x _
      have h : PrunedCore.neighboursIn S.graph {w} x ≤ ({w} : Finset V).card :=
        card_le_card (fun v hv => (mem_filter.mp hv).2)
      rw [card_singleton] at h
      rw [mem_singleton.mp ha]
      omega
  have hCurrent' : current ⊆ actual := by rw [hSupp]; exact hCurrent
  have hCore' : initialᶜ ⊆ actual := by rw [hSupp]; exact hCoreSupport
  rcases exists_trimming_step_selection S.graph initial current {w} hInitial
    (singleton_subset_iff.mpr hw) (fun a ha => by rw [mem_singleton.mp ha]; omega)
    (Or.inl hMode) degree d floor test (by omega) state.degree_bound hExact
    (fun v hv => by have h := state.exceptional_upper v hv; change degree v < floor+2 at h; omega)
    hSize S.used j cap cap (2*(initial.card+1)) hCap state.free_size hRate hCurrent' hCore'
    hTest hStop hProj with hSelect | hSwitch
  · have hNo : ¬HasAlmostOverfullRecord support d test degree := by rw [←hSupp]; exact hStop
    exact Or.inr (Or.inr ⟨hSupp,hNo,hCore,hSelect⟩)
  · exact (notMem_empty w (hSwitch.1 ▸ mem_singleton_self w)).elim

set_option maxHeartbeats 4400000 in
/-- An actual singleton round spends at least one active edge. The
updated exceptional set is obtained by intersecting with the support,
so the support can lose only the singleton on its final round. -/
theorem InheritedSingletonPosition.continue_or_stop
    {origin : SimpleGraph V} {initial current support : Finset V} {w : V}
    {S : VirtualTrimmingState V} {d floor loss j cap : ℕ}
    (state : InheritedSingletonPosition origin initial current support w S d floor loss j cap)
    (threshold test : ℕ) (hTest : 1 ≤ test) (hCap : 0 < cap)
    (hSize : 4 ≤ initialᶜ.card) (hRate : j*(2*(initial.card+1)) ≤ cap*cap)
    (hInitial : current ⊆ initial) (hCurrent : current ⊆ support)
    (hCoreSupport : initialᶜ ⊆ support) (hw : w ∈ current)
    (hOdd : Odd (support \ current).card) (hWindow : floor+1+threshold ≤ d-2)
    (hRoom : 5*initial.card+cap+4+(loss+current.card+3) ≤ floor) :
    HasAlmostOverfullRecord (univ.filter (fun v => 0 < S.record initial j v)) d test (S.record initial j) ∨
      S.graph.degree w ≤ 1 ∨
      ∃ T : VirtualTrimmingState V,
        HasTrimmingRoundWithoutCleanup S T initial current {w} support d floor test j cap ∧
        InheritedSingletonPosition origin initial current support w T (d-2) floor loss (j+1) cap ∧
        nextTrimmingExceptional current (univ.filter (fun v => 0 < T.record initial (j+1) v))
          (T.record initial (j+1)) (d-2) threshold =
            current ∩ univ.filter (fun v => 0 < T.record initial (j+1) v) ∧
        T.graph.degree w+1 ≤ S.graph.degree w := by
  have hWindow' : floor+3 ≤ d := by omega
  rcases state.select_or_stop test hTest hCap hSize hRate hInitial hCurrent hCoreSupport hw
    hWindow' hRoom with hStop | hSmall | ⟨hSupp,hNo,hCore,hSelect⟩
  · exact Or.inl hStop
  · exact Or.inr (Or.inl hSmall)
  obtain ⟨R⟩ := hSelect
  let degree := S.record initial j
  let P := R.round.words.prescribedGraph
  let T := S.advance j P (R.round.words.degreeCredit R.round.omitted) R.freeEndpoints
  let record := T.record initial (j+1)
  let alive := univ.filter (fun v => 0 < record v)
  have hRead (v : V) : record v ≤ d-2 ∧
      record v+(2-R.round.words.degreeCredit R.round.omitted v) = degree v := by
    have h := (R.advance_without_cleanup S.prescribed S.credit (fun _ => rfl) hCore).2 v
    simpa only [degree,record,T,P,VirtualTrimmingState.record,VirtualTrimmingState.advance,
      Function.update_self] using h
  have hDegree (v : V) : T.graph.degree v+P.degree v = S.graph.degree v := by
    change (sdiff S.graph P).degree v+P.degree v = S.graph.degree v
    simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le S.graph P R.round.words.prescribedGraph_le v
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
  have hOdd' : Odd ((univ.filter (fun v => 0 < degree v)) \ current).card := by
    rw [show univ.filter (fun v => 0 < degree v) = support from hSupp]
    exact hOdd
  have hProgress : T.graph.degree w+1 ≤ S.graph.degree w := by
    have h : 1 ≤ P.degree w := R.active_progress (Or.inr hOdd') w (mem_singleton_self _)
    have hn := hDegree w
    omega
  have hInactive (v : V) (hv : v ∈ current) (hn : v ≠ w) :
      floor+2*(T.graph.neighborFinset v ∩ {w}).card+min (current.card+1) (T.graph.degree w) ≤
        T.graph.degree v+loss+2*(origin.neighborFinset v ∩ {w}).card+
          min (current.card+1) (origin.degree w) := by
    have hEdges : (T.graph.neighborFinset v ∩ {w}).card+(P.neighborFinset v ∩ {w}).card =
        (S.graph.neighborFinset v ∩ {w}).card :=
      neighbour_finset_inter_add_sdiff S.graph P R.round.words.prescribedGraph_le {w} v
    have hMono : T.graph.degree w ≤ S.graph.degree w :=
      (Nat.le_add_right _ _).trans_eq (hDegree w)
    have hFuel := min_le_min_left (current.card+1) hMono
    have hOld := state.inactive_balance v hv hn
    have hNow := hDegree v
    by_cases hPos : 0 < P.degree v
    · obtain ⟨hChoice,hInternal⟩ := R.inactive_singleton_degree_charge hv hn
      rcases hChoice hPos with hEdge | ⟨hI,hOne⟩
      · have hPair : 1 ≤ (P.neighborFinset v ∩ {w}).card :=
          card_pos.mpr ⟨w,mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr hEdge.symm,mem_singleton_self _⟩⟩
        have hTwo := R.round.words.prescribed_graph_degree_le v
        rw [if_pos (hInitial hv)] at hTwo
        change P.degree v ≤ 2 at hTwo
        omega
      · obtain ⟨hSmall,hOneW⟩ := hInternal hI
        have hBefore : min (current.card+1) (S.graph.degree w) = S.graph.degree w :=
          min_eq_right hSmall
        have hAfter : min (current.card+1) (T.graph.degree w) = T.graph.degree w :=
          min_eq_right (hMono.trans hSmall)
        have hD := hDegree w
        change P.degree v = 1 at hOne
        change P.degree w = 1 at hOneW
        rw [hBefore] at hOld
        rw [hAfter]
        omega
    · omega
  have hSurvive (v : V) (hv : v ∈ support) (hn : v ≠ w) : 0 < record v := by
    by_cases hc : v ∈ current
    · have h := hInactive v hc hn
      have hCoin : (origin.neighborFinset v ∩ {w}).card ≤ 1 := by
        rw [←card_singleton w]
        exact card_le_card inter_subset_right
      have hCap := min_le_left (current.card+1) (origin.degree w)
      change 0 < auxiliaryPhysicalDegree T.graph initial T.prescribed T.credit (j+1) v
      rw [auxiliaryPhysicalDegree,if_pos (hInitial hc)]
      omega
    · have h := single_le_sum (f := fun u => d-2-record u) (fun _ _ => Nat.zero_le _)
        (mem_sdiff.mpr ⟨hv,hc⟩)
      omega
  have hErase : alive.erase w = support.erase w := by
    ext v
    simp only [mem_erase]
    constructor
    · rintro ⟨hne,hp⟩
      have hu := (mem_filter.mp hp).2
      have hr := (hRead v).2
      have hm : v ∈ univ.filter (fun x => 0 < degree x) :=
        mem_filter.mpr ⟨mem_univ _,by omega⟩
      exact ⟨hne,hSupp ▸ hm⟩
    · exact fun ⟨hn,hs⟩ => ⟨hn,mem_filter.mpr ⟨mem_univ _,hSurvive v hs hn⟩⟩
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
  refine Or.inr (Or.inr ⟨T,⟨hNo,R,rfl⟩,
    ⟨fun v => (hRead v).1,hErase,hUpper,hMass,hInactive,hFree,hFLoad⟩,?_,hProgress⟩)
  apply le_antisymm (filter_subset _ _)
  intro v hv
  have h := hUpper v (mem_inter.mp hv).1
  exact mem_filter.mpr ⟨hv,by change threshold ≤ d-2-record v; omega⟩

theorem CriticalTrimmingEntry.start_inherited_singleton
    {S : VirtualTrimmingState V} {initial current : Finset V} {w : V}
    {d floor loss j cap : ℕ}
    (E : CriticalTrimmingEntry S.graph initial current {w} (S.record initial j) d floor loss)
    (hSize : ∀ i < j,(S.used i).card ≤ 2*(initial.card+1))
    (hLoad : ∀ v,projectionLoad (range j) S.used v ≤ cap) :
    InheritedSingletonPosition S.graph initial current (univ.filter (fun v => 0 < S.record initial j v))
      w S d floor loss j cap := by
  refine ⟨E.degree_cap,rfl,E.exceptional_upper,E.ordinary_deficit,?_,hSize,hLoad⟩
  intro v hv _
  have hI := E.current_initial hv
  have hPos := E.current_positive v hv
  rw [E.degree_exact v hI] at hPos
  exact Nat.add_le_add_right (Nat.add_le_add_right (E.degree_floor v hI hPos) _) _

structure InheritedSingletonHistory (start : VirtualTrimmingState V)
    (initial current support : Finset V) (w : V)
    (D floor loss threshold test j cap m : ℕ) where
  states : ℕ → VirtualTrimmingState V
  starts : states 0 = start
  rounds : ∀ i < m,HasTrimmingRoundWithoutCleanup (states i) (states (i+1))
    initial current {w} support (D-2*i) floor test (j+i) cap
  positions : ∀ i ≤ m,InheritedSingletonPosition start.graph initial current support w
    (states i) (D-2*i) floor loss (j+i) cap
  exceptional : ∀ i < m,
    let record := (states (i+1)).record initial (j+(i+1))
    let alive := univ.filter (fun v => 0 < record v)
    nextTrimmingExceptional current alive record (D-2*(i+1)) threshold = current ∩ alive
  active_drop : ∀ i < m,(states (i+1)).graph.degree w+1 ≤ (states i).graph.degree w

set_option maxHeartbeats 4200000 in
/-- Iterate the singleton up to the first almost-overfull record,
degree at most one, or the short limit. All proper rounds retain
their exact prescription and the accumulated projection budget. -/
theorem exists_inherited_singleton_trimming_history
    (start : VirtualTrimmingState V) (initial current support : Finset V) (w : V)
    (D floor loss threshold test j cap total : ℕ)
    (hEntry : InheritedSingletonPosition start.graph initial current support w start D floor loss j cap)
    (hTest : 1 ≤ test) (hCap : 0 < cap) (hSize : 4 ≤ initialᶜ.card)
    (hRate : (j+total)*(2*(initial.card+1)) ≤ cap*cap)
    (hInitial : current ⊆ initial) (hCurrent : current ⊆ support)
    (hCoreSupport : initialᶜ ⊆ support) (hw : w ∈ current) (hOdd : Odd (support \ current).card)
    (hWindow : floor+1+threshold ≤ D-2*total)
    (hRoom : 5*initial.card+cap+4+(loss+current.card+3) ≤ floor) :
    ∃ m ≤ total,∃ H : InheritedSingletonHistory start initial current support w
      D floor loss threshold test j cap m,
      m = total ∨ (H.states m).graph.degree w ≤ 1 ∨
        HasAlmostOverfullRecord (univ.filter (fun v => 0 < (H.states m).record initial (j+m) v))
          (D-2*m) test ((H.states m).record initial (j+m)) := by
  let History (i : ℕ) := InheritedSingletonHistory start initial current support w
    D floor loss threshold test j cap i
  let stopped (i : ℕ) (H : History i) :=
    (H.states i).graph.degree w ≤ 1 ∨
      HasAlmostOverfullRecord (univ.filter (fun v => 0 < (H.states i).record initial (j+i) v))
        (D-2*i) test ((H.states i).record initial (j+i))
  have hZero : Nonempty (History 0) := by
    refine ⟨⟨fun _ => start,rfl,by simp,?_,by simp,by simp⟩⟩
    intro i hi
    have he : i = 0 := by omega
    subst i
    simpa only [Nat.mul_zero,Nat.sub_zero,Nat.add_zero] using hEntry
  have hGrow (i : ℕ) (hi : i ≤ total) :
      (∃ m ≤ i,∃ H : History m,stopped m H) ∨ Nonempty (History i) := by
    induction i with
    | zero => exact Or.inr hZero
    | succ i ih =>
      have hi' : i ≤ total := (Nat.le_succ _).trans hi
      have hD : D-2*i-2 = D-2*(i+1) := by rw [Nat.mul_succ,Nat.sub_sub]
      have hIndex : j+i+1 = j+(i+1) := Nat.add_assoc _ _ _
      have hWindow' : floor+1+threshold ≤ (D-2*i)-2 := by
        rw [hD]
        exact hWindow.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 hi) _)
      rcases ih hi' with ⟨m,hm,H,hStop⟩ | hHistory
      · exact Or.inl ⟨m,hm.trans (Nat.le_succ _),H,hStop⟩
      obtain ⟨H⟩ := hHistory
      have hState := H.positions i le_rfl
      have hr := (Nat.mul_le_mul_right (2*(initial.card+1))
        (Nat.add_le_add_left hi' j)).trans hRate
      rcases hState.continue_or_stop threshold test hTest hCap hSize hr hInitial hCurrent
        hCoreSupport hw hOdd hWindow' hRoom with hStop | hSmall | ⟨T,hStep,hNext,hExceptional,hDrop⟩
      · exact Or.inl ⟨i,Nat.le_succ _,H,Or.inr hStop⟩
      · exact Or.inl ⟨i,Nat.le_succ _,H,Or.inl hSmall⟩
      let states := Function.update H.states (i+1) T
      have hPrior (k : ℕ) (hk : k ≤ i) : states k = H.states k :=
        Function.update_of_ne (by omega) _ _
      have hLast : states (i+1) = T := Function.update_self _ _ _
      rw [hD,hIndex] at hNext hExceptional
      refine Or.inr ⟨⟨states,(hPrior 0 (Nat.zero_le _)).trans H.starts,?_,?_,?_,?_⟩⟩
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
        dsimp only
        by_cases he : k = i
        · subst k
          rwa [hLast]
        · have hk' : k < i := by omega
          rw [hPrior (k+1) (by omega)]
          exact H.exceptional k hk'
      · intro k hk
        by_cases he : k = i
        · subst k
          rwa [hPrior i le_rfl,hLast]
        · have hk' : k < i := by omega
          rw [hPrior k hk'.le,hPrior (k+1) (by omega)]
          exact H.active_drop k hk'
  rcases hGrow total le_rfl with ⟨m,hm,H,hStop⟩ | hFull
  · exact ⟨m,hm,H,Or.inr hStop⟩
  · obtain ⟨H⟩ := hFull
    exact ⟨total,le_rfl,H,Or.inl rfl⟩

/-- Begin the singleton run at a certified critical entry. -/
theorem CriticalTrimmingEntry.exists_inherited_singleton_run
    {start : VirtualTrimmingState V} {initial current : Finset V} {w : V}
    {D floor loss j cap : ℕ}
    (E : CriticalTrimmingEntry start.graph initial current {w} (start.record initial j) D floor loss)
    (threshold test total : ℕ) (hTest : 1 ≤ test) (hCap : 0 < cap) (hSize : 4 ≤ initialᶜ.card)
    (hRate : (j+total)*(2*(initial.card+1)) ≤ cap*cap)
    (hWindow : floor+1+threshold ≤ D-2*total)
    (hRoom : 5*initial.card+cap+4+(loss+current.card+3) ≤ floor)
    (hSize₀ : ∀ i < j,(start.used i).card ≤ 2*(initial.card+1))
    (hLoad₀ : ∀ v,projectionLoad (range j) start.used v ≤ cap) :
    let support := univ.filter (fun v => 0 < start.record initial j v)
    ∃ m ≤ total,∃ H : InheritedSingletonHistory start initial current support w
      D floor loss threshold test j cap m,
      m = total ∨ (H.states m).graph.degree w ≤ 1 ∨
        HasAlmostOverfullRecord (univ.filter (fun v => 0 < (H.states m).record initial (j+m) v))
          (D-2*m) test ((H.states m).record initial (j+m)) := by
  intro support
  have hCurrent : current ⊆ support := fun v hv =>
    mem_filter.mpr ⟨mem_univ _,E.current_positive v hv⟩
  have hCore : initialᶜ ⊆ support := fun v hv =>
    mem_filter.mpr ⟨mem_univ _,by have h := E.core_room v (mem_compl.mp hv); omega⟩
  exact exists_inherited_singleton_trimming_history start initial current support w D floor loss
    threshold test j cap total (E.start_inherited_singleton hSize₀ hLoad₀)
    hTest hCap hSize hRate E.current_initial hCurrent hCore (E.active_current (mem_singleton_self _))
    E.ordinary_odd hWindow hRoom

set_option maxHeartbeats 3500000 in
/-- At either exhaustion degree, recover the even support and the
same odd ordinary side. The degree-one case uses the actual final
cleanup, with no additional trimming layer or new projection usage. -/
theorem InheritedSingletonPosition.cleanup_at_exhaustion
    {origin : SimpleGraph V} {initial current support : Finset V} {w : V}
    {S : VirtualTrimmingState V} {d floor loss j cap : ℕ}
    (state : InheritedSingletonPosition origin initial current support w S d floor loss j cap)
    (hInitial : current ⊆ initial) (hCurrent : current ⊆ support)
    (hCoreSupport : initialᶜ ⊆ support) (hw : w ∈ current)
    (hOdd : Odd support.card) (hD : 3 ≤ d)
    (hFloor : loss+current.card+5 ≤ floor) (hStop : S.graph.degree w ≤ 1) :
    ∃ T : SimpleGraph V,
      DeletionRun {w} S.graph T ∧
      let next := auxiliaryPhysicalDegree T initial S.prescribed S.credit j
      let alive := univ.filter (fun v => 0 < next v)
      (∀ v,(sdiff S.graph T).degree v ≤ 1 ∧
        next v+(sdiff S.graph T).degree v = S.record initial j v) ∧
      alive = support.erase w ∧ current ∩ alive = current.erase w ∧
      Even alive.card ∧ alive \ current.erase w = support \ current ∧
      (∑ v ∈ alive \ current.erase w,(d-next v)) ≤ 2 := by
  let alive := univ.filter (fun v => 0 < S.record initial j v)
  have hW : S.record initial j w = S.graph.degree w := by
    simp only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos (hInitial hw)]
  have hMem (v : V) (hne : v ≠ w) : v ∈ alive ↔ v ∈ support := by
    have h := Finset.ext_iff.mp state.support_except v
    exact ⟨fun hp => (mem_erase.mp (h.mp (mem_erase.mpr ⟨hne,hp⟩))).2,
      fun hp => (mem_erase.mp (h.mpr (mem_erase.mpr ⟨hne,hp⟩))).2⟩
  have hEven : Even (support.erase w).card := by
    obtain ⟨k,hk⟩ := hOdd
    have h := card_erase_add_one (hCurrent hw)
    exact ⟨k,by omega⟩
  have hSet : current ∩ support.erase w = current.erase w := by
    ext v
    simp only [mem_inter,mem_erase]
    exact ⟨fun ⟨hv,hn,_⟩ => ⟨hn,hv⟩,fun ⟨hn,hv⟩ => ⟨hv,hn,hCurrent hv⟩⟩
  have hCut : support.erase w \ current.erase w = support \ current := by
    ext v
    simp only [mem_sdiff,mem_erase]
    by_cases he : v = w <;> simp [he,hw]
  by_cases hZero : S.graph.degree w = 0
  · have hAlive : alive = support.erase w := by
      ext v
      by_cases he : v = w
      · subst v
        simp [alive,hW,hZero]
      · have h := hMem v he
        exact h.trans ⟨fun hp => mem_erase.mpr ⟨he,hp⟩,fun hp => (mem_erase.mp hp).2⟩
    have hBudget : (∑ v ∈ alive \ current.erase w,(d-S.record initial j v)) ≤ 2 := by
      rw [hAlive,hCut]
      exact state.ordinary_deficit.trans (by decide)
    refine ⟨S.graph,DeletionRun.refl _,?_,hAlive,?_,?_,?_,hBudget⟩
    · intro v
      have h : (sdiff S.graph S.graph).degree v = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hPos
        obtain ⟨x,hx⟩ := ((sdiff S.graph S.graph).degree_pos_iff_exists_adj v).mp hPos
        exact hx.2 hx.1
      simp only [h,Nat.zero_le,add_zero,and_true,VirtualTrimmingState.record]
    · change current ∩ alive = current.erase w
      rwa [hAlive]
    · change Even alive.card
      rwa [hAlive]
    · change alive \ current.erase w = support \ current
      rwa [hAlive]
  have hOne : S.graph.degree w = 1 := by omega
  have hAlive : alive = support := by
    ext v
    by_cases he : v = w
    · subst v
      exact iff_of_true (mem_filter.mpr ⟨mem_univ _,by rw [hW,hOne]; decide⟩) (hCurrent hw)
    · exact hMem v he
  have hCore (v : V) (hv : v ∉ initial) : 0 < S.record initial j v := by
    have hm : v ∈ alive := hAlive.symm ▸ hCoreSupport (mem_compl.mpr hv)
    exact (mem_filter.mp hm).2
  have hInactive (v : V) (hv : v ∈ current) (hn : v ≠ w) : 2 ≤ S.graph.degree v := by
    have h := state.inactive_floor v hv hn
    omega
  have hNeighbours := exhausted_singleton_neighbour_has_room S.graph initial current w
    S.prescribed S.credit j d hD hInitial hCore hInactive (by
      change (∑ v ∈ alive \ current,(d-S.record initial j v)) ≤ 1
      rw [hAlive]
      exact state.ordinary_deficit)
  have hLive : current ⊆ alive := by rw [hAlive]; exact hCurrent
  have hOdd' : Odd alive.card := by rwa [hAlive]
  have hMass : (∑ v ∈ alive \ current,(d-S.record initial j v)) ≤ 1 := by
    rw [hAlive]
    exact state.ordinary_deficit
  obtain ⟨x,T,hAdj,hT,hRun,hExact,hErased,hSet',hEven',hCut',hBudget⟩ :=
    virtual_cleanup_of_exhausted_singleton S.graph initial current hInitial w hw
      S.prescribed S.credit j d hOne hLive hOdd' hNeighbours state.degree_bound hMass
  refine ⟨T,hRun,?_,?_,hSet',hEven',?_,hBudget⟩
  · intro v
    have hDegree : T.degree v+(if v=w ∨ v=x then 1 else 0) = S.graph.degree v := by
      rw [hT]
      exact WeakVALSingleEdgeDeletion.degree_delete_add S.graph hAdj v
    have hDiff : T.degree v+(sdiff S.graph T).degree v = S.graph.degree v := by
      simpa only [add_comm,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le S.graph T (DeletionRun.le_source hRun) v
    have he : (sdiff S.graph T).degree v = if v=w ∨ v=x then 1 else 0 := by omega
    rw [he]
    exact ⟨by split <;> decide,hExact v⟩
  · change _ = alive.erase w at hErased
    rwa [hAlive] at hErased
  · change _ = alive \ current at hCut'
    rwa [hAlive] at hCut'

/-- From either kind of critical entry, build the corresponding
inherited history to its next boundary. All rounds in that history
use the original index and the original projection arrays. -/
theorem CriticalTrimmingEntry.exists_inherited_run
    {start : VirtualTrimmingState V} {initial current active : Finset V}
    {D floor loss j cap : ℕ}
    (E : CriticalTrimmingEntry start.graph initial current active (start.record initial j) D floor loss)
    (threshold test total : ℕ) (hTest : 1 ≤ test) (hCap : 0 < cap) (hSize : 4 ≤ initialᶜ.card)
    (hRate : (j+total)*(2*(initial.card+1)) ≤ cap*cap)
    (hEntry : total+6+loss ≤ floor) (hWindow : floor+1+threshold ≤ D-2*total)
    (hRoom : 5*initial.card+cap+4+(loss+current.card+4) ≤ floor)
    (hSize₀ : ∀ i < j,(start.used i).card ≤ 2*(initial.card+1))
    (hLoad₀ : ∀ v,projectionLoad (range j) start.used v ≤ cap) :
    let support := univ.filter (fun v => 0 < start.record initial j v)
    ∃ m ≤ total,
      (∃ w,active = {w} ∧
        ∃ H : InheritedSingletonHistory start initial current support w D floor loss threshold test j cap m,
          m = total ∨ (H.states m).graph.degree w ≤ 1 ∨
            HasAlmostOverfullRecord (univ.filter (fun v => 0 < (H.states m).record initial (j+m) v))
              (D-2*m) test ((H.states m).record initial (j+m))) ∨
      (active.card = 2 ∧
        ∃ H : InheritedPairHistory start initial current active support D floor loss threshold test j cap total m,
          m = total ∨ HasAlmostOverfullRecord support (D-2*m) test ((H.states m).record initial (j+m))) := by
  intro support
  rcases E.active_size with hOne | hTwo
  · obtain ⟨w,rfl⟩ := card_eq_one.mp hOne
    have hReserve : 5*initial.card+cap+4+(loss+current.card+3) ≤ floor := by omega
    obtain ⟨m,hm,H,hEnd⟩ := E.exists_inherited_singleton_run threshold test total hTest hCap hSize
      hRate hWindow hReserve hSize₀ hLoad₀
    exact ⟨m,hm,Or.inl ⟨w,rfl,H,hEnd⟩⟩
  · have hReserve : 5*initial.card+cap+4+(loss+4) ≤ floor := by omega
    obtain ⟨m,hm,H,hEnd⟩ := E.exists_inherited_pair_run threshold test total hTest hCap hSize
      hRate hTwo hEntry hWindow hReserve hSize₀ hLoad₀
    exact ⟨m,hm,Or.inr ⟨hTwo,H,hEnd⟩⟩

set_option maxHeartbeats 2900000 in
/-- The weak degree-sum bound persists over a singleton history.
Only one endpoint of a surviving edge can use the per-round debit
of the singleton. Inactive exceptional losses have a fixed bound. -/
theorem InheritedSingletonHistory.weak_degree_sum
    {start : VirtualTrimmingState V} {initial current support : Finset V} {w : V}
    {D floor loss threshold test j cap m : ℕ}
    (H : InheritedSingletonHistory start initial current support w D floor loss threshold test j cap m)
    (hInitial : current ⊆ initial) (hw : w ∈ current)
    (hCore : initialᶜ ⊆ support) (budget : ℕ)
    (hEntry : ∀ u v,start.graph.Adj u v →
      D ≤ start.record initial j u+start.record initial j v+budget) :
    ∀ u v,(H.states m).graph.Adj u v →
      D-2*m ≤ (H.states m).record initial (j+m) u+(H.states m).record initial (j+m) v+
        budget+2*(loss+current.card+4) := by
  have hPrefix (i : ℕ) (hi : i ≤ m) :
      (H.states i).graph ≤ start.graph ∧
        start.graph.degree w ≤ (H.states i).graph.degree w+2*i := by
    induction i with
    | zero => rw [H.starts]; exact ⟨le_rfl,by simp⟩
    | succ i ih =>
      have hi' : i < m := by omega
      obtain ⟨hG,hDegree⟩ := ih hi'.le
      obtain ⟨_,R,hNext⟩ := H.rounds i hi'
      have hTwo := R.round.words.prescribed_graph_degree_le w
      rw [if_pos (hInitial hw)] at hTwo
      have hStep : (H.states (i+1)).graph.degree w+R.round.words.prescribedGraph.degree w =
          (H.states i).graph.degree w := by
        rw [hNext]
        change (sdiff (H.states i).graph R.round.words.prescribedGraph).degree w+
          R.round.words.prescribedGraph.degree w = (H.states i).graph.degree w
        simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
          MaximumMatching.degree_sdiff_add_of_le (H.states i).graph R.round.words.prescribedGraph
            R.round.words.prescribedGraph_le w
      refine ⟨?_,by omega⟩
      rw [hNext]
      exact fun u v he => hG he.1
  have first := H.positions 0 (Nat.zero_le _)
  have last := H.positions m le_rfl
  have hActive : start.record initial j w ≤ (H.states m).record initial (j+m) w+2*m := by
    simp only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos (hInitial hw)]
    exact (hPrefix m le_rfl).2
  have hInactive (x : V) (hx : x ∈ current) (hne : x ≠ w) :
      start.record initial j x ≤ (H.states m).record initial (j+m) x+loss+current.card+4 := by
    have hBefore := first.exceptional_upper x hx
    have hAfter := last.inactive_floor x hx hne
    have hI := hInitial hx
    rw [H.starts,Nat.add_zero,VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hI] at hBefore
    simp only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hI]
    omega
  have hOrd (x : V) (hx : x ∉ current) (hPos : 0 < (H.states m).graph.degree x) :
      D-2*m ≤ (H.states m).record initial (j+m) x+1 := by
    have hn : x ≠ w := fun h => hx (h.symm ▸ hw)
    have hs : x ∈ support := by
      by_cases hI : x ∈ initial
      · have hRecord : 0 < (H.states m).record initial (j+m) x := by
          simpa only [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos hI] using hPos
        have hm : x ∈ (univ.filter (fun v => 0 < (H.states m).record initial (j+m) v)).erase w :=
          mem_erase.mpr ⟨hn,mem_filter.mpr ⟨mem_univ _,hRecord⟩⟩
        rw [last.support_except] at hm
        exact (mem_erase.mp hm).2
      · exact hCore (mem_compl.mpr hI)
    have he := single_le_sum (f := fun v => D-2*m-(H.states m).record initial (j+m) v)
      (fun _ _ => Nat.zero_le _) (mem_sdiff.mpr ⟨hs,hx⟩)
    have hm := last.ordinary_deficit
    omega
  intro u v hEdge
  by_cases hBoth : u ∈ current ∧ v ∈ current
  · have he := hEntry u v ((hPrefix m le_rfl).1 hEdge)
    by_cases hu : u = w
    · subst u
      have h := hInactive v hBoth.2 hEdge.ne.symm
      omega
    · by_cases hv : v = w
      · subst v
        have h := hInactive u hBoth.1 hu
        omega
      · have hU := hInactive u hBoth.1 hu
        have hV := hInactive v hBoth.2 hv
        omega
  rcases not_and_or.mp hBoth with hu | hv
  · have h := hOrd u hu (((H.states m).graph.degree_pos_iff_exists_adj _).mpr ⟨v,hEdge⟩)
    omega
  · have h := hOrd v hv (((H.states m).graph.degree_pos_iff_exists_adj _).mpr ⟨u,hEdge.symm⟩)
    omega

end OverfullWork.CMSTrimmingRound
