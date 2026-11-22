module

public import OverfullWork.CMSOperation41OriginalPhaseRun

@[expose] public section


/-! At the first critical choice the surviving exceptional vertices
are high enough in absolute degree to restart the selector, but low
enough to stay exceptional in the shorter range. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

structure CriticalTrimmingEntry (T : SimpleGraph V) [DecidableRel T.Adj]
    (initial current active : Finset V) (degree : V → ℕ) (d floor loss : ℕ) : Prop where
  current_initial : current ⊆ initial
  current_positive : ∀ v ∈ current,0 < degree v
  active_current : active ⊆ current
  active_size : active.card = 1 ∨ active.card = 2
  active_parity : Even (univ.filter (fun v => 0 < degree v)).card ↔ active.card = 2
  active_minimum : (Even current.card ∧ ∃ a ∈ current,active = {a} ∧
      ∀ v ∈ current,degree a ≤ degree v) ∨
    (Odd current.card ∧ ∃ a ∈ current,∃ b ∈ current,a ≠ b ∧ active = {a,b} ∧
      (∀ v ∈ current,degree a ≤ degree v) ∧ ∀ v ∈ current,v ≠ a → degree b ≤ degree v)
  exceptional_upper : ∀ v ∈ current,degree v < floor+2
  ordinary_odd : Odd ((univ.filter (fun v => 0 < degree v)) \ current).card
  ordinary_deficit : (∑ v ∈ (univ.filter (fun v => 0 < degree v)) \ current,(d-degree v)) ≤ 1
  degree_cap : ∀ v,degree v ≤ d
  degree_exact : ∀ v ∈ initial,degree v = T.degree v
  core_room : ∀ v,v ∉ initial → 2 ≤ degree v
  degree_floor : ∀ v ∈ initial,0 < T.degree v → floor ≤ T.degree v+loss

set_option maxHeartbeats 3000000 in
/-- Resolve the first boundary of the original phase. A critical
choice comes with the actual cleaned graph and a lower bound at
every positive exceptional vertex, including the newly chosen active
ones. The loss includes the cleanup in the switching round. -/
theorem OriginalTrimmingHistory.critical_entry_at_boundary
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial low : Finset V}
    {threshold floor cap test m : ℕ}
    (H : OriginalTrimmingHistory G initial low threshold floor cap test m) (limit : ℕ)
    (hEnd : H.AtBoundary limit)
    (hLow : low ⊆ initial) (hInd : G.IsIndepSet (low : Set V))
    (hOrd : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+threshold)
    (hFloor : ∀ v ∈ initial,v ∉ low → floor ≤ G.degree v)
    (hMargin : 5*initial.card+cap+4+(4*initial.card+2) ≤ floor)
    (hRange : floor+threshold+low.card ≤ G.maxDegree-2*m) :
    let d := G.maxDegree-2*m
    let loss := 3*low.card+initial.card+1
    m = limit ∨ HasAlmostOverfullRecord (univ.filter (fun v => 0 < H.degree m v)) d test (H.degree m) ∨
      ∃ T : SimpleGraph V,
        let cleaned := auxiliaryPhysicalDegree T initial H.prescribed H.credit m
        let support := univ.filter (fun v => 0 < cleaned v)
        let current := H.exceptional m ∩ support
        DeletionRun (H.exceptional m ∩ low) (H.graph m) T ∧
          (HasAlmostOverfullRecord support d test cleaned ∨
            ∃ A,CriticalTrimmingEntry T initial current A cleaned d floor loss) := by
  intro d loss
  rcases hEnd with hLimit | hStop | ⟨T,hRun,hOutcome⟩
  · exact Or.inl hLimit
  · exact Or.inr (Or.inl hStop)
  right
  right
  refine ⟨T,hRun,?_⟩
  rcases hOutcome with hStop | ⟨hEmpty,A,hA,hApos,hAsize,hParity,hUpper,hOdd,hDeficit,hMinimum⟩
  · exact Or.inl hStop
  right
  let W := H.exceptional m ∩ low
  let cleaned := auxiliaryPhysicalDegree T initial H.prescribed H.credit m
  let support := univ.filter (fun v => 0 < cleaned v)
  let current := H.exceptional m ∩ support
  have hSource : H.graph m ≤ G := by
    have h := virtual_trimming_prefix_le H.graph H.cleaned H.prescribed m
      (fun i hi => DeletionRun.le_source (H.cleanup i hi)) H.graph_next 0 m (Nat.zero_le _) le_rfl
    exact h.trans H.graph_zero.le
  have hW : (H.graph m).IsIndepSet (W : Set V) := by
    intro a ha b hb hne hab
    exact hInd (mem_inter.mp ha).2 (mem_inter.mp hb).2 hne (hSource hab)
  have hU : H.exceptional m ⊆ initial := by
    have h := trimming_exceptional_sets_antitone H.exceptional
      (fun i => univ.filter (fun v => 0 < H.degree i v)) H.degree G.maxDegree threshold m
      H.exceptional_next m le_rfl 0 (Nat.zero_le _)
    rwa [H.exceptional_zero] at h
  have hLe := DeletionRun.le_source hRun
  have hLoss (v : V) : (sdiff (H.graph m) T).degree v ≤ W.card := by
    have hBalance : T.degree v+(sdiff (H.graph m) T).degree v = (H.graph m).degree v := by
      simpa only [add_comm,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le (H.graph m) T hLe v
    have h := independent_auxiliary_preprocessing_degree_loss hRun hW v
    change (H.graph m).degree v ≤ T.degree v+W.card at h
    omega
  have hClean (v : V) : cleaned v = H.degree m v-(sdiff (H.graph m) T).degree v := by
    rw [H.degree_exact m le_rfl]
    exact auxiliary_physical_degree_after_cleanup (H.graph m) T initial H.prescribed H.credit m hLe v
  obtain ⟨hCore,hReserve⟩ := H.next_round_reserves hLow hInd hOrd hFloor hMargin hRange
  refine ⟨A,⟨inter_subset_left.trans hU,?_,hA,by omega,hParity,hMinimum,hUpper,hOdd,hDeficit,
    ?_,?_,?_,?_⟩⟩
  · intro v hv
    exact (mem_filter.mp (mem_inter.mp hv).2).2
  · intro v
    change cleaned v ≤ d
    rw [hClean]
    exact (Nat.sub_le _ _).trans (H.degree_bound m le_rfl v)
  · intro v hv
    simp only [auxiliaryPhysicalDegree,if_pos hv]
  · intro v hv
    change 2 ≤ cleaned v
    rw [hClean]
    have h := hCore v hv
    change W.card+2 ≤ H.degree m v at h
    have hC := hLoss v
    omega
  · intro v hv hp
    have hn : v ∉ W := by
      intro h
      have hm : v ∈ originalCleanActive low (H.exceptional m) T := mem_filter.mpr ⟨h,hp⟩
      rw [hEmpty] at hm
      exact notMem_empty _ hm
    have hOld := (hReserve v hv hn (hp.trans_le (degree_le_of_le hLe))).2
    have hWCard : W.card ≤ low.card := card_le_card inter_subset_right
    have hClean := independent_auxiliary_preprocessing_degree_loss hRun hW v
    change (H.graph m).degree v ≤ T.degree v+W.card at hClean
    change floor ≤ T.degree v+loss
    change floor ≤ (H.graph m).degree v+2*low.card+initial.card+1 at hOld
    dsimp only [loss]
    omega

set_option maxHeartbeats 2500000 in
/-- The first inherited active round is selected directly from the
cleaned graph at the boundary. Its exceptional degrees are below the
moving threshold, and the paper's two-matchings branch is available. -/
theorem CriticalTrimmingEntry.exists_first_selection
    {T : SimpleGraph V} [DecidableRel T.Adj] {initial current active : Finset V}
    {degree : V → ℕ} {d floor loss : ℕ}
    (E : CriticalTrimmingEntry T initial current active degree d floor loss)
    (test : ℕ) (hTest : 1 ≤ test)
    (used : ℕ → Finset V) (j cap k budget : ℕ)
    (hCap : 0 < cap) (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hSize : 4 ≤ initialᶜ.card)
    (hUpper : floor+3 ≤ d) (hProjection : 5*initial.card+k+4+loss ≤ floor)
    (hActive : 6+loss ≤ floor) :
    let support := univ.filter (fun v => 0 < degree v)
    HasAlmostOverfullRecord support d test degree ∨
      Nonempty (TrimmingStepSelection T initial current active degree d floor used j cap) := by
  intro support
  by_cases hStop : HasAlmostOverfullRecord support d test degree
  · exact Or.inl hStop
  have hCurrent : current ⊆ support := fun v hv => mem_filter.mpr ⟨mem_univ _,E.current_positive v hv⟩
  have hHigh (v : V) (hv : v ∈ active) : 6 ≤ T.degree v := by
    have hvU := E.active_current hv
    have hvI := E.current_initial hvU
    have hp := E.current_positive v hvU
    rw [E.degree_exact v hvI] at hp
    have h := E.degree_floor v hvI hp
    omega
  have hMode : (T.IsIndepSet (active : Set V) ∧
      ∀ w ∈ active,∀ x,T.Adj w x → PrunedCore.neighboursIn T active x < T.degree w) ∨
      (active.card = 2 ∧ ∀ w ∈ active,6 ≤ T.degree w) := by
    rcases E.active_size with hOne | hTwo
    · left
      refine ⟨?_,?_⟩
      · obtain ⟨v,hv⟩ := card_eq_one.mp hOne
        rw [hv,isIndepSet_iff]
        intro a ha b hb hne _
        have ha' : a = v := by simpa using ha
        have hb' : b = v := by simpa using hb
        exact hne (ha'.trans hb'.symm)
      · intro w hw x _
        have hN : PrunedCore.neighboursIn T active x ≤ active.card :=
          card_le_card (fun v hv => (mem_filter.mp hv).2)
        have h := hHigh w hw
        omega
    · exact Or.inr ⟨hTwo,hHigh⟩
  have hCore : initialᶜ ⊆ support := by
    intro v hv
    have h := E.core_room v (mem_compl.mp hv)
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  rcases exists_trimming_step_selection T initial current active E.current_initial E.active_current
      (fun v hv => by have h := hHigh v hv; omega) hMode degree d floor test (by omega)
      E.degree_cap E.degree_exact (fun v hv => by have h := E.exceptional_upper v hv; omega)
      hSize used j cap k budget hCap hUsed hTotal hCurrent hCore hTest hStop
      (fun v hv _ hp => by have h := E.degree_floor v hv hp; omega) with hRound | hSwitch
  · exact Or.inr hRound
  · have hZero : active.card = 0 := by rw [hSwitch.1,card_empty]
    rcases E.active_size with h | h <;> omega

/-- Introduce one prescription on the cleaned graph without adding
another cleanup. This is also the exact update for later inherited
rounds that have enough degree to avoid Algorithm 1. -/
theorem TrimmingStepSelection.advance_without_cleanup
    {T : SimpleGraph V} [tDec : DecidableRel T.Adj] {initial current active : Finset V}
    {degree : V → ℕ} {d floor j cap : ℕ} {used : ℕ → Finset V}
    (R : TrimmingStepSelection T initial current active degree d floor used j cap)
    (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ)
    (hExact : ∀ v,degree v = auxiliaryPhysicalDegree T initial P credit j v)
    (hCore : ∀ v,v ∉ initial → 2 ≤ degree v) :
    let P' := Function.update P j R.round.words.prescribedGraph
    let credit' := Function.update credit j (R.round.words.degreeCredit R.round.omitted)
    let next := sdiff T (P' j)
    let record := auxiliaryPhysicalDegree next initial P' credit' (j+1)
    (∀ i < j,P' i = P i ∧ credit' i = credit i) ∧
    ∀ v,record v ≤ d-2 ∧ record v+(2-credit' j v) = degree v := by
  cases Subsingleton.elim tDec (fun u v => Classical.propDecidable (T.Adj u v))
  intro P' credit' next record
  have hOld (i : ℕ) (hi : i < j) : P' i = P i ∧ credit' i = credit i :=
    ⟨Function.update_of_ne hi.ne _ _,Function.update_of_ne hi.ne _ _⟩
  have hNewP : P' j = R.round.words.prescribedGraph := Function.update_self _ _ _
  have hNewC : credit' j = R.round.words.degreeCredit R.round.omitted := Function.update_self _ _ _
  have hPrefix (v : V) : auxiliaryPhysicalDegree T initial P' credit' j v = degree v := by
    rw [hExact v]
    unfold auxiliaryPhysicalDegree
    split
    · rfl
    · congr 1
      apply sum_congr rfl
      intro i _
      rw [(hOld i.val i.isLt).1,(hOld i.val i.isLt).2]
  refine ⟨hOld,?_⟩
  intro v
  have hP : P' j ≤ sdiff T ⊥ := by rw [sdiff_bot,hNewP]; exact R.round.words.prescribedGraph_le
  have hDebit (x : V) (hx : x ∉ initial) : (P' j).degree x ≤ 2-credit' j x := by
    rw [hNewP,hNewC]
    exact R.round.words.prescribed_degree_le_core_debit R.round.omitted R.round.endpoints_retained hx
  have hNext := auxiliary_physical_degree_after_round T ⊥ initial P' credit' j bot_le hP hDebit v
  dsimp only at hNext
  have hZero (dec : DecidableRel (⊥ : SimpleGraph V).Adj) :
      (letI := dec; (⊥ : SimpleGraph V).degree v) = 0 := by
    rw [←card_neighborFinset_eq_degree,neighborFinset_bot,card_empty]
  rw [sdiff_bot,hPrefix] at hNext
  simp only [hZero,zero_add] at hNext
  have hCharge : (if v ∈ initial then (P' j).degree v else 2-credit' j v) = 2-credit' j v := by
    by_cases hv : v ∈ initial
    · rw [if_pos hv,hNewP,hNewC]
      have h := R.round.words.prescribed_degree_add_credit_on_exceptional R.round.omitted hv
      omega
    · rw [if_neg hv]
  rw [hCharge] at hNext
  have hRoom : 2-credit' j v ≤ degree v := by
    by_cases hv : v ∈ initial
    · rw [←hCharge,if_pos hv,hExact v,auxiliaryPhysicalDegree,if_pos hv]
      exact degree_le_of_le (by simpa only [sdiff_bot] using hP)
    · have h := hCore v hv
      omega
  have hCap : degree v+credit' j v ≤ d := by rw [hNewC]; exact R.round.degree_cap v
  change record v = _ at hNext
  omega

set_option maxHeartbeats 2600000 in
/-- Execute the first inherited round, unless the cleaned state is an
almost-overfull stop. All inherited vertices survive that first round
and the ordinary side retains its parity and deficiency bound. -/
theorem CriticalTrimmingEntry.exists_first_round
    {T : SimpleGraph V} [DecidableRel T.Adj] {initial current active : Finset V}
    {degree : V → ℕ} {d floor loss : ℕ}
    (E : CriticalTrimmingEntry T initial current active degree d floor loss)
    (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (threshold test : ℕ) (hTest : 1 ≤ test)
    (used : ℕ → Finset V) (j cap k budget : ℕ)
    (hExact : ∀ v,degree v = auxiliaryPhysicalDegree T initial P credit j v)
    (hCap : 0 < cap) (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hSize : 4 ≤ initialᶜ.card)
    (hWindow : floor+1+threshold ≤ d-2)
    (hProjection : 5*initial.card+k+4+loss ≤ floor) (hActive : 6+loss ≤ floor) :
    let support := univ.filter (fun v => 0 < degree v)
    HasAlmostOverfullRecord support d test degree ∨
      ∃ R : TrimmingStepSelection T initial current active degree d floor used j cap,
        let P' := Function.update P j R.round.words.prescribedGraph
        let credit' := Function.update credit j (R.round.words.degreeCredit R.round.omitted)
        let next := sdiff T (P' j)
        let record := auxiliaryPhysicalDegree next initial P' credit' (j+1)
        (∀ i < j,P' i = P i ∧ credit' i = credit i) ∧
        (∀ v,record v ≤ d-2 ∧ record v+(2-credit' j v) = degree v) ∧
        univ.filter (fun v => 0 < record v) = support ∧
        nextTrimmingExceptional current support record (d-2) threshold = current ∧
        (∑ v ∈ support \ current,(d-2-record v)) ≤ 1 ∧
        (∀ v ∈ current,record v+loss+2 ≥ floor) ∧
        (∀ w ∈ active,1 ≤ (P' j).degree w ∧ (P' j).degree w ≤ 2) ∧
        (active.card = 2 → ∀ w ∈ active,(P' j).degree w = 1) := by
  intro support
  rcases E.exists_first_selection test hTest used j cap k budget hCap hUsed hTotal hSize
    (by omega) hProjection hActive with hStop | hRound
  · exact Or.inl hStop
  obtain ⟨R⟩ := hRound
  right
  let P' := Function.update P j R.round.words.prescribedGraph
  let credit' := Function.update credit j (R.round.words.degreeCredit R.round.omitted)
  let next := sdiff T (P' j)
  let record := auxiliaryPhysicalDegree next initial P' credit' (j+1)
  have hP : P' j = R.round.words.prescribedGraph := Function.update_self _ _ _
  have hCredit : credit' j = R.round.words.degreeCredit R.round.omitted := Function.update_self _ _ _
  obtain ⟨hPrefix,hRecord⟩ := R.advance_without_cleanup P credit hExact E.core_room
  change (∀ i < j,P' i = P i ∧ credit' i = credit i) at hPrefix
  change (∀ v,record v ≤ d-2 ∧ record v+(2-credit' j v) = degree v) at hRecord
  have hMass : (∑ v ∈ support \ current,(d-2-record v)) ≤ 1 := by
    have h := ordinary_deficit_balance_after_trimming_round (support \ current) degree record (fun _ => 0)
      (credit' j) d (by omega) (fun v _ => E.degree_cap v) (fun v _ => (hRecord v).1)
      (fun v _ => by rw [hCredit]; exact R.round.words.degree_credit_le_two R.round.omitted v)
      (fun v _ => by simpa only [add_zero] using (hRecord v).2)
    have hm := E.ordinary_deficit
    change (∑ v ∈ support \ current,(d-degree v)) ≤ 1 at hm
    simp only [sum_const_zero,add_zero] at h
    omega
  have hOldHigh (v : V) (hv : v ∈ current) : floor ≤ degree v+loss := by
    have hvI := E.current_initial hv
    have hp := E.current_positive v hv
    rw [E.degree_exact v hvI] at hp ⊢
    exact E.degree_floor v hvI hp
  have hNewFloor (v : V) (hv : v ∈ current) : floor ≤ record v+loss+2 := by
    have h := hOldHigh v hv
    have hn := (hRecord v).2
    omega
  have hNewPos (v : V) (hv : v ∈ support) : 0 < record v := by
    by_cases he : v ∈ current
    · have h := hNewFloor v he
      omega
    · have h : d-2-record v ≤ ∑ x ∈ support \ current,(d-2-record x) :=
        single_le_sum (f := fun x => d-2-record x) (fun _ _ => Nat.zero_le _) (mem_sdiff.mpr ⟨hv,he⟩)
      omega
  have hSupport : univ.filter (fun v => 0 < record v) = support := by
    ext v
    constructor
    · intro h
      have hp := (mem_filter.mp h).2
      have hn := (hRecord v).2
      exact mem_filter.mpr ⟨mem_univ _,by omega⟩
    · exact fun h => mem_filter.mpr ⟨mem_univ _,hNewPos v h⟩
  have hExceptional : nextTrimmingExceptional current support record (d-2) threshold = current := by
    apply le_antisymm ((filter_subset _ _).trans inter_subset_left)
    intro v hv
    have hn := (hRecord v).2
    have hu := E.exceptional_upper v hv
    exact mem_filter.mpr ⟨mem_inter.mpr ⟨hv,mem_filter.mpr ⟨mem_univ _,E.current_positive v hv⟩⟩,by omega⟩
  have hHigh (v : V) (hv : v ∈ active) : 6 ≤ T.degree v := by
    have hc := E.active_current hv
    have h := hOldHigh v hc
    rw [E.degree_exact v (E.current_initial hc)] at h
    omega
  refine ⟨R,hPrefix,hRecord,hSupport,hExceptional,hMass,hNewFloor,?_,?_⟩
  · intro w hw
    change 1 ≤ (P' j).degree w ∧ (P' j).degree w ≤ 2
    rw [hP]
    have hBound := R.round.words.prescribed_graph_degree_le w
    rw [if_pos (E.current_initial (E.active_current hw))] at hBound
    exact ⟨R.active_progress (Or.inr E.ordinary_odd) w hw,hBound⟩
  · intro h w hw
    change (P' j).degree w = 1
    rw [hP]
    exact R.pair_progress h hHigh w hw

omit [Fintype V] [DecidableEq V] in
/-- Uniform room for the complete short phase, including internal
singleton charges, one final singleton edge and the later pair.
These inequalities use the same integer round limits as the selector. -/
theorem critical_phase_rounded_reserves (n D exceptional : ℕ) (η : ℝ)
    (hη : 0 ≤ η) (hSmall : η ≤ 1/64) (hShift : 64 ≤ η*(n:ℝ))
    (hDense : 24*(η*(n:ℝ)) ≤ (D:ℝ)) (hFew : (exceptional:ℝ) ≤ η^2*(n:ℝ)) :
    let shift := η*(n:ℝ)
    let floor := ⌊(D:ℝ)/3-shift⌋₊
    let short := ⌊(D:ℝ)/3-2*shift⌋₊
    let threshold := ⌈shift⌉₊
    let cap := ⌊shift⌋₊
    let loss := 5*exceptional+12
    floor+1+threshold ≤ D-2*short ∧ short+6+loss ≤ floor ∧
      5*exceptional+cap+4+loss ≤ floor := by
  intro shift floor short threshold cap loss
  have hFew' : (exceptional:ℝ) ≤ shift/64 := by
    have h := mul_le_mul_of_nonneg_right hSmall (mul_nonneg hη (Nat.cast_nonneg (α := ℝ) n))
    dsimp only [shift]
    nlinarith only [h,hFew]
  have hLoss : (loss:ℝ) ≤ shift/2 := by
    have hCast : (loss:ℝ) = 5*(exceptional:ℝ)+12 := by dsimp only [loss]; push_cast; rfl
    linarith only [hCast,hFew',hShift]
  have hD : 6*shift ≤ (D:ℝ) := by linarith only [hShift,hDense]
  obtain ⟨hWindow,hPair⟩ := short_limit_exceptional_and_pair_reserves D loss shift
    (by linarith only [hShift]) hD hLoss
  refine ⟨hWindow,hPair,?_⟩
  have hCap : (cap:ℝ) ≤ shift := Nat.floor_le (by linarith only [hShift])
  have hFloor : (D:ℝ)/3-shift < (floor:ℝ)+1 := Nat.lt_floor_add_one _
  have h : 5*(exceptional:ℝ)+cap+4+loss ≤ floor := by
    linarith only [hFew',hShift,hDense,hLoss,hCap,hFloor]
  exact_mod_cast h

set_option maxHeartbeats 2800000 in
/-- Link an actual original-phase boundary to the next selection at the
paper's short limit. The same checked cleanup and the same projection
history are used on both sides of the change of active vertices. -/
theorem cms_operation_4_1_first_critical_selection
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
      HasAlmostOverfullRecord (univ.filter (fun v => 0 < H.degree m v)) (G.maxDegree-2*m) test (H.degree m) ∨
      ∃ T : SimpleGraph V,
        let degree := auxiliaryPhysicalDegree T initial H.prescribed H.credit m
        let support := univ.filter (fun v => 0 < degree v)
        let current := H.exceptional m ∩ support
        DeletionRun (H.exceptional m ∩ low) (H.graph m) T ∧
          (HasAlmostOverfullRecord support (G.maxDegree-2*m) test degree ∨
            ∃ A,CriticalTrimmingEntry T initial current A degree (G.maxDegree-2*m) long
                (3*low.card+initial.card+1) ∧
              (short ≤ m ∨ Nonempty (TrimmingStepSelection T initial current A degree
                (G.maxDegree-2*m) long H.free m cap))) := by
  intro n initial low shift threshold cap long short hShift hSize hDense hFew
  have hηsmall : η ≤ 1/16 := by linarith only [hSmall]
  obtain ⟨m,hm,H,hBoundary⟩ := cms_operation_4_1_original_phase G η hη hηsmall hVAL test hTest
    (by linarith only [hShift]) hSize hDense hFew
  change m ≤ long at hm
  change OriginalTrimmingHistory G initial low threshold long cap test m at H
  change H.AtBoundary long at hBoundary
  have hLow : low ⊆ initial := filter_subset _ _
  have hW := card_le_card hLow
  have hWreal : (low.card:ℝ) ≤ initial.card := by exact_mod_cast hW
  have hShiftNonneg : 0 ≤ shift := by linarith only [hShift]
  have hFew' : (initial.card:ℝ) ≤ shift/64 := by
    have h := mul_le_mul_of_nonneg_right hSmall hShiftNonneg
    dsimp only [shift] at h ⊢
    nlinarith only [h,hFew]
  have hLong : (long:ℝ) ≤ (G.maxDegree:ℝ)/3-shift := Nat.floor_le (by linarith only [hDense,hShift])
  have hCeil : shift ≤ (threshold:ℝ) := Nat.le_ceil _
  have hCeilUpper : (threshold:ℝ) ≤ shift+1 := (Nat.ceil_lt_add_one hShiftNonneg).le
  have hRange : long+threshold+low.card+2*long ≤ G.maxDegree := by
    exact_mod_cast (show (long:ℝ)+threshold+low.card+2*long ≤ G.maxDegree by
      linarith only [hLong,hCeilUpper,hWreal,hFew',hShift])
  have hOrd (v : V) (hv : v ∉ initial) : G.maxDegree ≤ G.degree v+threshold := by
    have h : (G.maxDegree:ℝ)-G.degree v ≤ shift := by
      by_contra! h
      exact hv (mem_filter.mpr ⟨mem_univ _,h⟩)
    exact_mod_cast (show (G.maxDegree:ℝ) ≤ (G.degree v:ℝ)+threshold by linarith only [h,hCeil])
  have hFloor (v : V) (hv : v ∈ initial) (hw : v ∉ low) : long ≤ G.degree v := by
    have h : (G.maxDegree:ℝ)/3-shift ≤ G.degree v := by
      by_contra! h
      exact hw (mem_filter.mpr ⟨hv,h⟩)
    exact_mod_cast hLong.trans h
  have hM : 5*initial.card+cap+4+(4*initial.card+2) ≤ long :=
    cms_projection_margin_after_trimming_losses n G.maxDegree initial.card η hη hηsmall
      (by linarith only [hShift]) (by simpa only [shift,mul_assoc] using hDense) hFew
  have hAtM : long+threshold+low.card ≤ G.maxDegree-2*m := by omega
  refine ⟨m,hm,H,?_⟩
  rcases H.critical_entry_at_boundary long hBoundary hLow (initial_low_set_independent G η hη hVAL)
    hOrd hFloor hM hAtM with hLast | hStop | ⟨T,hRun,hOutcome⟩
  · exact Or.inl hLast
  · exact Or.inr (Or.inl hStop)
  right
  right
  refine ⟨T,hRun,?_⟩
  rcases hOutcome with hStop | ⟨A,E⟩
  · exact Or.inl hStop
  change CriticalTrimmingEntry T initial _ A _ (G.maxDegree-2*m) long
    (3*low.card+initial.card+1) at E
  by_cases hAtLimit : short ≤ m
  · exact Or.inr ⟨A,E,Or.inl hAtLimit⟩
  obtain ⟨hWindow,hPair,hProjection⟩ :=
    critical_phase_rounded_reserves n G.maxDegree initial.card η hη hSmall hShift hDense hFew
  have hAtLeast : 64 ≤ (n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hηsmall (Nat.cast_nonneg (α := ℝ) n)
    change 64 ≤ η*(n:ℝ) at hShift
    linarith only [h,hShift]
  have hJoin : (initial.card:ℝ)+(initialᶜ.card:ℝ) = n := by exact_mod_cast card_add_card_compl initial
  have hShiftLe : shift ≤ n := by
    have h := mul_le_mul_of_nonneg_right (show η ≤ 1 by linarith only [hSmall]) (Nat.cast_nonneg (α := ℝ) n)
    simpa only [shift,one_mul] using h
  have hCore : 4 ≤ initialᶜ.card := by
    exact_mod_cast (show (4:ℝ) ≤ initialᶜ.card by linarith only [hJoin,hAtLeast,hFew',hShiftLe])
  have hCap : 0 < cap := by
    have h : 1 ≤ cap := Nat.le_floor (by simpa using (show (1:ℝ) ≤ shift by linarith only [hShift]))
    omega
  have hRounds : 3*m ≤ n := by
    have hNV : Nonempty V := Fintype.card_pos_iff.mp (by exact_mod_cast (show 0 < (n:ℝ) by linarith))
    have hG : (G.maxDegree:ℝ) ≤ n := by exact_mod_cast G.maxDegree_lt_card_verts.le
    have hMR : (m:ℝ) ≤ long := by exact_mod_cast hm
    exact_mod_cast (show (3:ℝ)*m ≤ n by linarith only [hG,hMR,hLong,hShift])
  have hRate := free_projection_budget_at_trimming_limit n m initial.card η hRounds
    (show 12 ≤ shift by linarith only [hShift]) hSize hFew
  change long+1+threshold ≤ G.maxDegree-2*short at hWindow
  change short+6+(5*initial.card+12) ≤ long at hPair
  change 5*initial.card+cap+4+(5*initial.card+12) ≤ long at hProjection
  have hUpper : long+3 ≤ G.maxDegree-2*m := by omega
  have hProject : 5*initial.card+cap+4+(3*low.card+initial.card+1) ≤ long := by omega
  have hSix : 6+(3*low.card+initial.card+1) ≤ long := by omega
  rcases E.exists_first_selection test hTest H.free m cap cap (2*(initial.card+1)) hCap H.free_size
    hRate hCore hUpper hProject hSix with hStop | hRound
  · exact Or.inl hStop
  · exact Or.inr ⟨A,E,Or.inr hRound⟩

end OverfullWork.CMSTrimmingRound
