module

public import OverfullWork.CMSOperation41CriticalPhase
public import OverfullWork.CMSOperation41ProjectionHistory

@[expose] public section


/-! Finite continuation of the short part of Operation 4.1. An empty
round following singleton exhaustion either leaves a stopping record
or enables a pair. Once inherited, the pair keeps its degree reserve. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Erasing only an exceptional singleton turns its odd support even
and leaves the odd ordinary side in place. Its last edge costs at
most one of the two deficiency units allowed before reselection. -/
theorem critical_cut_after_singleton_cleanup (S U : Finset V) (w x : V)
    (hU : U ⊆ S) (hw : w ∈ U) (hOdd : Odd S.card)
    (before after : V → ℕ) (d : ℕ)
    (hBound : ∀ v ∈ S,before v ≤ d)
    (hMass : (∑ v ∈ S \ U,(d-before v)) ≤ 1)
    (hExact : ∀ v,after v+(if v=w ∨ v=x then 1 else 0) = before v) :
    Even (S.erase w).card ∧ S.erase w \ U.erase w = S \ U ∧
      (∑ v ∈ S.erase w \ U.erase w,(d-after v)) ≤ 2 := by
  have hCut : S.erase w \ U.erase w = S \ U := by
    ext v
    simp only [mem_sdiff,mem_erase]
    by_cases hv : v = w <;> simp [hv,hw]
  have hEven : Even (S.erase w).card := by
    obtain ⟨k,hk⟩ := hOdd
    have hCard := card_erase_add_one (hU hw)
    exact ⟨k,by omega⟩
  rw [hCut]
  refine ⟨hEven,rfl,?_⟩
  have hDef := ordinary_deficit_after_singleton_exhaustion (S \ U) before after d w x
    (fun h => (mem_sdiff.mp h).2 hw) (fun v hv => hBound v (mem_sdiff.mp hv).1)
    (fun v _ => hExact v)
  omega

omit [Fintype V] in
/-- After the singleton leaves an odd support, a fresh critical choice
on the surviving even support selects the two smallest exceptional degrees. -/
theorem critical_stop_or_inherited_pair (support current : Finset V)
    (degree : V → ℕ) (d budget : ℕ) (hTest : 1 ≤ budget)
    (hCurrent : current ⊆ support) (hEven : Even support.card)
    (hOdd : Odd (support \ current).card)
    (hBound : ∀ v ∈ support,degree v ≤ d)
    (hMass : (∑ v ∈ support \ current,(d-degree v)) ≤ 1) :
    HasAlmostOverfullRecord support d budget degree ∨
      ∃ a ∈ current,∃ b ∈ current,a ≠ b ∧
        (∀ v ∈ current,degree a ≤ degree v) ∧
        (∀ v ∈ current,v ≠ a → degree b ≤ degree v) := by
  by_cases hStop : HasAlmostOverfullRecord support d budget degree
  · exact Or.inl hStop
  obtain ⟨W,_,hParity,hMin⟩ := exists_critical_active_vertices support current hCurrent d
    budget degree hTest hBound hOdd hMass hStop
  rcases hMin with ⟨_,a,_,hW,_⟩ | ⟨_,a,ha,b,hb,hab,_,haMin,hbMin⟩
  · have hTwo := hParity.mp hEven
    simp [hW] at hTwo
  · exact Or.inr ⟨a,ha,b,hb,hab,haMin,hbMin⟩

set_option maxHeartbeats 1600000 in
/-- The possible neutral round between an exhausted singleton and the
next pair leaves both sides of the cut intact. Its credits consume the
entire ordinary deficit, so a second neutral round is unnecessary. -/
theorem TrimmingStepSelection.critical_reselection_after_odd_empty_round
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial current : Finset V}
    {degree : V → ℕ} {d floor j cap : ℕ} {used : ℕ → Finset V}
    (R : TrimmingStepSelection G initial current ∅ degree d floor used j cap)
    (next : V → ℕ) (threshold budget : ℕ) (hD : 3 ≤ d) (hTest : 1 ≤ budget)
    (hCurrent : current ⊆ initial) (hLow : ∀ v ∈ current,degree v < floor+2)
    (hBand : floor+1+threshold ≤ d-2)
    (hBefore : ∀ v,degree v ≤ d) (hAfter : ∀ v,next v ≤ d-2)
    (hExact : ∀ v,next v+(2-R.round.words.degreeCredit R.round.omitted v) = degree v) :
    let S := univ.filter (fun v => 0 < degree v)
    let T := univ.filter (fun v => 0 < next v)
    current ⊆ S → Even S.card → Odd (S \ current).card →
    (∑ v ∈ S \ current,(d-degree v)) ≤ 2 →
    T = S ∧ nextTrimmingExceptional current T next (d-2) threshold = current ∧
      (∀ v ∈ current,next v = degree v) ∧
      (∑ v ∈ T \ current,(d-2-next v)) = 0 ∧
      (HasAlmostOverfullRecord T (d-2) budget next ∨
        ∃ a ∈ current,∃ b ∈ current,a ≠ b ∧
          (∀ v ∈ current,next a ≤ next v) ∧
          (∀ v ∈ current,v ≠ a → next b ≤ next v)) := by
  intro S T hSub hEven hOdd hMass
  have hOrd := R.ordinary_degrees_after_odd_empty_round next (by omega) rfl hLow hBefore
    hAfter hExact hOdd hMass
  have hCurrentEq (v : V) (hv : v ∈ current) : next v = degree v := by
    have hZero : R.round.words.prescribedGraph.degree v = 0 := by
      by_contra! h
      rcases R.exceptional_debit v hv (notMem_empty _) (Nat.pos_of_ne_zero h) with
        ⟨w,hw,_⟩ | hs | ⟨w,hw,_⟩
      · exact notMem_empty _ hw
      · obtain ⟨_,hHigh,_⟩ := R.special_debit v hs
        exact Nat.not_lt_of_ge hHigh (hLow v hv)
      · simp at hw
    have hCredit := R.round.words.prescribed_degree_add_credit_on_exceptional
      R.round.omitted (hCurrent hv)
    have h := hExact v
    omega
  have hSupport : T = S := by
    apply le_antisymm
    · intro v hv
      have h := hExact v
      exact mem_filter.mpr ⟨mem_univ _,by
        have hp := (mem_filter.mp hv).2
        omega⟩
    · intro v hv
      refine mem_filter.mpr ⟨mem_univ _,?_⟩
      by_cases h : v ∈ current
      · rw [hCurrentEq v h]
        exact (mem_filter.mp hv).2
      · rw [hOrd v (mem_sdiff.mpr ⟨hv,h⟩)]
        omega
  have hKeep : nextTrimmingExceptional current T next (d-2) threshold = current := by
    apply le_antisymm ((filter_subset _ _).trans inter_subset_left)
    intro v hv
    have h := hLow v hv
    refine mem_filter.mpr ⟨mem_inter.mpr ⟨hv,hSupport.symm ▸ hSub hv⟩,?_⟩
    rw [hCurrentEq v hv]
    omega
  have hZero : (∑ v ∈ S \ current,(d-2-next v)) = 0 := by
    apply sum_eq_zero
    intro v hv
    rw [hOrd v hv,Nat.sub_self]
  refine ⟨hSupport,hKeep,hCurrentEq,?_ ,?_⟩
  · rwa [hSupport]
  · rw [hSupport]
    exact critical_stop_or_inherited_pair S current next (d-2) budget hTest hSub hEven hOdd
      (fun v _ => hAfter v) (hZero.le.trans (Nat.zero_le _))

set_option maxHeartbeats 2200000 in
/-- At the cleaned state after singleton exhaustion, either a stopping
test or a pair is available now, or one actual Step 2 prescription will
make one of them available at the next record. -/
theorem exists_critical_continuation_after_singleton
    (G : SimpleGraph V) [DecidableRel G.Adj] (initial current : Finset V)
    (degree : V → ℕ) (d floor threshold testBudget : ℕ)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hCurrent : current ⊆ initial) (hLow : ∀ v ∈ current,degree v < floor+2)
    (hBand : floor+1+threshold ≤ d-2) (hThreshold : 2 ≤ threshold)
    (hExact : ∀ v ∈ initial,degree v = G.degree v)
    (hRoom : ∀ v,v ∉ initial → 2 ≤ degree v)
    (hReserve : ∀ v ∈ initial,0 < G.degree v → 5*initial.card+k+4 ≤ G.degree v)
    (hSize : 4 ≤ initialᶜ.card) (hD : 3 ≤ d) (hBound : ∀ v,degree v ≤ d)
    (hTest : 1 ≤ testBudget) :
    let S := univ.filter (fun v => 0 < degree v)
    let result (t : ℕ) (record : V → ℕ) :=
      HasAlmostOverfullRecord S t testBudget record ∨
        ((∑ v ∈ S \ current,(t-record v)) ≤ 1 ∧
          ∃ a ∈ current,∃ b ∈ current,a ≠ b ∧
            (∀ v ∈ current,record a ≤ record v) ∧
            (∀ v ∈ current,v ≠ a → record b ≤ record v))
    current ⊆ S → Even S.card → Odd (S \ current).card →
    (∑ v ∈ S \ current,(d-degree v)) ≤ 2 →
    result d degree ∨
      ∃ R : TrimmingStepSelection G initial current ∅ degree d floor used j cap,
        let next (v : V) := degree v-(2-R.round.words.degreeCredit R.round.omitted v)
        ¬HasAlmostOverfullRecord S d testBudget degree ∧
        (∀ v,next v ≤ d-2 ∧
          next v+(2-R.round.words.degreeCredit R.round.omitted v) = degree v) ∧
        univ.filter (fun v => 0 < next v) = S ∧
        nextTrimmingExceptional current S next (d-2) threshold = current ∧
        (∀ v ∈ current,next v = degree v) ∧
        (∑ v ∈ S \ current,(d-2-next v)) = 0 ∧
        result (d-2) next := by
  intro S result hSub hEven hOdd hMass
  by_cases hStop : HasAlmostOverfullRecord S d testBudget degree
  · exact Or.inl (Or.inl hStop)
  by_cases hEnough : (∑ v ∈ S \ current,(d-degree v)) ≤ 1
  · rcases critical_stop_or_inherited_pair S current degree d testBudget hTest hSub
      hEven hOdd (fun v _ => hBound v) hEnough with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨hEnough,h⟩)
  have hMode : (G.IsIndepSet (↑(∅ : Finset V) : Set V) ∧
      ∀ w ∈ (∅ : Finset V),∀ x,G.Adj w x → PrunedCore.neighboursIn G ∅ x < G.degree w) ∨
      ((∅ : Finset V).card = 2 ∧ ∀ w ∈ (∅ : Finset V),6 ≤ G.degree w) := by
    left
    refine ⟨?_,by simp⟩
    intro a ha
    simp at ha
  have hDef (v : V) (hv : v ∈ current) : degree v+2 ≤ d := by
    have h := hLow v hv
    omega
  have hCore : initialᶜ ⊆ S := fun v hv =>
    mem_filter.mpr ⟨mem_univ _,by have h := hRoom v (mem_compl.mp hv); omega⟩
  rcases exists_trimming_step_selection G initial current ∅ hCurrent (empty_subset _)
      (by simp) hMode degree d floor testBudget (by omega) hBound hExact hDef hSize
      used j cap k budget hCap hUsed hTotal hSub hCore hTest hStop
      (fun v hv _ hp => hReserve v hv hp) with hRound | hSwitch
  · obtain ⟨R⟩ := hRound
    let next (v : V) := degree v-(2-R.round.words.degreeCredit R.round.omitted v)
    have hNext (v : V) : next v ≤ d-2 ∧
        next v+(2-R.round.words.degreeCredit R.round.omitted v) = degree v := by
      have hPay : 2-R.round.words.degreeCredit R.round.omitted v ≤ degree v := by
        by_cases h : v ∈ initial
        · have hBalance := R.round.words.prescribed_degree_add_credit_on_exceptional
            R.round.omitted h
          have hHost : R.round.words.prescribedGraph.degree v ≤ G.degree v :=
            degree_le_of_le R.round.words.prescribedGraph_le
          have hDeg := hExact v h
          omega
        · have h := hRoom v h
          omega
      have hCap := R.round.degree_cap v
      dsimp only [next]
      omega
    obtain ⟨hSupport,hExceptional,hCurrentEq,hZero,hResult⟩ := R.critical_reselection_after_odd_empty_round
      next threshold testBudget hD hTest hCurrent hLow hBand hBound
      (fun v => (hNext v).1) (fun v => (hNext v).2) hSub hEven hOdd hMass
    rw [hSupport] at hExceptional hZero hResult
    refine Or.inr ⟨R,hStop,hNext,hSupport,hExceptional,hCurrentEq,hZero,?_⟩
    exact hResult.imp_right (fun h => ⟨hZero.le.trans (Nat.zero_le _),h⟩)
  · obtain ⟨_,A,_,_,_,_,_,_,hDeficit,_⟩ := hSwitch
    exact (hEnough hDeficit).elim

/-- One lost edge per active endpoint is compatible with the six-edge
reserve used to construct every later pair prescription. -/
theorem inherited_pair_prefix_has_six (A : Finset V) (S T P : ℕ → SimpleGraph V)
    (m : ℕ) (hPair : A.card = 2)
    (hEntry : ∀ w ∈ A,m+6 ≤ (S 0).degree w)
    (hClean : ∀ i < m,DeletionRun A (S i) (T i))
    (hP : ∀ i < m,P i ≤ T i)
    (hUnit : ∀ i < m,∀ w ∈ A,(P i).degree w = 1)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i)) :
    (∀ i < m,T i = S i) ∧
      ∀ i ≤ m,∀ w ∈ A,(S i).degree w+i = (S 0).degree w ∧ 6 ≤ (S i).degree w := by
  obtain ⟨hEq,hNone,_⟩ := inherited_active_set_persists A S T P m
    (fun w hw => by rw [hPair]; have h := hEntry w hw; omega) hClean hP hUnit hNext
  refine ⟨hNone,fun i hi w hw => ⟨hEq i hi w hw,?_⟩⟩
  have h := hEq i hi w hw
  have he := hEntry w hw
  omega

/-- Add exactly the endpoints whose previous free projection load is
below the cap. Any other endpoint already has a forced-edge or deficit
certificate in the current round. -/
theorem TrimmingStepSelection.append_free_projections
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial current active : Finset V}
    {degree : V → ℕ} {d floor j cap : ℕ} {used : ℕ → Finset V}
    (R : TrimmingStepSelection G initial current active degree d floor used j cap)
    (hCap : ∀ v,projectionLoad (range j) used v ≤ cap) :
    let endpoints := univ.image (fun i => (R.round.words.endpoint i).val)
    let free := endpoints.filter (fun v => projectionLoad (range j) used v < cap)
    let next := Function.update used j free
    free.card ≤ 2*(initial.card+1) ∧ (∀ i < j,next i = used i) ∧
    (∀ v,projectionLoad (range (j+1)) next v ≤ cap) ∧
    ∀ v ∈ endpoints,v ∈ free ∨
      (∃ w ∈ active,R.round.words.prescribedGraph.Adj w v) ∨
      0 < R.round.words.degreeCredit R.round.omitted v := by
  intro endpoints free next
  have hCard : endpoints.card ≤ 2*R.round.size := by
    apply (card_image_le (f := fun i => (R.round.words.endpoint i).val)).trans
    simp [Fintype.card_prod,Nat.mul_comm]
  have hOld (i : ℕ) (hi : i < j) : next i = used i := Function.update_of_ne hi.ne _ _
  have hLoad (v : V) : projectionLoad (range j) next v = projectionLoad (range j) used v := by
    unfold projectionLoad
    congr 1
    exact filter_congr (fun i hi => by rw [hOld i (mem_range.mp hi)])
  refine ⟨(card_le_card (filter_subset _ _)).trans (hCard.trans (Nat.mul_le_mul_left _ R.size_bound)),
    hOld,?_,?_⟩
  · intro v
    rw [projectionLoad_range_succ,hLoad,show next j = free from Function.update_self _ _ _]
    split_ifs with h
    · exact Nat.succ_le_of_lt (mem_filter.mp h).2
    · simpa using hCap v
  · intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact (R.endpoint_payment i).imp_left (fun h => mem_filter.mpr ⟨hv,h⟩)

omit [Fintype V] [DecidableEq V] in
/-- The uniform free-projection budget pays for all rounds through
either limit. The size hypothesis absorbs the extra word in the
per-round bound, including when the initial exceptional set is empty. -/
theorem free_projection_budget_at_trimming_limit (n j exceptional : ℕ) (η : ℝ)
    (hRounds : 3*j ≤ n) (hShift : 12 ≤ η*(n:ℝ))
    (hSize : 6 ≤ η^2*(n:ℝ)) (hFew : (exceptional:ℝ) ≤ η^2*(n:ℝ)) :
    let cap := ⌊η*(n:ℝ)⌋₊
    j*(2*(exceptional+1)) ≤ cap*cap := by
  intro cap
  have hFloor := Nat.lt_floor_add_one (η*(n:ℝ))
  change η*(n:ℝ) < (cap:ℝ)+1 at hFloor
  have hCap : (11/12:ℝ)*(η*(n:ℝ)) ≤ cap := by linarith only [hFloor,hShift]
  have hCapNonneg : 0 ≤ (cap:ℝ) := Nat.cast_nonneg _
  have hScaleNonneg : 0 ≤ (11/12:ℝ)*(η*(n:ℝ)) := by linarith only [hShift]
  have hSquare := mul_le_mul hCap hCap hScaleNonneg hCapNonneg
  have hJ : (j:ℝ) ≤ (n:ℝ)/3 := by
    have h : (3:ℝ)*(j:ℝ) ≤ n := by exact_mod_cast hRounds
    linarith only [h]
  have hB : 2*((exceptional:ℝ)+1) ≤ (7/3:ℝ)*(η^2*(n:ℝ)) := by
    linarith only [hFew,hSize]
  have hProd := mul_le_mul hJ hB (by positivity : 0 ≤ 2*((exceptional:ℝ)+1))
    (by positivity : 0 ≤ (n:ℝ)/3)
  have hTarget : (j:ℝ)*(2*((exceptional:ℝ)+1)) ≤ (cap:ℝ)*(cap:ℝ) := by
    refine hProd.trans ((show (n:ℝ)/3*((7/3:ℝ)*(η^2*(n:ℝ))) ≤
      (11/12:ℝ)*(η*(n:ℝ))*((11/12:ℝ)*(η*(n:ℝ))) by
        nlinarith only [sq_nonneg (η*(n:ℝ))]).trans hSquare)
  exact_mod_cast hTarget

end OverfullWork.CMSTrimmingRound
