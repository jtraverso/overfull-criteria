module

public import OverfullWork.CMSOperation41EmptyActiveRounds

@[expose] public section


/-! S2.3 and S2.4 either supply a prescription or select the one or
two vertices that start the critical part of Operation 4.1. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 6000000 in
theorem exists_empty_active_trimming_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (initial current : Finset V) (hCurrent : current ⊆ initial)
    (degree : V → ℕ) (d floor testBudget : ℕ) (hD : 2 ≤ d)
    (hBound : ∀ v,degree v ≤ d) (hCurrentCap : ∀ v ∈ current,degree v+2 ≤ d)
    (hSize : 4 ≤ (initialᶜ : Finset V).card)
    (used : ℕ → Finset V) (j cap k budget : ℕ)
    (hCap : 0 < cap) (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap) :
    let active := univ.filter (fun v => 0 < degree v)
    let B := retiredTrimmingPool initial current active
    current ⊆ active → initialᶜ ⊆ active →
    1 ≤ testBudget → ¬HasAlmostOverfullRecord active d testBudget degree →
    (∀ v ∈ B,initial.card+2+k+2*B.card ≤ G.degree v) →
    (∀ z ∈ current,floor+2 ≤ degree z → initial.card+2+k+2*B.card ≤ G.degree z) →
    (∃ (R : TrimmingRoundPrescription G initial degree d) (special : Option V),
      R.size ≤ B.card+1 ∧
      (∀ v,special = some v → v ∈ current ∧ floor+2 ≤ degree v) ∧
      (∀ v ∈ current,(∃ i,v ∈ R.words.body i) ↔ special = some v) ∧
      (∀ v ∈ current,R.words.prescribedGraph.degree v = if special = some v then 2 else 0) ∧
      (Odd (active \ current).card → special = none →
        2 ≤ ∑ v ∈ active \ current,R.words.degreeCredit R.omitted v) ∧
      (∀ i,projectionLoad (range j) used (R.words.endpoint i).val < cap ∨
        0 < R.words.degreeCredit R.omitted (R.words.endpoint i).val)) ∨
    (∃ W ⊆ current,1 ≤ W.card ∧ W.card ≤ 2 ∧
      (Even active.card ↔ W.card = 2) ∧
      (∀ z ∈ current,degree z < floor+2) ∧
      Odd (active \ current).card ∧ (∑ v ∈ active \ current,(d-degree v)) ≤ 1 ∧
      ((Even current.card ∧ ∃ a ∈ current,W = {a} ∧ ∀ v ∈ current,degree a ≤ degree v) ∨
        (Odd current.card ∧ ∃ a ∈ current,∃ b ∈ current,a ≠ b ∧ W = {a,b} ∧
          (∀ v ∈ current,degree a ≤ degree v) ∧ ∀ v ∈ current,v ≠ a → degree b ≤ degree v))) := by
  intro active B hActive hCore hTest hNo hRoom hSpecialRoom
  let X := active \ current
  let C := ↥(initialᶜ : Finset V)
  have hB (v : V) : v ∈ B ↔ (v ∈ active ∧ v ∈ initial) ∧ v ∉ current := by
    simp only [B,retiredTrimmingPool,mem_sdiff,mem_inter]
  have hBI : B ⊆ initial := fun v hv => ((hB v).mp hv).1.2
  have hX (v : V) (hv : v ∈ X) (hvI : v ∈ initial) : v ∈ B :=
    (hB v).mpr ⟨⟨(mem_sdiff.mp hv).1,hvI⟩,(mem_sdiff.mp hv).2⟩
  have hExcluded (v : V) (hvI : v ∈ initial) (hvB : v ∉ B) : degree v+2 ≤ d := by
    by_cases hvC : v ∈ current
    · exact hCurrentCap v hvC
    have hvA : v ∉ active := fun h => hvB ((hB v).mpr ⟨⟨h,hvI⟩,hvC⟩)
    have hv : ¬0 < degree v := fun h => hvA (mem_filter.mpr ⟨mem_univ _,h⟩)
    omega
  have hParts := trimming_parity_for_retired_spokes initial current active hCurrent hCore
  change (initialᶜ.card+B.card = X.card) ∧ _ at hParts
  have hSpoke
      (D : Finset V) (I : Finset C) (special : Option V) (hDI : D ⊆ initial)
      (hDSize : D.card ≤ B.card+1) (hISize : I.card ≤ 1)
      (hSpecial : ∀ v,special = some v → v ∈ current ∧ floor+2 ≤ degree v)
      (hCentres : ∀ v ∈ current,v ∈ D ↔ special = some v)
      (hMissing : ∀ v ∈ initial,v ∉ D → degree v+2 ≤ d)
      (hOmit : ∀ v ∈ I,degree v.val+2 ≤ d)
      (hParity : Even (initialᶜ.card-I.card+D.card))
      (hSpend : Odd X.card → special = none →
        ∃ v ∈ X,(v ∈ initial ∧ v ∉ D) ∨ ∃ x ∈ I,x.val = v)
      (hDRoom : ∀ v ∈ D,initial.card+I.card+k+2*D.card ≤ G.degree v) :
      ∃ (R : TrimmingRoundPrescription G initial degree d) (special : Option V),
        R.size ≤ B.card+1 ∧
        (∀ v,special = some v → v ∈ current ∧ floor+2 ≤ degree v) ∧
        (∀ v ∈ current,(∃ i,v ∈ R.words.body i) ↔ special = some v) ∧
        (∀ v ∈ current,R.words.prescribedGraph.degree v = if special = some v then 2 else 0) ∧
        (Odd X.card → special = none → 2 ≤ ∑ v ∈ X,R.words.degreeCredit R.omitted v) ∧
        (∀ i,projectionLoad (range j) used (R.words.endpoint i).val < cap ∨
          0 < R.words.degreeCredit R.omitted (R.words.endpoint i).val) := by
    have hLen : 3 ≤ initialᶜ.card-I.card+D.card := by omega
    obtain ⟨R,hRSize,hRI,hGaps,hBody,hFresh⟩ := exists_spoke_trimming_prescription G
      initial D hDI I degree d hBound hMissing hOmit hLen hParity hISize
      used j cap k budget hCap hUsed hTotal hDRoom
    have hUse (v : V) (hv : v ∈ current) := (hBody v).trans (hCentres v hv)
    refine ⟨R,special,hRSize ▸ hDSize,hSpecial,hUse,?_,?_,fun i => Or.inl (hFresh i)⟩
    · intro v hv
      by_cases hs : special = some v
      · obtain ⟨i,hi⟩ := (hUse v hv).mpr hs
        have hCredit : R.words.degreeCredit ∅ v = 0 := by
          rw [TrimmingReplacementWords.degreeCredit,if_pos (Or.inr ⟨i,hi⟩),hGaps,
            trimming_gap_degree_eq_card_incident_pairs]
          simp
        have hBalance := R.words.prescribed_degree_add_credit_on_exceptional ∅ (hCurrent hv)
        rw [if_pos hs]
        omega
      · rw [if_neg hs]
        exact R.words.prescribed_degree_eq_zero_of_absent_body (hCurrent hv)
          (fun i hi => hs ((hUse v hv).mp ⟨i,hi⟩))
    · intro hOdd hs
      obtain ⟨v,hv,hCase⟩ := hSpend hOdd hs
      have hCredit : R.words.degreeCredit R.omitted v = 2 := by
        rcases hCase with ⟨hvI,hn⟩ | ⟨x,hx,he⟩
        · have hZero := R.words.prescribed_degree_eq_zero_of_absent_body hvI
            (fun i hi => hn ((hBody v).mp ⟨i,hi⟩))
          have hBalance := R.words.prescribed_degree_add_credit_on_exceptional R.omitted hvI
          omega
        · rw [←he,hRI]
          exact R.words.degree_credit_eq_two_at_omitted_core I x hx
      have hc := single_le_sum (f := R.words.degreeCredit R.omitted) (fun _ _ => Nat.zero_le _) hv
      rwa [hCredit] at hc
  have hNotCentres {D : Finset V} (hSub : D ⊆ B) (v : V) (hv : v ∈ current) :
      v ∈ D ↔ (none : Option V) = some v := by
    simp only [reduceCtorEq,iff_false]
    intro h
    exact ((hB v).mp (hSub h)).2 hv
  cases empty_active_operation_4_1_choice active current hActive d floor testBudget degree hTest
      (fun v _ => hBound v) hNo with
  | even_core hEven =>
    left
    refine hSpoke B ∅ none hBI (Nat.le_add_right _ _) (by simp) (by simp) (hNotCentres Subset.rfl)
      hExcluded (by simp) ?_ (fun h _ => (Nat.not_even_iff_odd.mpr h hEven).elim) ?_
    · simpa only [card_empty,Nat.sub_zero,hParts.1] using hEven
    · intro v hv
      have h := hRoom v hv
      simp only [card_empty,add_zero]
      omega
  | charged_pair a b ha hb hab hDa hDb =>
    left
    obtain ⟨R,hRF,hRI,hRGap,hRBody,hFresh⟩ :=
      exists_charged_pair_trimming_prescription G initial B hBI degree d a b hab
        (hX a ha) (hX b hb) hDa hDb hBound hExcluded (by omega)
        used j cap k budget hCap hUsed hTotal hRoom
    refine ⟨R,none,hRF,by simp,fun v hv => (hRBody v).trans (hNotCentres Subset.rfl v hv),?_,?_,?_⟩
    · intro v hv
      simp only [reduceCtorEq,if_false]
      exact R.words.prescribed_degree_eq_zero_of_absent_body (hCurrent hv)
        (fun i hi => ((hB v).mp ((hRBody v).mp ⟨i,hi⟩)).2 hv)
    · intro _ _
      have hAt (v : V) (hv : v ∈ X) (hPair : v = a ∨ v = b) :
          R.words.degreeCredit R.omitted v = 1 := by
        by_cases hvI : v ∈ initial
        · obtain ⟨i,hi⟩ := (hRBody v).mpr (hX v hv hvI)
          rw [TrimmingReplacementWords.degreeCredit,if_pos (Or.inr ⟨i,hi⟩),hRGap,
            trimming_gap_degree_of_single_pair hab,if_pos hPair]
        · let z : C := ⟨v,mem_compl.mpr hvI⟩
          have hz := R.words.degree_credit_eq_gaps_at_retained_core ∅ z (notMem_empty _)
          change R.words.degreeCredit ∅ v = _ at hz
          rw [hRI,hz,hRGap,trimming_gap_degree_of_single_pair hab,if_pos hPair]
      have hSum := sum_le_sum_of_subset_of_nonneg
        (insert_subset_iff.mpr ⟨ha,singleton_subset_iff.mpr hb⟩ : ({a,b} : Finset V) ⊆ X)
        (fun (v : V) _ _ => Nat.zero_le (R.words.degreeCredit R.omitted v))
      rw [sum_pair hab,hAt a ha (Or.inl rfl),hAt b hb (Or.inr rfl)] at hSum
      exact hSum
    · intro i
      rcases hFresh i with h | h
      · exact Or.inl h
      · right
        rw [hRI,R.words.degree_credit_eq_gaps_at_retained_core ∅ (R.words.endpoint i) (notMem_empty _),
          hRGap,trimming_gap_degree_of_single_pair hab,if_pos h]
        decide
  | «omit» a ha hDa _ hOdd =>
    left
    have hParity (q : ℕ) (hq : q+1 = X.card) : Even q := by
      obtain ⟨t,ht⟩ := (show Odd X.card from hOdd)
      exact ⟨t,by omega⟩
    by_cases haI : a ∈ initial
    · let D := B.erase a
      have hDB : D ⊆ B := erase_subset _ _
      have hDCard : D.card ≤ B.card := card_le_card hDB
      refine hSpoke D ∅ none (hDB.trans hBI) (by omega) (by simp) (by simp) (hNotCentres hDB)
        ?_ (by simp) (hParity _ ?_) (fun _ _ => ⟨a,ha,Or.inl ⟨haI,notMem_erase _ _⟩⟩) ?_
      · intro v hvI hvD
        by_cases h : v = a
        · rwa [h]
        · exact hExcluded v hvI (fun hvB => hvD (mem_erase.mpr ⟨h,hvB⟩))
      · have hDrop := card_erase_add_one (hX a ha haI)
        change D.card+1 = B.card at hDrop
        simp only [card_empty,Nat.sub_zero]
        omega
      · intro v hv
        have h := hRoom v (hDB hv)
        simp only [card_empty,add_zero]
        omega
    · let a' : C := ⟨a,mem_compl.mpr haI⟩
      let I : Finset C := {a'}
      have hI : I.card = 1 := card_singleton a'
      refine hSpoke B I none hBI (Nat.le_add_right _ _) (by omega) (by simp)
        (hNotCentres Subset.rfl) hExcluded ?_ (hParity _ (by rw [hI]; omega))
        (fun _ _ => ⟨a,ha,Or.inr ⟨a',mem_singleton_self _,rfl⟩⟩) ?_
      · intro v hv
        have h : v = a' := mem_singleton.mp hv
        simpa only [h] using hDa
      · intro v hv
        have h := hRoom v hv
        rw [hI]
        omega
  | special z hz hHigh _ hOdd =>
    left
    let D := insert z B
    have hZB : z ∉ B := fun h => ((hB z).mp h).2 hz
    have hDCard : D.card = B.card+1 := card_insert_of_notMem hZB
    refine hSpoke D ∅ (some z) (insert_subset_iff.mpr ⟨hCurrent hz,hBI⟩) hDCard.le
      (by simp) ?_ ?_ ?_ (by simp) ?_ (fun _ h => (Option.some_ne_none z h).elim) ?_
    · intro v hv
      obtain rfl := Option.some.inj hv
      exact ⟨hz,hHigh⟩
    · intro v hv
      have hVB : v ∉ B := fun h => ((hB v).mp h).2 hv
      simp [D,hVB,eq_comm]
    · exact fun v hv hn => hExcluded v hv (fun h => hn (mem_insert_of_mem h))
    · simp only [card_empty,Nat.sub_zero,hDCard,←add_assoc,hParts.1]
      obtain ⟨t,ht⟩ := (show Odd X.card from hOdd)
      exact ⟨t+1,by omega⟩
    · intro v hv
      have hBudget : initial.card+2+k+2*B.card ≤ G.degree v := by
        rcases mem_insert.mp hv with rfl | h
        · exact hSpecialRoom _ hz hHigh
        · exact hRoom v h
      simp only [card_empty,add_zero,hDCard]
      omega
  | switch_active W hW hParity hSmall hOdd hMass hMin =>
    right
    have hCards : 1 ≤ W.card ∧ W.card ≤ 2 := by
      rcases hMin with ⟨_,a,_,rfl,_⟩ | ⟨_,a,_,b,_,hne,rfl,_⟩
      · simp
      · simp [card_pair hne]
    exact ⟨W,hW,hCards.1,hCards.2,hParity,hSmall,hOdd,hMass,hMin⟩

end OverfullWork.CMSTrimmingRound
