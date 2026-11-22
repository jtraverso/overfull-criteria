module

public import OverfullWork.CMSOperation41EmptyActiveStep
public import OverfullWork.CMSOperation41HistoryReserves
public import OverfullWork.CMSOperation41IndependentRounds
public import OverfullWork.CMSOperation41SingletonRetired

@[expose] public section


/-! Step 2 on the cleaned virtual graph. All branches expose the
loss witnesses used to maintain the next round's degree reserves. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PrunedCore
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

structure TrimmingStepSelection (G : SimpleGraph V) [DecidableRel G.Adj]
    (initial current active : Finset V) (degree : V → ℕ) (d floor : ℕ)
    (used : ℕ → Finset V) (j cap : ℕ) where
  round : TrimmingRoundPrescription G initial degree d
  size_bound : round.size ≤ initial.card+1
  special : Option V
  special_debit : ∀ v,special = some v →
    v ∈ current ∧ floor+2 ≤ degree v ∧ round.words.prescribedGraph.degree v = 2
  special_only_when_empty : active.Nonempty → special = none
  empty_odd_ordinary_credit : active = ∅ →
    Odd (((univ : Finset V).filter (fun v => 0 < degree v)) \ current).card →
    special = none →
    2 ≤ ∑ v ∈ ((univ : Finset V).filter (fun v => 0 < degree v)) \ current,
      round.words.degreeCredit round.omitted v
  active_progress :
    (2 ≤ active.card ∨ Odd (((univ : Finset V).filter (fun v => 0 < degree v)) \ current).card) →
    ∀ w ∈ active,1 ≤ round.words.prescribedGraph.degree w
  pair_progress : active.card = 2 → (∀ w ∈ active,6 ≤ G.degree w) →
    ∀ w ∈ active,round.words.prescribedGraph.degree w = 1
  adjacent_actives : ∀ u ∈ active,∀ v ∈ active,G.Adj u v →
    round.words.prescribedGraph.degree u ≤ 1 ∧ round.words.prescribedGraph.degree v ≤ 1
  exceptional_debit : ∀ v ∈ current,v ∉ active → 0 < round.words.prescribedGraph.degree v →
    (∃ w ∈ active,round.words.prescribedGraph.Adj w v) ∨ special = some v ∨
      (∃ w,active = {w} ∧ s(w,v) ∈ round.words.gaps ∧ G.degree w < current.card+2 ∧
        round.words.prescribedGraph.degree w = 1 ∧ round.words.prescribedGraph.degree v = 1)
  endpoint_payment : ∀ i,projectionLoad (range j) used (round.words.endpoint i).val < cap ∨
    (∃ w ∈ active,round.words.prescribedGraph.Adj w (round.words.endpoint i).val) ∨
    0 < round.words.degreeCredit round.omitted (round.words.endpoint i).val

/-- The exceptional charge recorded by this prescription can occur
only in S2.2.1. The projected leaf and the singleton each lose one. -/
def TrimmingStepSelection.internalCharge
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial current active : Finset V}
    {degree : V → ℕ} {d floor j cap : ℕ} {used : ℕ → Finset V}
    (R : TrimmingStepSelection G initial current active degree d floor used j cap) (v : V) : Prop :=
  ∃ w,active = {w} ∧ s(w,v) ∈ R.round.words.gaps ∧ G.degree w < current.card+2 ∧
    R.round.words.prescribedGraph.degree w = 1 ∧ R.round.words.prescribedGraph.degree v = 1

/-- Convert the selected loss witnesses into the inequality consumed
by the cumulative reserve proof. -/
theorem TrimmingStepSelection.exceptional_cost
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial current active : Finset V}
    {degree : V → ℕ} {d floor j cap : ℕ} {used : ℕ → Finset V}
    (R : TrimmingStepSelection G initial current active degree d floor used j cap)
    (S : SimpleGraph V) (A : Finset V) {v : V}
    (hv : v ∈ current) (hInit : current ⊆ initial) (hInactive : v ∉ active) (hActive : active ⊆ A)
    (hCleanup : ∀ x,(sdiff S G).Adj v x → x ∈ A) :
    let C := sdiff S G
    let P := R.round.words.prescribedGraph
    C.degree v+P.degree v ≤ 2*((C ⊔ P).neighborFinset v ∩ A).card+
      (if R.special = some v then 2 else 0)+(if R.internalCharge v then 1 else 0) := by
  intro C P
  have hDis : Disjoint C P := by
    rw [disjoint_iff_inf_le]
    intro x y h
    exact h.1.2 (R.round.words.prescribedGraph_le h.2)
  have hTwo := R.round.words.prescribed_graph_degree_le v
  rw [if_pos (hInit hv)] at hTwo
  have hPay := exceptional_round_cost_of_classification C P A v
    (R.special = some v) (R.internalCharge v) hDis hCleanup hTwo (fun hp => by
      rcases R.exceptional_debit v hv hInactive hp with ⟨w,hw,he⟩ | hs | ⟨w,hw,hGap,hSmall,hOne,hV⟩
      · exact Or.inl ⟨w,hActive hw,he.symm⟩
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr ⟨⟨w,hw,hGap,hSmall,hOne,hV⟩,hV⟩))
  have hDec : Classical.propDecidable (R.special = some v) =
      (inferInstance : Decidable (R.special = some v)) := Subsingleton.elim _ _
  rwa [hDec] at hPay

set_option maxHeartbeats 3000000 in
/-- Construct the next prescription, or the critical active choice
that the paper makes when an empty set cannot supply a prescription. -/
theorem exists_trimming_step_selection
    (G : SimpleGraph V) [DecidableRel G.Adj] (initial current active : Finset V)
    (hCurrent : current ⊆ initial) (hActive : active ⊆ current)
    (hPos : ∀ w ∈ active,0 < G.degree w)
    (hMode : (G.IsIndepSet (active : Set V) ∧
      ∀ w ∈ active,∀ x,G.Adj w x → neighboursIn G active x < G.degree w) ∨
      (active.card = 2 ∧ ∀ w ∈ active,6 ≤ G.degree w))
    (degree : V → ℕ) (d floor testBudget : ℕ) (hD : 2 ≤ d)
    (hBound : ∀ v,degree v ≤ d) (hExact : ∀ v ∈ initial,degree v = G.degree v)
    (hDef : ∀ v ∈ current,degree v+2 ≤ d) (hSize : 4 ≤ initialᶜ.card)
    (used : ℕ → Finset V) (j cap k budget : ℕ)
    (hCap : 0 < cap) (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap) :
    let support := univ.filter (fun v => 0 < degree v)
    current ⊆ support → initialᶜ ⊆ support →
    1 ≤ testBudget → ¬HasAlmostOverfullRecord support d testBudget degree →
    (∀ v ∈ initial,v ∉ active → 0 < G.degree v → 5*initial.card+k+4 ≤ G.degree v) →
    Nonempty (TrimmingStepSelection G initial current active degree d floor used j cap) ∨
    (active = ∅ ∧ ∃ W ⊆ current,1 ≤ W.card ∧ W.card ≤ 2 ∧
      (Even support.card ↔ W.card = 2) ∧
      (∀ z ∈ current,degree z < floor+2) ∧
      Odd (support \ current).card ∧ (∑ v ∈ support \ current,(d-degree v)) ≤ 1 ∧
      ((Even current.card ∧ ∃ a ∈ current,W = {a} ∧ ∀ v ∈ current,degree a ≤ degree v) ∨
        (Odd current.card ∧ ∃ a ∈ current,∃ b ∈ current,a ≠ b ∧ W = {a,b} ∧
          (∀ v ∈ current,degree a ≤ degree v) ∧ ∀ v ∈ current,v ≠ a → degree b ≤ degree v))) := by
  intro support hSupport hCore hTest hNo hReserve
  let B := retiredTrimmingPool initial current support
  have hBI : B ⊆ initial := fun _ h => (mem_inter.mp (mem_sdiff.mp h).1).2
  have hBC := card_le_card hBI
  have hCore₃ : 3 ≤ initialᶜ.card := by omega
  have hProject (v : V) (hv : v ∈ initial) (ha : v ∉ active) (hp : 0 < G.degree v) :
      initial.card+4*(active.card+1)+k ≤ G.degree v :=
    (projection_and_spoke_room_of_degree_floor initial active B (hActive.trans hCurrent) hBI
      (G.degree v) (G.degree v) 0 k (by simp) (by simpa using hReserve v hv ha hp)).1
  have hSpoke (v : V) (hv : v ∈ initial) (hn : v ∉ current) (hp : 0 < G.degree v) :
      initial.card+(active.card+1)+k+2*initial.card ≤ G.degree v :=
    (projection_and_spoke_room_of_degree_floor initial active B (hActive.trans hCurrent) hBI
      (G.degree v) (G.degree v) 0 k (by simp)
      (by simpa using hReserve v hv (fun h => hn (hActive h)) hp)).2.1
  have hRetired (v : V) (hv : v ∈ B) : initial.card+2+k+2*B.card ≤ G.degree v := by
    have hvI := hBI hv
    have hvN := (mem_sdiff.mp hv).2
    have hvP := (mem_filter.mp (mem_inter.mp (mem_sdiff.mp hv).1).1).2
    rw [hExact v hvI] at hvP
    have h := hReserve v hvI (fun h => hvN (hActive h)) hvP
    omega
  by_cases hPairMode : active.card = 2 ∧ ∀ w ∈ active,6 ≤ G.degree w
  · obtain ⟨hPair,hHigh⟩ := hPairMode
    obtain ⟨R,hCount,_,hOne,_,hEnd,hPay⟩ :=
      exists_inherited_pair_trimming_prescription G initial current active hCurrent hActive hPair
        hHigh hCore₃ degree d hD hBound hExact hDef used j cap k budget hCap hUsed hTotal hProject hSpoke
    exact Or.inl ⟨⟨R,by omega,none,by simp,fun _ => rfl,
      fun h => by rw [h,card_empty] at hPair; omega,fun _ w hw => (hOne w hw).ge,
      fun _ _ => hOne,fun u hu v hv _ => ⟨(hOne u hu).le,(hOne v hv).le⟩,
      fun v hv hn hp => Or.inl (hPay v hv hn hp),fun i => (hEnd i).imp_right Or.inl⟩⟩
  rcases hMode.resolve_right hPairMode with ⟨hInd,hStrict⟩
  have hNoPair (hc : active.card = 2) (hd : ∀ w ∈ active,6 ≤ G.degree w) : False :=
    hPairMode ⟨hc,hd⟩
  · by_cases hEmpty : active = ∅
    · rcases exists_empty_active_trimming_step G initial current hCurrent degree d floor testBudget
        hD hBound hDef hSize used j cap k budget hCap hUsed hTotal hSupport hCore hTest hNo hRetired
        (fun v hv high => by
          have hvI := hCurrent hv
          have hp : 0 < G.degree v := by rw [←hExact v hvI]; omega
          have h := hReserve v hvI (by simp [hEmpty]) hp
          change initial.card+2+k+2*B.card ≤ G.degree v
          omega) with ⟨R,special,hCount,hSpecial,_,hDebit,hSpend,hEnd⟩ | hSwitch
      · left
        change R.size ≤ B.card+1 at hCount
        refine ⟨⟨R,by omega,special,?_,?_,fun _ => hSpend,?_,
          fun hc hd => (hNoPair hc hd).elim,?_,?_,
          fun i => (hEnd i).imp_right Or.inr⟩⟩
        · intro v hv
          obtain ⟨hvc,hf⟩ := hSpecial v hv
          exact ⟨hvc,hf,by rw [hDebit v hvc,if_pos hv]⟩
        · simp [hEmpty]
        · simp [hEmpty]
        · simp [hEmpty]
        · intro v hv _ hPos
          right
          left
          by_contra hn
          rw [hDebit v hv,if_neg hn] at hPos
          omega
      · exact Or.inr ⟨hEmpty,hSwitch⟩
    by_cases hOne : active.card = 1
    · obtain ⟨w,hwA⟩ := card_eq_one.mp hOne
      have hw : w ∈ active := by rw [hwA]; exact mem_singleton_self _
      have hwTwo : 2 ≤ G.degree w := by
        obtain ⟨x,hx⟩ := (G.degree_pos_iff_exists_adj w).mp (hPos w hw)
        have hBound := hStrict w hw x hx
        rw [hwA,RobustExpansion.neighboursIn_eq_filter_card,filter_singleton,if_pos hx.symm,card_singleton]
          at hBound
        omega
      obtain ⟨R,hRCount,_,_,_,hProgress,hSmall,hPays,hEnd⟩ :=
        exists_singleton_trimming_step G initial current hCurrent w (hActive hw) hwTwo
          degree d hD hBound hExact hDef hCore₃ used j cap k budget hCap hUsed hTotal hCore
          (fun v hv hne hp => by
            have h := hReserve v hv (by simpa [hwA] using hne) hp
            omega) hRetired
      left
      change R.size ≤ B.card+1 at hRCount
      refine ⟨⟨R,by omega,none,by simp,fun _ => rfl,fun h => (hEmpty h).elim,
        ?_,fun hc hd => (hNoPair hc hd).elim,?_,?_,?_⟩⟩
      · intro h v hv
        rw [hwA,mem_singleton] at hv
        exact hv ▸ hProgress (h.resolve_left (by omega))
      · intro u hu v hv hEdge
        exact (hInd hu hv hEdge.ne hEdge).elim
      · intro v hv hn hp
        have hne : v ≠ w := fun h => hn (h.symm ▸ hw)
        rcases hPays v hv hne hp with he | ⟨hGap,hDebit⟩
        · exact Or.inl ⟨w,hw,he⟩
        · obtain ⟨hc,hwD⟩ := hSmall v hv hGap
          exact Or.inr (Or.inr ⟨w,hwA,hGap,hc,hwD,hDebit⟩)
      · intro i
        exact (hEnd i).imp_right (fun h => h.imp_left (fun he => ⟨w,hw,he⟩))
    have hMany : 2 ≤ active.card := by
      have hPosCard := card_pos.mpr (nonempty_iff_ne_empty.mpr hEmpty)
      omega
    obtain ⟨R,hCount,_,hProgress,_,hEnd,hPay⟩ :=
      exists_independent_trimming_prescription G initial current active hCurrent hActive
        hInd hStrict hPos hMany hCore₃ degree d hD hBound hExact hDef
        used j cap k budget hCap hUsed hTotal hProject hSpoke
    exact Or.inl ⟨⟨R,by omega,none,by simp,fun _ => rfl,fun h => (hEmpty h).elim,fun _ => hProgress,
      fun hc hd => (hNoPair hc hd).elim,
      fun u hu v hv he => (hInd hu hv he.ne he).elim,
      fun v hv hn hp => Or.inl (hPay v hv hn hp),fun i => (hEnd i).imp_right Or.inl⟩⟩

/-- Append the selected prescription to the previous virtual records
and update the support and exceptional set without a packed layer. -/
theorem TrimmingStepSelection.append_virtual_round
    (S C : SimpleGraph V) {initial current active : Finset V}
    {degree : V → ℕ} {d floor j cap : ℕ} {used : ℕ → Finset V}
    (R : TrimmingStepSelection (sdiff S C) initial current active degree d floor used j cap)
    (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (threshold : ℕ)
    (hC : C ≤ S)
    (hDegree : ∀ v,degree v+C.degree v = auxiliaryPhysicalDegree S initial P credit j v)
    (hCore : ∀ v,v ∉ initial → 2 ≤ degree v) :
    let P' := Function.update P j R.round.words.prescribedGraph
    let credit' := Function.update credit j (R.round.words.degreeCredit R.round.omitted)
    let next := sdiff (sdiff S C) (P' j)
    let record := auxiliaryPhysicalDegree next initial P' credit' (j+1)
    let support := univ.filter (fun v => 0 < record v)
    let exceptional := nextTrimmingExceptional current support record (d-2) threshold
    (∀ i < j,P' i = P i ∧ credit' i = credit i) ∧
    (∀ v,record v ≤ d-2 ∧
      record v+C.degree v+(2-credit' j v) = auxiliaryPhysicalDegree S initial P credit j v) ∧
    exceptional ⊆ current ∧ exceptional ⊆ support := by
  intro P' credit' next record support exceptional
  have hOld (i : ℕ) (hi : i < j) : P' i = P i ∧ credit' i = credit i :=
    ⟨Function.update_of_ne hi.ne _ _,Function.update_of_ne hi.ne _ _⟩
  have hPrefix (v : V) : auxiliaryPhysicalDegree S initial P' credit' j v =
      auxiliaryPhysicalDegree S initial P credit j v := by
    unfold auxiliaryPhysicalDegree
    split
    · rfl
    · congr 1
      apply sum_congr rfl
      intro i _
      rw [(hOld i.val i.isLt).1,(hOld i.val i.isLt).2]
  have hNewP : P' j = R.round.words.prescribedGraph := Function.update_self _ _ _
  have hNewCredit : credit' j = R.round.words.degreeCredit R.round.omitted := Function.update_self _ _ _
  have hClean (v : V) : auxiliaryPhysicalDegree S initial P' credit' j v-C.degree v = degree v := by
    rw [hPrefix,←hDegree,Nat.add_sub_cancel]
  have hRoom (v : V) : C.degree v ≤ auxiliaryPhysicalDegree S initial P' credit' j v := by
    rw [hPrefix,←hDegree]
    exact Nat.le_add_left _ _
  refine ⟨hOld,?_,?_,?_⟩
  · intro v
    have hCap := (R.round.next_degree_record S C initial degree d P' credit' j hC
      hNewP hNewCredit hClean v).2
    have hExact := R.round.next_degree_record_add_debits S C initial degree d P' credit' j hC
      hNewP hNewCredit hClean hRoom hCore v
    change record v+C.degree v+(2-credit' j v) = _ at hExact
    rw [hPrefix] at hExact
    exact ⟨hCap,hExact⟩
  · exact (filter_subset _ _).trans inter_subset_left
  · exact (filter_subset _ _).trans inter_subset_right

end OverfullWork.CMSTrimmingRound
