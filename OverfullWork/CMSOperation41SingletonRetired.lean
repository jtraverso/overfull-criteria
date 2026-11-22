module

public import OverfullWork.CMSOperation41EmptyActiveRounds
public import OverfullWork.CMSOperation41RetiredPool
public import OverfullWork.CMSOperation41SingletonChoice
public import OverfullWork.CMSOperation41SingletonRounds

@[expose] public section


/-! Singleton branches of Step 2, with the retired centres of S2.5. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1300000 in
theorem exists_singleton_prescription_with_retired_spokes
    (G : SimpleGraph V) [DecidableRel G.Adj] (U B : Finset V) (hBU : B ⊆ U)
    {w a b : V} (hw : w ∈ U) (hwB : w ∉ B) (hwa : G.Adj w a) (hwb : w ≠ b) (hab : a ≠ b)
    (omitEdge : Bool) (hActual : omitEdge = false → G.Adj w b)
    (degree : V → ℕ) (d : ℕ) (hBound : ∀ v,degree v ≤ d)
    (hDef : ∀ v ∈ U,v ∉ B → degree v+2 ≤ d)
    (hCharged : omitEdge = true → degree b < d)
    (hSize : 3 ≤ Uᶜ.card)
    (hParity : omitEdge = false → Even (Uᶜ ∪ B ∪ {w,a,b}).card)
    (used : ℕ → Finset V) (j cap k budget : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hProjection : ∀ v ∈ ({a,b} : Finset V),v ∈ U → U.card+2+k ≤ G.degree v)
    (hRoom : ∀ v ∈ B,U.card+2+k+2*B.card ≤ G.degree v) :
    ∃ R : TrimmingRoundPrescription G U degree d,
      R.size ≤ B.card+1 ∧ R.omitted = ∅ ∧
      R.words.gaps = (if omitEdge then {s(w,b)} else ∅) ∧
      R.words.prescribedGraph.degree w = (if omitEdge then 1 else 2) ∧
      (∀ v,(∃ i,v ∈ R.words.body i) ↔ v ∈ B ∨ (v ∈ U ∧ v ∈ ({w,a,b} : Finset V))) ∧
      (∀ v ∈ U,v ∉ B → v ≠ w → 0 < R.words.prescribedGraph.degree v →
        R.words.prescribedGraph.Adj w v ∨ (s(w,v) ∈ R.words.gaps ∧ R.words.prescribedGraph.degree v = 1)) ∧
      ∀ i,projectionLoad (range j) used (R.words.endpoint i).val < cap ∨
        R.words.prescribedGraph.Adj w (R.words.endpoint i).val ∨
        0 < R.words.degreeCredit R.omitted (R.words.endpoint i).val := by
  let A : Finset V := {w,a,b}
  obtain ⟨S,hGap,hBody,hA,hB,_,_,hFirst,hLast⟩ :=
    exists_capped_singleton_round_with_leaf_positions G U ∅ hw hwa hwb hab omitEdge hActual
      used j cap k budget hCap hUsed hTotal (by simpa only [card_empty,add_zero] using hProjection)
  have hBodySet (v : V) : v ∈ S.body 0 ↔ v ∈ U ∧ v ∈ A := by
    simpa [A] using hBody v
  let B' := B \ A
  have hSub : B' ⊆ B := sdiff_subset
  have hCard := card_le_card hSub
  obtain ⟨T,hTG,hEnds,hOld,hNew,_,hFresh⟩ := S.exists_with_retired_spokes B' ∅
    (hSub.trans hBU)
    (fun i v hv hvB => (mem_sdiff.mp hvB).2 ((hBodySet v).mp ((Subsingleton.elim i 0) ▸ hv)).2)
    (fun _ => notMem_empty _) used j cap k budget hCap hUsed hTotal (fun v hv => by
      have h := hRoom v (hSub hv)
      simp only [Fintype.card_fin,card_empty]
      omega)
  let coord : Fin (1+B'.card) ≃ Fin 1 ⊕ ↥B' := (Fintype.equivFinOfCardEq (by simp)).symm
  let L := T.reindex coord
  have hLG : L.gaps = (if omitEdge then {s(w,b)} else ∅) := hTG.trans hGap
  have hOldEdges : S.prescribedGraph ≤ L.prescribedGraph := by
    intro u v h
    obtain ⟨hNot,i,hPair⟩ := (S.prescribedGraph_adj u v).mp h
    apply (L.prescribedGraph_adj u v).mpr
    refine ⟨by rwa [show L.gaps = S.gaps from hTG],coord.symm (Sum.inl i),?_⟩
    have hWord : L.word (coord.symm (Sum.inl i)) = S.word i := by
      change T.word (coord (coord.symm (Sum.inl i))) = S.word i
      rw [Equiv.apply_symm_apply]
      simp only [TrimmingReplacementWords.word,hEnds,hOld]
    rwa [hWord]
  have hCovers (v : V) : (∃ i,v ∈ L.body i) ↔ v ∈ B ∨ (v ∈ U ∧ v ∈ A) := by
    constructor
    · rintro ⟨i,hi⟩
      change v ∈ T.body (coord i) at hi
      cases h : coord i with
      | inl t =>
        rw [h,hOld,Subsingleton.elim t 0] at hi
        exact Or.inr ((hBodySet v).mp hi)
      | inr z =>
        rw [h,hNew,List.mem_singleton] at hi
        exact Or.inl (hSub (hi.symm ▸ z.property))
    · intro hv
      by_cases hvA : v ∈ A
      · have hvU := hv.elim (hBU ·) And.left
        refine ⟨coord.symm (Sum.inl 0),?_⟩
        change v ∈ T.body (coord (coord.symm (Sum.inl 0)))
        rw [Equiv.apply_symm_apply,hOld,hBodySet]
        exact ⟨hvU,hvA⟩
      · have hvB := hv.resolve_right (fun h => hvA h.2)
        let z : B' := ⟨v,mem_sdiff.mpr ⟨hvB,hvA⟩⟩
        refine ⟨coord.symm (Sum.inr z),?_⟩
        change v ∈ T.body (coord (coord.symm (Sum.inr z)))
        rw [Equiv.apply_symm_apply,hNew]
        exact List.mem_cons_self
  have hLength : Uᶜ.card+∑ i,(L.body i).length = (Uᶜ ∪ B ∪ A).card := by
    have hSum : (∑ i,(L.body i).length) = (S.body 0).length+B'.card := by
      change (∑ i,(T.body (coord i)).length) = _
      rw [Equiv.sum_comp coord (fun i => (T.body i).length),Fintype.sum_sum_type]
      simp [hOld,hNew]
    have hBodyFinset : (S.body 0).toFinset = U ∩ A := by
      ext v
      simp [hBodySet]
    have hSplit : Uᶜ ∪ B ∪ A = Uᶜ ∪ ((U ∩ A) ∪ B') := by
      ext v
      simp only [B',mem_union,mem_inter,mem_sdiff,mem_compl]
      by_cases hv : v ∈ U
      · simp only [hv,not_true_eq_false,false_or,true_and]
        by_cases ha : v ∈ A <;> simp [ha]
      · simp [hv]
    have hDis : Disjoint (U ∩ A) B' :=
      disjoint_left.mpr (fun _ hv hv' => (mem_sdiff.mp hv').2 (mem_inter.mp hv).2)
    have hDisCore : Disjoint Uᶜ ((U ∩ A) ∪ B') := by
      apply Finset.disjoint_left.mpr
      intro v hv hv'
      exact mem_compl.mp hv ((mem_union.mp hv').elim (fun h => (mem_inter.mp h).1) (fun h => hBU (hSub h)))
    rw [hSplit,card_union_of_disjoint hDisCore,card_union_of_disjoint hDis,hSum,
      ←hBodyFinset,List.toFinset_card_of_nodup (S.simple 0)]
  have hGapDegree (v : V) : (trimmingGapGraph L.gaps).degree v =
      if omitEdge then (if v = w ∨ v = b then 1 else 0) else 0 := by
    rw [hLG]
    cases omitEdge
    · simp [trimming_gap_degree_eq_card_incident_pairs]
    · exact trimming_gap_degree_of_single_pair hwb v
  have hRetainedCredit (v : V)
      (hv : v ∉ U ∨ ∃ i,v ∈ L.body i) :
      L.degreeCredit ∅ v = (trimmingGapGraph L.gaps).degree v := by
    apply if_pos
    exact hv.elim (fun h => Or.inl ⟨⟨v,mem_compl.mpr h⟩,notMem_empty _,rfl⟩) Or.inr
  have hOrdCredit (v : V) (hv : v ∉ U) := hRetainedCredit v (Or.inl hv)
  have hRetainedCap (v : V) (hvw : v ≠ w) (hv : v ∉ U ∨ ∃ i,v ∈ L.body i) :
      degree v+L.degreeCredit ∅ v ≤ d := by
    rw [hRetainedCredit v hv,hGapDegree]
    by_cases hvb : v = b
    · subst v
      cases h : omitEdge
      · simpa [h] using hBound b
      · simpa [h] using hCharged h
    · have hNot : ¬(v = w ∨ v = b) := fun h => h.elim hvw hvb
      cases omitEdge <;> simpa [hNot] using hBound v
  have hDebit : L.prescribedGraph.degree w = (if omitEdge then 1 else 2) := by
    have hCredit := hRetainedCredit w (Or.inr ((hCovers w).mpr (Or.inr ⟨hw,mem_insert_self _ _⟩)))
    have hBalance := L.prescribed_degree_add_credit_on_exceptional ∅ hw
    rw [hCredit,hGapDegree,if_pos (Or.inl rfl)] at hBalance
    cases h : omitEdge <;> simp [h] at hBalance ⊢ <;> omega
  let R : TrimmingRoundPrescription G U degree d :=
    { size := 1+B'.card
      words := L
      omitted := ∅
      endpoints_retained := fun _ => notMem_empty _
      core_credit_bound := by
        rw [card_empty,zero_add]
        apply (card_le_card (filter_subset _ _)).trans
        rw [hLG]
        split <;> simp
      empty_body_is_gap := by
        intro i hi
        change T.body (coord i) = [] at hi
        cases h : coord i with
        | inl t =>
          rw [h,hOld,Subsingleton.elim t 0] at hi
          have hwMem := (hBodySet w).mpr ⟨hw,mem_insert_self _ _⟩
          rw [hi] at hwMem
          simp at hwMem
        | inr z => rw [h,hNew] at hi; cases hi
      minimum_length := by simpa only [card_empty,Nat.sub_zero] using hSize.trans (Nat.le_add_right _ _)
      even_or_gap := by
        cases h : omitEdge
        · exact Or.inl (by simpa only [card_empty,Nat.sub_zero,hLength] using hParity h)
        · exact Or.inr (by simp [hLG,h])
      degree_cap := by
        intro v
        by_cases hvU : v ∈ U
        · by_cases hvB : v ∈ B
          · exact hRetainedCap v (fun h => hwB (h ▸ hvB)) (Or.inr ((hCovers v).mpr (Or.inl hvB)))
          · exact (Nat.add_le_add_left (L.degree_credit_le_two ∅ v) _).trans (hDef v hvU hvB)
        · exact hRetainedCap v (fun h => hvU (h.symm ▸ hw)) (Or.inl hvU) }
  refine ⟨R,?_,rfl,hLG,hDebit,fun v => hCovers v,?_,?_⟩
  · change 1+B'.card ≤ B.card+1
    omega
  · intro v hvU hvB hvw hPos
    have hvBody : ∃ i,v ∈ L.body i := by
      by_contra! h
      have hZero := L.prescribed_degree_eq_zero_of_absent_body hvU h
      change 0 < L.prescribedGraph.degree v at hPos
      omega
    have hV : v = w ∨ v = a ∨ v = b := by
      have h := ((hCovers v).mp hvBody).resolve_left hvB
      simpa [A] using h.2
    rcases hV.resolve_left hvw with h | h
    · exact Or.inl (h.symm ▸ hOldEdges hFirst)
    · subst v
      cases h : omitEdge
      · exact Or.inl (hOldEdges (hLast h))
      · change L.prescribedGraph.Adj w b ∨ (s(w,b) ∈ L.gaps ∧ L.prescribedGraph.degree b = 1)
        have hGaps : L.gaps = {s(w,b)} := hLG.trans (if_pos h)
        have hG : (trimmingGapGraph L.gaps).degree b = 1 := by
          have he := trimming_gap_degree_of_single_pair hwb b
          rw [if_pos (Or.inr rfl)] at he
          rwa [hGaps]
        have hCredit := (hRetainedCredit b (Or.inr hvBody)).trans hG
        have hBalance := L.prescribed_degree_add_credit_on_exceptional ∅ hvU
        rw [hCredit] at hBalance
        exact Or.inr ⟨hGaps.symm ▸ mem_singleton_self _,by omega⟩
  · rintro ⟨i,side⟩
    change projectionLoad (range j) used (T.endpoint (coord i,side)).val < cap ∨
      L.prescribedGraph.Adj w (T.endpoint (coord i,side)).val ∨
      0 < L.degreeCredit ∅ (T.endpoint (coord i,side)).val
    cases h : coord i with
    | inl t =>
      rw [hEnds,Subsingleton.elim t 0]
      cases side
      · by_cases ha : a ∈ U
        · exact Or.inl (by simpa [ha] using hA)
        · exact Or.inr (Or.inl ((show (S.endpoint (0,false)).val = a by simpa [ha] using hA).symm ▸
            hOldEdges hFirst))
      · by_cases hb : b ∈ U
        · exact Or.inl (by simpa [hb] using hB)
        · rw [show (S.endpoint (0,true)).val = b by simpa [hb] using hB]
          cases hO : omitEdge
          · exact Or.inr (Or.inl (hOldEdges (hLast hO)))
          · exact Or.inr (Or.inr (by rw [hOrdCredit b hb,hGapDegree]; simp [hO]))
    | inr z => exact Or.inl (hFresh z side)

set_option maxHeartbeats 4200000 in
/-- All three singleton alternatives of Step 2, with the ordinary and
retired pool computed from the current degree record. -/
theorem exists_singleton_trimming_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (initial current : Finset V) (hCurrent : current ⊆ initial)
    (w : V) (hw : w ∈ current) (hTwo : 2 ≤ G.degree w)
    (degree : V → ℕ) (d : ℕ) (hD : 2 ≤ d) (hBound : ∀ v,degree v ≤ d)
    (hExact : ∀ v ∈ initial,degree v = G.degree v)
    (hDef : ∀ v ∈ current,degree v+2 ≤ d) (hSize : 3 ≤ initialᶜ.card)
    (used : ℕ → Finset V) (j cap k budget : ℕ)
    (hCap : 0 < cap) (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap) :
    let support := univ.filter (fun v => 0 < degree v)
    let B := retiredTrimmingPool initial current support
    initialᶜ ⊆ support →
    (∀ v ∈ initial,v ≠ w → 0 < G.degree v → initial.card+2+k ≤ G.degree v) →
    (∀ v ∈ B,initial.card+2+k+2*B.card ≤ G.degree v) →
    ∃ R : TrimmingRoundPrescription G initial degree d,
      R.size ≤ B.card+1 ∧ R.omitted = ∅ ∧
      (∀ v ∈ B,∃ i,v ∈ R.words.body i) ∧
      R.words.prescribedGraph.degree w ≤ 2 ∧
      (Odd (support \ current).card → 1 ≤ R.words.prescribedGraph.degree w) ∧
      (∀ x ∈ current,s(w,x) ∈ R.words.gaps →
        G.degree w < current.card+2 ∧ R.words.prescribedGraph.degree w = 1) ∧
      (∀ x ∈ current,x ≠ w → 0 < R.words.prescribedGraph.degree x →
        R.words.prescribedGraph.Adj w x ∨ (s(w,x) ∈ R.words.gaps ∧ R.words.prescribedGraph.degree x = 1)) ∧
      ∀ i,projectionLoad (range j) used (R.words.endpoint i).val < cap ∨
        R.words.prescribedGraph.Adj w (R.words.endpoint i).val ∨
        0 < R.words.degreeCredit R.omitted (R.words.endpoint i).val := by
  intro support B hCore hProjection hRoom
  let X := support \ current
  have hwInitial := hCurrent hw
  have hwX : w ∉ X := fun h => (mem_sdiff.mp h).2 hw
  have hBI : B ⊆ initial := fun _ h => (mem_inter.mp (mem_sdiff.mp h).1).2
  have hwB : w ∉ B := fun h => (mem_sdiff.mp h).2 hw
  have hParts := ordinary_and_retired_trimming_partition initial current support hCurrent hCore
  change X = initialᶜ ∪ B ∧ Disjoint initialᶜ B at hParts
  have hExclude (v : V) (hv : v ∈ initial) (hvB : v ∉ B) : degree v+2 ≤ d := by
    by_cases hvC : v ∈ current
    · exact hDef v hvC
    · have hvSupp : v ∉ support := fun h => hvB (mem_sdiff.mpr ⟨mem_inter.mpr ⟨h,hv⟩,hvC⟩)
      have hn : ¬0 < degree v := fun h => hvSupp (mem_filter.mpr ⟨mem_univ _,h⟩)
      omega
  have hPos (v : V) (hv : v ∈ X ∪ current) (hvI : v ∈ initial)
      (hCurrentPos : v ∈ current → 0 < G.degree v) : 0 < G.degree v := by
    rcases mem_union.mp hv with h | h
    · rw [←hExact v hvI]
      exact (mem_filter.mp (mem_sdiff.mp h).1).2
    · exact hCurrentPos h
  have hBuild {a b : V} (hwa : G.Adj w a) (hwb : w ≠ b) (hab : a ≠ b)
      (hbPos : b ∈ initial → 0 < G.degree b)
      (omitEdge : Bool) (hActual : omitEdge = false → G.Adj w b)
      (hCharged : omitEdge = true → degree b < d)
      (hChargeRoom : omitEdge = true → b ∈ current → G.degree w < current.card+2)
      (hParity : omitEdge = false → Even (initialᶜ ∪ B ∪ {w,a,b}).card) :
      ∃ R : TrimmingRoundPrescription G initial degree d,
        R.size ≤ B.card+1 ∧ R.omitted = ∅ ∧
        (∀ v ∈ B,∃ i,v ∈ R.words.body i) ∧
        R.words.prescribedGraph.degree w ≤ 2 ∧
        (Odd X.card → 1 ≤ R.words.prescribedGraph.degree w) ∧
        (∀ x ∈ current,s(w,x) ∈ R.words.gaps →
          G.degree w < current.card+2 ∧ R.words.prescribedGraph.degree w = 1) ∧
        (∀ x ∈ current,x ≠ w → 0 < R.words.prescribedGraph.degree x →
          R.words.prescribedGraph.Adj w x ∨ (s(w,x) ∈ R.words.gaps ∧ R.words.prescribedGraph.degree x = 1)) ∧
        ∀ i,projectionLoad (range j) used (R.words.endpoint i).val < cap ∨
          R.words.prescribedGraph.Adj w (R.words.endpoint i).val ∨
          0 < R.words.degreeCredit R.omitted (R.words.endpoint i).val := by
    have hProject (v : V) (hv : v ∈ ({a,b} : Finset V)) (hvI : v ∈ initial) :
        initial.card+2+k ≤ G.degree v := by
      rcases (show v = a ∨ v = b by simpa using hv) with h | h
      · exact h.symm ▸ hProjection a (h ▸ hvI) hwa.ne.symm
          ((G.degree_pos_iff_exists_adj a).mpr ⟨w,hwa.symm⟩)
      · exact h.symm ▸ hProjection b (h ▸ hvI) hwb.symm (hbPos (h ▸ hvI))
    obtain ⟨R,hRSize,hOmit,hGaps,hDebit,hBodies,hPay,hEnd⟩ :=
      exists_singleton_prescription_with_retired_spokes G initial B hBI
        hwInitial hwB hwa hwb hab omitEdge hActual degree d hBound hExclude hCharged
        hSize hParity used j cap k budget hCap hUsed hTotal hProject hRoom
    refine ⟨R,hRSize,hOmit,fun v hv => (hBodies v).mpr (Or.inl hv),
      by rw [hDebit]; split <;> decide,fun _ => by rw [hDebit]; split <;> decide,?_,?_,hEnd⟩
    · intro x hx hxGap
      rw [hGaps] at hxGap
      by_cases hO : omitEdge = true
      · rw [if_pos hO,mem_singleton] at hxGap
        have he : x = b := by simpa [hwb] using hxGap
        exact ⟨hChargeRoom hO (he ▸ hx),by simpa [hO] using hDebit⟩
      · simp [hO] at hxGap
    · intro x hx
      exact hPay x (hCurrent hx) (fun h => (mem_sdiff.mp h).2 hx)
  let N := G.neighborFinset w
  let limit := current.card+2
  let leaves := if limit ≤ G.degree w then N \ current else N
  have hN : N.card = G.degree w := card_neighborFinset_eq_degree _ _
  have hLeaves : 1 < leaves.card := by
    by_cases h : limit ≤ G.degree w
    · rw [show leaves = N \ current from if_pos h]
      have hCard := card_sdiff_add_card_inter N current
      have hInter := card_le_card (inter_subset_right : N ∩ current ⊆ current)
      change current.card+2 ≤ G.degree w at h
      omega
    · rw [show leaves = N from if_neg h]
      omega
  have hLeavesSub : leaves ⊆ N := by
    change (if limit ≤ G.degree w then N \ current else N) ⊆ N
    split
    · exact sdiff_subset
    · exact Subset.rfl
  have hAway (v : V) (hv : v ∈ leaves) (h : limit ≤ G.degree w) : v ∉ current :=
    (mem_sdiff.mp (show v ∈ N \ current from (if_pos h : leaves = N \ current) ▸ hv)).2
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp hLeaves
  have hwa := (mem_neighborFinset G w a).mp (hLeavesSub ha)
  have hwb := (mem_neighborFinset G w b).mp (hLeavesSub hb)
  have hAB (v : V) (hv : G.Adj w v) : v ∈ X ∪ current := by
    by_cases hc : v ∈ current
    · exact mem_union_right _ hc
    have hp : v ∈ support := by
      by_cases hi : v ∈ initial
      · apply mem_filter.mpr
        exact ⟨mem_univ _,by rw [hExact v hi]; exact (G.degree_pos_iff_exists_adj v).mpr ⟨w,hv.symm⟩⟩
      · exact hCore (mem_compl.mpr hi)
    exact mem_union_left _ (mem_sdiff.mpr ⟨hp,hc⟩)
  have hPool : (initialᶜ ∪ B ∪ ({w,a,b} : Finset V)) = insert w (insert a (insert b X)) := by
    rw [←hParts.1]
    ext v
    simp only [mem_union,mem_insert,mem_singleton]
    tauto
  by_cases hEven : Even (insert w (insert a (insert b X))).card
  · exact hBuild hwa hwb.ne hab (fun _ => (G.degree_pos_iff_exists_adj b).mpr ⟨w,hwb.symm⟩)
      false (fun _ => hwb) (by simp) (by simp) (fun _ => hPool.symm ▸ hEven)
  rcases singleton_odd_pool_choice X current degree d hw hwX (hAB a hwa) (hAB b hwb)
    hwa.ne.symm hwb.ne.symm (fun v hv => by have h := hDef v hv; omega)
    (Nat.not_even_iff_odd.mp hEven) with ⟨x,hx,hLow⟩ | ⟨_,_,hEvenX⟩
  · have hPartsX := mem_erase.mp hx
    have hxw := hPartsX.1
    have hxPos (hxI : x ∈ initial) : 0 < G.degree x := by
      rcases mem_insert.mp hPartsX.2 with h | h
      · exact h.symm ▸ (G.degree_pos_iff_exists_adj a).mpr ⟨w,hwa.symm⟩
      rcases mem_insert.mp h with h | h
      · exact h.symm ▸ (G.degree_pos_iff_exists_adj b).mpr ⟨w,hwb.symm⟩
      exact hPos x (mem_union_left _ h) hxI (fun h' => ((mem_sdiff.mp h).2 h').elim)
    have hxRoom (_ : true = true) (hxC : x ∈ current) : G.degree w < current.card+2 := by
      apply lt_of_not_ge
      intro h
      rcases mem_insert.mp hPartsX.2 with ha' | h'
      · exact hAway a ha h (ha' ▸ hxC)
      rcases mem_insert.mp h' with hb' | hxX
      · exact hAway b hb h (hb' ▸ hxC)
      · exact (mem_sdiff.mp hxX).2 hxC
    by_cases he : a = x
    · exact hBuild hwb hxw.symm (fun h => hab (he.trans h.symm)) hxPos
        true (by simp) (fun _ => hLow) hxRoom (by simp)
    · exact hBuild hwa hxw.symm he hxPos true (by simp) (fun _ => hLow) hxRoom (by simp)
  · have hCard : initialᶜ.card+B.card = X.card := by
      rw [hParts.1,card_union_of_disjoint hParts.2]
    obtain ⟨R,hRSize,hOmit,hGaps,hBodies,hFresh⟩ := exists_spoke_trimming_prescription G initial B
      hBI ∅ degree d hBound hExclude (by simp) (by simpa using hSize.trans (Nat.le_add_right _ _))
      (by simpa [hCard] using hEvenX) (by simp) used j cap k budget hCap hUsed hTotal
      (fun v hv => by have h := hRoom v hv; simp only [card_empty,add_zero]; omega)
    refine ⟨R,by rw [hRSize]; omega,hOmit,fun v hv => (hBodies v).mpr hv,
      by simpa [hwInitial] using R.words.prescribed_graph_degree_le w,
      fun ho => (Nat.not_even_iff_odd.mpr ho hEvenX).elim,
      by simp [hGaps], ?_,
      fun i => Or.inl (hFresh i)⟩
    intro x hx _ hp
    have hAbsent (i : Fin R.size) : x ∉ R.words.body i :=
      fun h => (mem_sdiff.mp ((hBodies x).mp ⟨i,h⟩)).2 hx
    have hZero := R.words.prescribed_degree_eq_zero_of_absent_body (hCurrent hx) hAbsent
    omega

end OverfullWork.CMSTrimmingRound
