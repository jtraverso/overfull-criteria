module

public import OverfullWork.CMSOperation41RoundPrescription
public import OverfullWork.CMSOperation41SpokeOnlyRounds

@[expose] public section


/-! The empty-active cases use the same prescription checks as the
other rounds. An omitted core vertex has two credits. A spoke centre
has none, including when it is the special exceptional vertex. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2600000 in
theorem exists_spoke_trimming_prescription (G : SimpleGraph V) [DecidableRel G.Adj]
    (U B : Finset V) (hBU : B ⊆ U) (I : Finset ↥(Uᶜ : Finset V))
    (degree : V → ℕ) (d : ℕ) (hBound : ∀ v,degree v ≤ d)
    (hExcluded : ∀ v ∈ U,v ∉ B → degree v+2 ≤ d)
    (hOmitted : ∀ v ∈ I,degree v.val+2 ≤ d)
    (hSize : 3 ≤ Uᶜ.card-I.card+B.card) (hParity : Even (Uᶜ.card-I.card+B.card))
    (hFew : I.card ≤ 1) (used : ℕ → Finset V) (j cap k budget : ℕ)
    (hCap : 0 < cap) (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hRoom : ∀ v ∈ B,U.card+I.card+k+2*B.card ≤ G.degree v) :
    ∃ R : TrimmingRoundPrescription G U degree d,
      R.size = B.card ∧ R.omitted = I ∧ R.words.gaps = ∅ ∧
      (∀ v,(∃ i,v ∈ R.words.body i) ↔ v ∈ B) ∧
      ∀ i,projectionLoad (range j) used (R.words.endpoint i).val < cap := by
  let inc : ↥(Uᶜ : Finset V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨S,hGap,hLength,hRetain,hFresh,hBody,hCentres⟩ :=
    exists_spoke_only_round G U B (I.map inc) hBU used j cap k budget hCap hUsed hTotal
      (by simpa only [card_map] using hRoom)
  have hCore : S.coreIncidentGaps = ∅ := by simp [TrimmingReplacementWords.coreIncidentGaps,hGap]
  have hGapZero (v : V) : (trimmingGapGraph S.gaps).degree v = 0 := by
    simp [hGap,trimming_gap_degree_eq_card_incident_pairs]
  let R : TrimmingRoundPrescription G U degree d :=
    { size := B.card
      words := S
      omitted := I
      endpoints_retained := fun i hi => hRetain i (mem_map.mpr ⟨_,hi,rfl⟩)
      core_credit_bound := by simpa only [hCore,card_empty,add_zero] using hFew
      empty_body_is_gap := by
        intro i h
        have he := hBody i
        rw [h,List.length_nil] at he
        omega
      minimum_length := by simpa only [hLength] using hSize
      even_or_gap := Or.inl (by simpa only [hLength] using hParity)
      degree_cap := by
        intro v
        by_cases hv : v ∈ U
        · by_cases hIn : v ∈ B
          · rw [TrimmingReplacementWords.degreeCredit,if_pos (Or.inr ((hCentres v).mpr hIn)),
                hGapZero,Nat.add_zero]
            exact hBound v
          · exact (Nat.add_le_add_left (S.degree_credit_le_two I v) _).trans (hExcluded v hv hIn)
        · let x : ↥(Uᶜ : Finset V) := ⟨v,mem_compl.mpr hv⟩
          by_cases hIn : x ∈ I
          · have hCredit : S.degreeCredit I v = 2 := S.degree_credit_eq_two_at_omitted_core I x hIn
            rw [hCredit]
            exact hOmitted x hIn
          · have hCredit : S.degreeCredit I v = 0 :=
              (S.degree_credit_eq_gaps_at_retained_core I x hIn).trans (hGapZero v)
            rw [hCredit,Nat.add_zero]
            exact hBound v }
  exact ⟨R,rfl,rfl,hGap,hCentres,hFresh⟩

set_option maxHeartbeats 5000000 in
theorem exists_charged_pair_trimming_prescription (G : SimpleGraph V) [DecidableRel G.Adj]
    (U B : Finset V) (hBU : B ⊆ U) (degree : V → ℕ) (d : ℕ)
    (a b : V) (hab : a ≠ b) (ha : a ∈ U → a ∈ B) (hb : b ∈ U → b ∈ B)
    (hDefA : degree a < d) (hDefB : degree b < d) (hBound : ∀ v,degree v ≤ d)
    (hExcluded : ∀ v ∈ U,v ∉ B → degree v+2 ≤ d) (hSize : 3 ≤ Uᶜ.card)
    (used : ℕ → Finset V) (j cap k budget : ℕ)
    (hCap : 0 < cap) (hUsed : ∀ i < j,(used i).card ≤ budget) (hTotal : j*budget ≤ k*cap)
    (hRoom : ∀ v ∈ B,U.card+2+k+2*B.card ≤ G.degree v) :
    ∃ R : TrimmingRoundPrescription G U degree d,
      R.size ≤ B.card+1 ∧ R.omitted = ∅ ∧ R.words.gaps = {s(a,b)} ∧
      (∀ v,(∃ i,v ∈ R.words.body i) ↔ v ∈ B) ∧
      ∀ i,projectionLoad (range j) used (R.words.endpoint i).val < cap ∨
        ((R.words.endpoint i).val = a ∨ (R.words.endpoint i).val = b) := by
  let A : Finset V := {a,b}
  let a' : A := ⟨a,mem_insert_self _ _⟩
  let b' : A := ⟨b,by simp [A]⟩
  have hCard : A.card = 2 := card_pair hab
  obtain ⟨P,hFresh⟩ := exists_projection_with_free_load_cap G A U ∅ (range j) used cap k budget
    hCap (fun i hi => hUsed i (mem_range.mp hi)) (by simpa only [card_range] using hTotal)
    (fun v hv => by
      obtain ⟨hvA,hvU⟩ := mem_inter.mp hv
      have hvB : v ∈ B := by
        rcases (show v = a ∨ v = b by simpa [A] using hvA) with rfl | rfl
        · exact ha hvU
        · exact hb hvU
      have h := hRoom v hvB
      rw [hCard,card_empty]
      omega)
  obtain ⟨S,hSa,hSb,hGap,hBody⟩ :=
    exists_charged_pair_prescription P a' b' (fun h => hab (congrArg Subtype.val h))
  have hOccurrences (v : V) : v ∈ S.body 0 ↔ v ∈ U ∧ v ∈ A := by
    refine ⟨fun h => ⟨S.outside 0 v h,by simpa [A] using hBody v h⟩,?_⟩
    rintro ⟨hv,hvA⟩
    have he : s(a,b) ∈ S.gaps := by rw [hGap]; exact mem_singleton_self _
    obtain ⟨i,x,y,heq,hWord⟩ := S.gap_witness _ he
    have hIndex : i = 0 := Subsingleton.elim _ _
    subst i
    have hvEdge : v ∈ s(a,b) := Sym2.mem_iff.mpr (by simpa [A] using hvA)
    have hvEdge' : v ∈ s(x,y) := by rwa [←heq]
    have hvWord : v ∈ S.word 0 := hWord.mem (by simpa using Sym2.mem_iff.mp hvEdge')
    rcases List.mem_cons.mp hvWord with h | h
    · exact (mem_compl.mp (S.endpoint (0,false)).property (h ▸ hv)).elim
    · rcases List.mem_append.mp h with h | h
      · exact h
      · exact (mem_compl.mp (S.endpoint (0,true)).property ((List.mem_singleton.mp h) ▸ hv)).elim
  have hEmpty (i : Fin 1) (hi : S.body i = []) :
      s((S.endpoint (i,false)).val,(S.endpoint (i,true)).val) ∈ S.gaps := by
    have he : s(a,b) ∈ S.gaps := by rw [hGap]; exact mem_singleton_self _
    obtain ⟨i',x,y,heq,hWord⟩ := S.gap_witness _ he
    have hIndex : i' = i := Subsingleton.elim _ _
    subst i'
    have hWordEq : S.word i = [(S.endpoint (i,false)).val,(S.endpoint (i,true)).val] := by
      simp [TrimmingReplacementWords.word,hi]
    change List.IsInfix [x,y] (S.word i) at hWord
    rw [hWordEq] at hWord
    obtain ⟨before,after,hEq⟩ := hWord
    have hLen := congrArg List.length hEq
    simp only [List.length_append,List.length_cons,List.length_nil] at hLen
    have hBefore : before = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hAfter : after = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [hBefore,hAfter,List.nil_append,List.append_nil,List.cons.injEq] at hEq
    rw [←hEq.1,←hEq.2.1,←heq]
    exact he
  let B' := B \ A
  have hB' : B' ⊆ B := sdiff_subset
  have hBCard := card_le_card hB'
  obtain ⟨T,hTGap,hEnds,hOld,hNew,_,hSpokes⟩ :=
    S.exists_with_retired_spokes B' ∅ (hB'.trans hBU)
      (fun i v h hBmem => by
        have hi : i = 0 := Subsingleton.elim _ _
        exact (mem_sdiff.mp hBmem).2 ((hOccurrences v).mp (hi ▸ h)).2)
      (fun _ => notMem_empty _) used j cap k budget hCap hUsed hTotal
      (fun v hv => by
        have h := hRoom v (hB' hv)
        simp only [Fintype.card_fin,card_empty]
        omega)
  let coord : Fin (1+B'.card) ≃ Fin 1 ⊕ ↥B' := (Fintype.equivFinOfCardEq (by simp)).symm
  let L := T.reindex coord
  have hLGap : L.gaps = {s(a,b)} := hTGap.trans hGap
  have hLBody (v : V) : (∃ i,v ∈ L.body i) ↔ v ∈ B := by
    constructor
    · rintro ⟨i,hi⟩
      change v ∈ T.body (coord i) at hi
      cases h : coord i with
      | inl t =>
        have ht : t = 0 := Subsingleton.elim _ _
        rw [h,hOld,ht] at hi
        obtain ⟨hU,hA⟩ := (hOccurrences v).mp hi
        rcases (show v = a ∨ v = b by simpa [A] using hA) with rfl | rfl
        · exact ha hU
        · exact hb hU
      | inr z =>
        rw [h,hNew,List.mem_singleton] at hi
        exact hB' (hi.symm ▸ z.property)
    · intro hv
      by_cases hvA : v ∈ A
      · refine ⟨coord.symm (Sum.inl 0),?_⟩
        change v ∈ T.body (coord (coord.symm (Sum.inl 0)))
        rw [Equiv.apply_symm_apply,hOld,hOccurrences]
        exact ⟨hBU hv,hvA⟩
      · let z : ↥B' := ⟨v,mem_sdiff.mpr ⟨hv,hvA⟩⟩
        refine ⟨coord.symm (Sum.inr z),?_⟩
        change v ∈ T.body (coord (coord.symm (Sum.inr z)))
        rw [Equiv.apply_symm_apply,hNew]
        exact List.mem_cons_self
  let R : TrimmingRoundPrescription G U degree d :=
    { size := 1+B'.card
      words := L
      omitted := ∅
      endpoints_retained := fun _ => notMem_empty _
      core_credit_bound := by
        rw [card_empty,zero_add]
        exact (card_le_card (filter_subset _ _)).trans (by rw [hLGap,card_singleton])
      empty_body_is_gap := by
        intro i h
        change T.body (coord i) = [] at h
        change s((T.endpoint (coord i,false)).val,(T.endpoint (coord i,true)).val) ∈ T.gaps
        cases he : coord i with
        | inl t =>
          rw [he,hOld] at h
          rw [hEnds,hEnds,hTGap]
          exact hEmpty t h
        | inr z =>
          rw [he,hNew] at h
          cases h
      minimum_length := by
        rw [card_empty,Nat.sub_zero]
        exact hSize.trans (Nat.le_add_right _ _)
      even_or_gap := Or.inr (by rw [hLGap]; exact ⟨_,mem_singleton_self _⟩)
      degree_cap := by
        intro v
        by_cases hSupported : (∃ x ∉ (∅ : Finset ↥(Uᶜ : Finset V)),x.val = v) ∨ ∃ i,v ∈ L.body i
        · rw [TrimmingReplacementWords.degreeCredit,if_pos hSupported,hLGap,trimming_gap_degree_of_single_pair hab]
          split_ifs with h
          · rcases h with rfl | rfl
            · omega
            · omega
          · simpa only [Nat.add_zero] using hBound v
        · have hvU : v ∈ U := by
            by_contra hv
            exact hSupported (Or.inl ⟨⟨v,mem_compl.mpr hv⟩,notMem_empty _,rfl⟩)
          have hvB : v ∉ B := fun h => hSupported (Or.inr ((hLBody v).mpr h))
          rw [TrimmingReplacementWords.degreeCredit,if_neg hSupported]
          exact hExcluded v hvU hvB }
  refine ⟨R,by change 1+B'.card ≤ B.card+1; omega,rfl,hLGap,hLBody,?_⟩
  rintro ⟨i,side⟩
  change projectionLoad (range j) used (T.endpoint (coord i,side)).val < cap ∨
    ((T.endpoint (coord i,side)).val = a ∨ (T.endpoint (coord i,side)).val = b)
  cases he : coord i with
  | inl t =>
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rw [hEnds]
    cases side
    · rw [hSa]
      by_cases h : a ∈ U
      · exact Or.inl (hFresh a' h)
      · exact Or.inr (Or.inl (P.fixed a' h))
    · rw [hSb]
      by_cases h : b ∈ U
      · exact Or.inl (hFresh b' h)
      · exact Or.inr (Or.inr (P.fixed b' h))
  | inr z => exact Or.inl (hSpokes z side)

end OverfullWork.CMSTrimmingRound
