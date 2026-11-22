module

public import OverfullWork.CMSOperation41ReplacementWords

@[expose] public section


/-! The deficit of the ordinary core in one trimming round comes from
omitted vertices and marked pairs with an ordinary endpoint. This is
the two-unit bound on the core used by Claim 4.2(4). -/
namespace OverfullWork.CMSTrimmingRound.TrimmingReplacementWords

open Finset SimpleGraph
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V I : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {U : Finset V}

/-- The marked pairs that can contribute to ordinary degree credits. -/
noncomputable def coreIncidentGaps (R : TrimmingReplacementWords G U I) : Finset (Sym2 V) :=
  R.gaps.filter (fun edge => ∃ v : ↥(Uᶜ : Finset V),v.val ∈ edge)

theorem core_incident_gaps_eq_empty_of_exceptional_pairs (R : TrimmingReplacementWords G U I)
    (hGaps : ∀ edge ∈ R.gaps,∃ a ∈ U,∃ b ∈ U,edge = s(a,b)) : R.coreIncidentGaps = ∅ := by
  apply eq_empty_of_forall_notMem
  intro edge he
  obtain ⟨hMem,v,hV⟩ := mem_filter.mp he
  obtain ⟨a,ha,b,hb,rfl⟩ := hGaps edge hMem
  exact mem_compl.mp v.property ((Sym2.mem_iff.mp hV).elim (fun h => h ▸ ha) (fun h => h ▸ hb))

set_option maxHeartbeats 2100000 in
theorem degree_credit_mass_le_omissions_and_incident_pairs (R : TrimmingReplacementWords G U I)
    (omitted : Finset ↥(Uᶜ : Finset V)) :
    (∑ v ∈ Uᶜ,R.degreeCredit omitted v) ≤ 2*(omitted.card+R.coreIncidentGaps.card) := by
  let C := ↥(Uᶜ : Finset V)
  let J := trimmingGapGraph R.gaps
  let count (edge : Sym2 V) : Finset C := univ.filter (fun v : C => v.val ∈ edge ∧ ¬edge.IsDiag)
  have hAcross : (∑ v : C,J.degree v.val) = ∑ edge ∈ R.gaps,(count edge).card := by
    calc
      _ = ∑ v : C,∑ edge ∈ R.gaps,if v.val ∈ edge ∧ ¬edge.IsDiag then (1:ℕ) else 0 := by
        apply sum_congr rfl
        intro v _
        rw [trimming_gap_degree_eq_card_incident_pairs,card_filter]
      _ = ∑ edge ∈ R.gaps,∑ v : C,if v.val ∈ edge ∧ ¬edge.IsDiag then (1:ℕ) else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro edge _
        dsimp only [count]
        rw [card_filter]
  have hRow (edge : Sym2 V) (he : edge ∈ R.gaps) : (count edge).card ≤
      if edge ∈ R.coreIncidentGaps then 2 else 0 := by
    by_cases hMarked : edge ∈ R.coreIncidentGaps
    · rw [if_pos hMarked]
      have hLe : (count edge).card ≤ edge.toFinset.card := by
        apply card_le_card_of_injOn Subtype.val
        · intro v hv
          exact Sym2.mem_toFinset.mpr (mem_filter.mp hv).2.1
        · exact Subtype.val_injective.injOn
      exact hLe.trans (by rw [Sym2.card_toFinset]; split_ifs <;> decide)
    · rw [if_neg hMarked]
      apply Nat.le_of_eq
      apply card_eq_zero.mpr
      apply eq_empty_of_forall_notMem
      intro v hv
      exact hMarked (mem_filter.mpr ⟨he,v,(mem_filter.mp hv).2.1⟩)
  have hGapMass : (∑ v : C,J.degree v.val) ≤ 2*R.coreIncidentGaps.card := by
    rw [hAcross]
    calc
      _ ≤ ∑ edge ∈ R.gaps,if edge ∈ R.coreIncidentGaps then 2 else 0 := sum_le_sum hRow
      _ = _ := by
        have hSub : R.coreIncidentGaps ⊆ R.gaps := filter_subset _ _
        rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr hSub]
        simp [Nat.mul_comm]
  have hOmissions : (∑ v : C,if v ∈ omitted then (2:ℕ) else 0) = 2*omitted.card := by
    rw [←sum_filter,filter_mem_eq_inter,univ_inter]
    simp [Nat.mul_comm]
  rw [sum_subtype Uᶜ (fun _ => Iff.rfl) (R.degreeCredit omitted)]
  change (∑ v : C,R.degreeCredit omitted v.val) ≤ _
  calc
    _ ≤ ∑ v : C,((if v ∈ omitted then (2:ℕ) else 0)+J.degree v.val) := by
      apply sum_le_sum
      intro v _
      by_cases hv : v ∈ omitted
      · rw [R.degree_credit_eq_two_at_omitted_core omitted v hv,if_pos hv]
        exact Nat.le_add_right _ _
      · rw [R.degree_credit_eq_gaps_at_retained_core omitted v hv,if_neg hv,zero_add]
    _ ≤ 2*(omitted.card+R.coreIncidentGaps.card) := by
      rw [sum_add_distrib,hOmissions]
      omega

/-- One isolated ordinary vertex or one marked pair with an ordinary
endpoint is enough room for the two-degree deficit bound. -/
theorem core_missing_degree_le_two_of_credits (R : TrimmingReplacementWords G U I)
    (omitted : Finset ↥(Uᶜ : Finset V)) (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (hMass : omitted.card+R.coreIncidentGaps.card ≤ 1)
    (hDebit : ∀ v,Q.degree v+R.degreeCredit omitted v = 2) :
    (∑ v ∈ Uᶜ,(2-Q.degree v)) ≤ 2 := by
  have hSum := R.degree_credit_mass_le_omissions_and_incident_pairs omitted
  calc
    _ = ∑ v ∈ Uᶜ,R.degreeCredit omitted v := by
      apply sum_congr rfl
      intro v _
      have h := hDebit v
      omega
    _ ≤ 2 := by omega

theorem degree_credit_eq_zero_on_core_of_no_core_gaps (R : TrimmingReplacementWords G U I)
    (hGaps : R.coreIncidentGaps = ∅) {v : V} (hv : v ∉ U) : R.degreeCredit ∅ v = 0 := by
  have hMass := R.degree_credit_mass_le_omissions_and_incident_pairs ∅
  simp only [hGaps,card_empty,add_zero,mul_zero] at hMass
  exact Nat.eq_zero_of_le_zero ((single_le_sum (fun _ _ => Nat.zero_le _) (mem_compl.mpr hv)).trans hMass)

end OverfullWork.CMSTrimmingRound.TrimmingReplacementWords
