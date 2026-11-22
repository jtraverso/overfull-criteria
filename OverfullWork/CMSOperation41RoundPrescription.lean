module

public import OverfullWork.CMSOperation41CoreCreditMass
public import OverfullWork.CMSOperation41CutSupport

@[expose] public section


/-! The data verified before a round is passed to the simultaneous
packing. The degree checks use the record after preprocessing. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

structure TrimmingRoundPrescription (G : SimpleGraph V) (U : Finset V)
    (degree : V → ℕ) (d : ℕ) where
  size : ℕ
  words : TrimmingReplacementWords G U (Fin size)
  omitted : Finset ↥(Uᶜ : Finset V)
  endpoints_retained : ∀ i,words.endpoint i ∉ omitted
  core_credit_bound : omitted.card+words.coreIncidentGaps.card ≤ 1
  empty_body_is_gap : ∀ i,words.body i = [] →
    s((words.endpoint (i,false)).val,(words.endpoint (i,true)).val) ∈ words.gaps
  minimum_length : 3 ≤ Uᶜ.card-omitted.card+∑ i,(words.body i).length
  even_or_gap : Even (Uᶜ.card-omitted.card+∑ i,(words.body i).length) ∨ words.gaps.Nonempty
  degree_cap : ∀ v,degree v+words.degreeCredit omitted v ≤ d

/-- Step 3 can be verified on the virtual graph before choosing any
ordinary packing edges. The same credit accounts for exceptional
losses exactly and bounds the remaining ordinary loss. -/
theorem TrimmingRoundPrescription.next_degree_record
    (S C : SimpleGraph V) (U : Finset V) (degree : V → ℕ) (d : ℕ)
    (R : TrimmingRoundPrescription (sdiff S C) U degree d)
    (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (j : ℕ)
    (hC : C ≤ S) (hP : P j = R.words.prescribedGraph)
    (hCredit : credit j = R.words.degreeCredit R.omitted)
    (hDegree : ∀ v,auxiliaryPhysicalDegree S U P credit j v-C.degree v = degree v)
    (v : V) :
    let next := sdiff (sdiff S C) (P j)
    let record := auxiliaryPhysicalDegree next U P credit (j+1) v
    record = degree v-(2-R.words.degreeCredit R.omitted v) ∧ record ≤ d-2 := by
  intro next record
  have hPLe : P j ≤ sdiff S C := hP.symm ▸ R.words.prescribedGraph_le
  have hDebit (w : V) (hw : w ∉ U) : (P j).degree w ≤ 2-credit j w := by
    rw [hP,hCredit]
    exact R.words.prescribed_degree_le_core_debit R.omitted R.endpoints_retained hw
  have hLoss : (if v ∈ U then (P j).degree v else 2-credit j v) =
      2-R.words.degreeCredit R.omitted v := by
    rw [hP,hCredit]
    by_cases hv : v ∈ U
    · rw [if_pos hv]
      have h := R.words.prescribed_degree_add_credit_on_exceptional R.omitted hv
      omega
    · rw [if_neg hv]
  have hNext := auxiliary_physical_degree_after_round S C U P credit j hC hPLe hDebit v
  change record = _ at hNext
  rw [hLoss,←Nat.sub_sub,hDegree] at hNext
  have hCap := R.degree_cap v
  exact ⟨hNext,by omega⟩

/-- The ordinary degree reserve makes the virtual debit exact before
packing, including the cleanup cost of this round. -/
theorem TrimmingRoundPrescription.next_degree_record_add_debits
    (S C : SimpleGraph V) (U : Finset V) (degree : V → ℕ) (d : ℕ)
    (R : TrimmingRoundPrescription (sdiff S C) U degree d)
    (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (j : ℕ)
    (hC : C ≤ S) (hP : P j = R.words.prescribedGraph)
    (hCredit : credit j = R.words.degreeCredit R.omitted)
    (hDegree : ∀ v,auxiliaryPhysicalDegree S U P credit j v-C.degree v = degree v)
    (hCleanupRoom : ∀ v,C.degree v ≤ auxiliaryPhysicalDegree S U P credit j v)
    (hCoreRoom : ∀ v,v ∉ U → 2 ≤ degree v) (v : V) :
    let next := sdiff (sdiff S C) (P j)
    auxiliaryPhysicalDegree next U P credit (j+1) v+C.degree v+(2-credit j v) =
      auxiliaryPhysicalDegree S U P credit j v := by
  intro next
  have hRoom : 2-R.words.degreeCredit R.omitted v ≤ degree v := by
    by_cases hv : v ∈ U
    · have hBalance := R.words.prescribed_degree_add_credit_on_exceptional R.omitted hv
      have hBound : R.words.prescribedGraph.degree v ≤ (sdiff S C).degree v :=
        degree_le_of_le R.words.prescribedGraph_le
      have hExact : degree v = (sdiff S C).degree v := by
        have h := hDegree v
        simp only [auxiliaryPhysicalDegree,if_pos hv] at h
        have hC' : (sdiff S C).degree v+C.degree v = S.degree v := by
          simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
            MaximumMatching.degree_sdiff_add_of_le S C hC v
        omega
      omega
    · have h := hCoreRoom v hv
      omega
  have hNext := (R.next_degree_record S C U degree d P credit j hC hP hCredit hDegree v).1
  change auxiliaryPhysicalDegree next U P credit (j+1) v = _ at hNext
  rw [hNext,show credit j v = R.words.degreeCredit R.omitted v by rw [hCredit]]
  have h := hDegree v
  have hClean := hCleanupRoom v
  omega

end OverfullWork.CMSTrimmingRound
