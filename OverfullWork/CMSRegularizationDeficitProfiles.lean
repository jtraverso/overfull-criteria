module

public import OverfullWork.CMSRegularizationDenseProfiles

@[expose] public section


/-! The deficit-budget alternative of CMS Claim 4.3, when only the
first vertex can carry multiple edges in the base graph. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph OrderedCanonicalTransport
open scoped Classical

variable {m d : ℕ} {D : MultiGraph (Fin (m+1) × Bool)}

theorem ordered_rank_mono_of_pairs
    (hPair : ∀ i : Fin (m+1), D.degree (i,false) ≤ D.degree (i,true))
    (hOrder : ∀ i j : Fin (m+1), i.val < j.val → D.degree (i,true) ≤ D.degree (j,false))
    (u v : Fin (m+1) × Bool) (hRank : pairedIndex (m+1) u ≤ pairedIndex (m+1) v) :
    D.degree u ≤ D.degree v := by
  obtain ⟨i,b⟩ := u
  obtain ⟨j,c⟩ := v
  change (pairedIndex (m+1) (i,b)).val ≤ (pairedIndex (m+1) (j,c)).val at hRank
  have hIndex : i.val ≤ j.val := by
    cases b <;> cases c <;>
      simp [pairedIndex] at hRank <;> omega
  by_cases hij : i.val < j.val
  · have hu : D.degree (i,b) ≤ D.degree (i,true) := by cases b; exact hPair i; exact le_rfl
    have hv : D.degree (j,false) ≤ D.degree (j,c) := by cases c; exact le_rfl; exact hPair j
    exact hu.trans ((hOrder i j hij).trans hv)
  · have he : i = j := Fin.ext (by omega)
    subst j
    cases b <;> cases c
    · exact le_rfl
    · exact hPair i
    · simp [pairedIndex] at hRank
    · exact le_rfl

/-- Outside the first row, all losses are paid by the ordinary
deficit budget and the first bundle. No simple-degree hypothesis
at the second vertex is needed for this local conclusion. -/
theorem Completion.local_profiles_of_star_deficits (C : Completion D d) (E Y : ℕ)
    (hD : ∀ v, D.degree v ≤ d)
    (hPair : ∀ i : Fin (m+1), D.degree (i,false) ≤ D.degree (i,true))
    (hOrder : ∀ i j : Fin (m+1), i.val < j.val → D.degree (i,true) ≤ D.degree (j,false))
    (hStar : D.IsStarAt (0,false))
    (hBudget : (∑ v ∈ univ.erase (0,false), (d-D.degree v))+D.degree (0,false) ≤ d+E) :
    let M := (D.addCopies C.L).addCopies C.N
    (∀ v, v ≠ (0,false) → d ≤ M.supportGraph.degree v+M.mult s((0,false),v)+E) ∧
    ∀ v, v ≠ (0,false) → D.mult s((0,false),v) ≤ Y →
      let k := (pairedIndex (m+1) v).val
      (((k-1:ℕ):ℝ)/(k:ℝ))*(d:ℝ)-((E+Y:ℕ):ℝ) ≤ D.supportGraph.degree v := by
  intro M
  let A := C.L.addCopies C.N
  have hEq : D.addCopies A = M := by
    apply MultiGraph.ext_mult
    intro e
    change D.mult e+(C.L.mult e+C.N.mult e) = D.mult e+C.L.mult e+C.N.mult e
    omega
  have hReg : (D.addCopies A).IsRegularOfDegree d := hEq ▸ C.regular
  have hAway := CompletionOffCentreBudget.outside_internal_le D A d E (0,false) hReg hBudget
  constructor
  · intro v hv
    have hRow := CompletionOffCentreBudget.outside_row_le A E (0,false) v hv hAway
    have hLocal := CompletionOffCentreBudget.degree_le_support_bundle_add D A (0,false) v hv hStar E hRow
    rwa [hReg v,hEq] at hLocal
  · intro v hv hY
    have hDef : (∑ u ∈ univ.erase (0,false), (d-D.degree u)) ≤ d+E := by omega
    have hZero : pairedIndex (m+1) (0,false) = 0 := by
      apply Fin.ext
      simp [pairedIndex]
    exact ranked_support_of_star_budget D d (2*m+1) E Y (pairedIndex (m+1))
      (0,false) hZero (ordered_rank_mono_of_pairs hPair hOrder) hD hStar hDef v hv hY

end OverfullWork.CanonicalRegularization
