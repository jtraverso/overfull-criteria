module

public import OverfullWork.CMSCaseTwoSeedCompletion
public import OverfullWork.ProtectedCanonicalResiduePalette

@[expose] public section


/-! Construct the two stages of the internal-residue palette in
CMS Theorem 4.2, Case 2, Step 4, on the general host. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph MultiGraph.PartialColouring
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {a b w : V}
variable {d m L r t k : ℕ} {η ξ B : ℝ}
variable {s : CaseTwoPartition M a b d m L r t η} {R Q : M.PartialColouring k}

set_option maxHeartbeats 1500000 in
theorem CaseTwoPartition.InitialRouteBudget.exists_two_stage_residue_palette
    (budget : s.InitialRouteBudget R w ξ B) (E : Finset V) {h ell n u : ℕ}
    (hReg : M.IsRegularOfDegree d) (run : GoodRouteRun s.part E h ell R Q n u)
    (hFactors : ∀ i v, (Q.colouring.colourGraph i).degree v = 1)
    (hCap : ∀ v, (Q.available.internalPart s.part).degree v ≤ h)
    (hCentre : (Q.available.internalPart s.part).degree a = 0) :
    ∃ q : ℕ, (q:ℝ) < 5*ξ ∧ ∃ C : (Q.available.internalPart s.part).EdgeColoring (q+3*h),
      (∀ i, (C.colourGraph i).edgesWithin s.part = (C.colourGraph i).edgesWithin s.partᶜ) ∧
      (∀ i : Fin q, (C.colourGraph (Fin.castAdd (3*h) i)).edgesWithin s.part = 1) ∧
      (∀ i : Fin (3*h), (3*h)*(C.colourGraph (Fin.natAdd q i)).edgesWithin s.part ≤
        (Q.available.internalPart s.part).edgeCount+3*h) ∧
      (∀ v ∈ E, v ∈ s.partᶜ → ∀ i : Fin (3*h), (C.colourGraph (Fin.natAdd q i)).degree v = 0) ∧
      (∀ i, (C.colourGraph i).degree a=0) ∧
      (∀ i v, ((Q.attach_internal_residue s.part C).colouring.colourGraph (Fin.castAdd (q+3*h) i)).degree v=1) ∧
      (Q.attach_internal_residue s.part C).CoversInternal s.part := by
  obtain ⟨first,hCount⟩ := run.exists_actual_stage_one_residue_colouring d hReg
    (s.card_part.trans s.card_compl.symm) hFactors
  obtain ⟨second⟩ := first.exists_stage_two_colouring h hCap
  obtain ⟨C,hBalance,hStageOne,hStageTwoBound,hClear⟩ := second.exists_combined_palette
  let q := ((Q.available.restrict s.partᶜ).incidentOn E).edgeCount
  have hCountR : (q:ℝ) ≤ (R.available.internalPart s.part).edgeCount := by
    rw [first.count] at hCount
    exact_mod_cast hCount
  have hLeftCount : ((Q.available.restrict s.part).subtractCopies first.left).edgeCount ≤
      (Q.available.internalPart s.part).edgeCount := by
    apply sum_le_sum
    intro e _
    exact (Nat.sub_le _ _).trans (MultiGraph.restrict_le_internal_part Q.available s.part e).1
  refine ⟨q,hCountR.trans_lt budget.residue,C,hBalance,hStageOne,?_,hClear,?_,?_,?_⟩
  · intro i
    exact (hStageTwoBound i).trans (Nat.add_le_add_right hLeftCount (3*h))
  · intro i
    have hh := C.incidence_le_degree a i
    rw [hCentre] at hh
    omega
  · intro i v
    rw [Q.attach_internal_residue_old_colour]
    exact hFactors i v
  · exact Q.attach_internal_residue_covers s.part C

end OverfullWork.CMSBalancedCut
