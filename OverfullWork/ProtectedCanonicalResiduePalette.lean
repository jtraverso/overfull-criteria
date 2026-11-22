module

public import OverfullWork.AttachResiduePalette
public import OverfullWork.CanonicalFreeAnchorBundles
public import OverfullWork.PrescribedResidueExtension

@[expose] public section


/-! # Construct the actual CMS Step 4 internal-residue palette

Starting from the completed canonical good run, select and color Stage I,
align Stage II and attach the fresh palette. The count of Stage I colors
is paid by the original initial residue, not by a new current hypothesis.
This is the internal coloring, before extending all fresh classes.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 24000000

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.exists_two_stage_residue_palette_for_set
    {R Q : p.completed.PartialColouring r.seedPalette} {h ell n t : ℕ}
    (budget : r.InitialRouteBudget R) (E : Finset (Fin (p.pairIndex+1) × Bool))
    (run : MultiGraph.PartialColouring.GoodRouteRun s.part E h ell R Q n t)
    (hFactors : ∀ i v, (Q.colouring.colourGraph i).degree v=1)
    (hCap : ∀ v, (Q.available.internalPart s.part).degree v ≤ h)
    (hCentre : (Q.available.internalPart s.part).degree p.centre=0) :
    ∃ q : ℕ, (q:ℝ) < 5*r.seedError ∧
      ∃ C : (Q.available.internalPart s.part).EdgeColoring (q+3*h),
        (∀ i, (C.colourGraph i).edgesWithin s.part=(C.colourGraph i).edgesWithin s.partᶜ) ∧
        (∀ i : Fin q, (C.colourGraph (Fin.castAdd (3*h) i)).edgesWithin s.part=1) ∧
        (∀ i : Fin (3*h), (3*h)*(C.colourGraph (Fin.natAdd q i)).edgesWithin s.part ≤
          (Q.available.internalPart s.part).edgeCount+3*h) ∧
        (∀ v ∈ E, v ∈ s.partᶜ → ∀ i : Fin (3*h),
          (C.colourGraph (Fin.natAdd q i)).degree v=0) ∧
        (∀ i, (C.colourGraph i).degree p.centre=0) ∧
        (∀ i v, ((Q.attach_internal_residue s.part C).colouring.colourGraph (Fin.castAdd (q+3*h) i)).degree v=1) ∧
        (Q.attach_internal_residue s.part C).CoversInternal s.part := by
  obtain ⟨first,hCount⟩ := run.exists_actual_stage_one_residue_colouring G.maxDegree p.completion.regular
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
  refine ⟨q,hCountR.trans_lt budget.residue_size,C,hBalance,hStageOne,?_,hClear,?_,?_,?_⟩
  · intro i
    exact (hStageTwoBound i).trans (Nat.add_le_add_right hLeftCount (3*h))
  · intro i
    have hh := C.incidence_le_degree p.centre i
    rw [hCentre] at hh
    omega
  · intro i v
    rw [Q.attach_internal_residue_old_colour]
    exact hFactors i v
  · exact Q.attach_internal_residue_covers s.part C

end OverfullWork.NormalizedCanonicalCandidate
