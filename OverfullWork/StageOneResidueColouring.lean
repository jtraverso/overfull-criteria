module

public import OverfullWork.DistinctCopyColouring
public import OverfullWork.UniformCaseTwoSeedCompletion

@[expose] public section


/-! # Actual balanced selection and distinct colors for CMS Stage I

The right selection is exactly the residue incident with the protected
vertices. Select the same number of left copies and color both with
one copy per color. The remaining side edge counts stay equal.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

structure StageOneResidueColouring (M : MultiGraph V) (A E : Finset V) where
  left : MultiGraph V
  left_le : ∀ e, left.mult e ≤ (M.restrict A).mult e
  count : left.edgeCount=((M.restrict Aᶜ).incidentOn E).edgeCount
  leftColouring : left.EdgeColoring ((M.restrict Aᶜ).incidentOn E).edgeCount
  rightColouring : ((M.restrict Aᶜ).incidentOn E).EdgeColoring ((M.restrict Aᶜ).incidentOn E).edgeCount
  left_mass : ∀ i, leftColouring.colourMass i=1
  right_mass : ∀ i, rightColouring.colourMass i=1
  disjoint_rows : ∀ v, left.degree v=0 ∨ ((M.restrict Aᶜ).incidentOn E).degree v=0
  balance : ((M.restrict A).subtractCopies left).edgeCount=
    ((M.restrict Aᶜ).subtractCopies ((M.restrict Aᶜ).incidentOn E)).edgeCount
  cleared : ∀ v ∈ E, ((M.restrict Aᶜ).subtractCopies ((M.restrict Aᶜ).incidentOn E)).degree v=0

theorem exists_stage_one_residue_colouring (M : MultiGraph V) (A E : Finset V)
    (hBalance : (M.restrict A).edgeCount=(M.restrict Aᶜ).edgeCount) :
    Nonempty (StageOneResidueColouring M A E) := by
  obtain ⟨J,hJ,hCount,hRemaining,hClear⟩ := exists_balanced_stage_one_selection (M.restrict A) (M.restrict Aᶜ) E hBalance
  have hCL : ∃ C : J.EdgeColoring ((M.restrict Aᶜ).incidentOn E).edgeCount, ∀ i, C.colourMass i=1 := by
    rw [←hCount]
    exact exists_distinct_copy_colouring J
  obtain ⟨CL,hCL⟩ := hCL
  obtain ⟨CR,hCR⟩ := exists_distinct_copy_colouring ((M.restrict Aᶜ).incidentOn E)
  refine ⟨{
    left := J, left_le := hJ, count := hCount, leftColouring := CL, rightColouring := CR,
    left_mass := hCL, right_mass := hCR, balance := hRemaining, cleared := hClear,
    disjoint_rows := ?_
  }⟩
  intro v
  have hLeR := (M.restrict Aᶜ).degree_le_of_mult_le ((M.restrict Aᶜ).incidentOn E)
    ((M.restrict Aᶜ).incidentOn_le E) v
  have hLeL := (M.restrict A).degree_le_of_mult_le J hJ v
  rcases M.restrict_vertex_disjoint A v with hl|hr
  · left;omega
  · right;omega

namespace PartialColouring.GoodRouteRun
variable {M : MultiGraph V} {k : ℕ} {A E : Finset V} {h ell : ℕ}
variable {P Q : M.PartialColouring k} {n t : ℕ}

theorem exists_actual_stage_one_residue_colouring (run : GoodRouteRun A E h ell P Q n t)
    (D : ℕ) (hRegular : M.IsRegularOfDegree D) (hParts : A.card=Aᶜ.card)
    (hFactors : ∀ i v, (Q.colouring.colourGraph i).degree v=1) :
    ∃ split : StageOneResidueColouring Q.available A E,
      split.left.edgeCount ≤ (P.available.internalPart A).edgeCount := by
  have hQreg : Q.graph.IsRegularOfDegree k := Q.regular_of_factorization (fun v i => hFactors i v)
  have hRemaining : Q.available.IsRegularOfDegree (D-k) := M.regular_subtract Q.graph Q.le hRegular hQreg
  have hBalance := Q.available.internal_edge_counts_eq_of_regular A (D-k) hRemaining hParts
  obtain ⟨split⟩ := exists_stage_one_residue_colouring Q.available A E hBalance
  exact ⟨split,by rw [split.count];exact run.protected_right_incident_bound⟩

end PartialColouring.GoodRouteRun
end SimpleGraph.MultiGraph
