module

public import OverfullWork.UniformFirstAnchorCompletion

@[expose] public section


/-! The uniform certificate provides actual anchors at the attached initial state. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T ell : ℕ} {η : ℝ} {b : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}

theorem Candidate.CaseTwoFirstAnchorCompletion.initial_anchors
    (a : p.CaseTwoFirstAnchorCompletion s ell) (j : Fin (a.fresh+3*a.cap)) :
    Nonempty (MultiGraph.PartialColouring.AnchorPrescription
      (a.seed.attach_internal_residue s.part a.palette)
      (Fin.natAdd a.middle.seedPalette j) s.part p.centre b) := by
  apply a.anchors _ (fun e => ?_) a.covers j
  · exact a.seed.attach_internal_residue_fresh_colour s.part a.palette j
  · change a.seed.graph.mult e ≤ a.seed.graph.mult e+(a.seed.available.internalPart s.part).mult e
    omega

theorem Candidate.CaseTwoFirstAnchorCompletion.initial_seed_factors
    (a : p.CaseTwoFirstAnchorCompletion s ell) (i : Fin a.middle.seedPalette)
    (v : Fin (p.pairIndex+1) × Bool) :
    ((a.seed.attach_internal_residue s.part a.palette).colouring.colourGraph
      (Fin.castAdd (a.fresh+3*a.cap) i)).degree v=1 := by
  rw [a.seed.attach_internal_residue_old_colour]
  exact a.factors i v

end OverfullWork.NormalizedCanonicalCandidate
