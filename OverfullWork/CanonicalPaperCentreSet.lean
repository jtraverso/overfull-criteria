module

public import OverfullWork.PaperCentreNeighbourhood
public import OverfullWork.CanonicalEndpointBootstrap

@[expose] public section


/-! # Canonical full-neighbourhood protection with its actual scalar budget

Use the CMS small/large simple-degree split, with a fixed explicit
cutoff paid before the graph. In the small branch every simple centre
neighbour belongs to the enlarged protected set.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b : Fin (p.pairIndex+1) × Bool}

noncomputable def Candidate.paperCentreSet (p : Candidate c) (P : ℕ) :
    Finset (Fin (p.pairIndex+1) × Bool) :=
  PaperCentreNeighbourhood.protectedNeighbours p.completed.supportGraph p.centre
    ((p.pairIndex+1)/(64*(2^30*P^3)))

theorem Candidate.paperCentreSet_card (p : Candidate c) (P : ℕ) (hP : 8 ≤ P) :
    (p.paperCentreSet P).card ≤ (p.pairIndex+1)/(32*(2^30*P^3)) := by
  have hPos : 0 < 32*(2^30*P^3) := by
    have hp : 0 < P := by omega
    positivity
  exact (PaperCentreNeighbourhood.card_le_cut p.completed.supportGraph p.centre _).trans
    (Nat.div_le_div_left (by omega : 32*(2^30*P^3) ≤ 64*(2^30*P^3)) hPos)

noncomputable def Candidate.CaseTwoPartition.paperCompletionExceptions
    (s : p.CaseTwoPartition P T η b) : Finset (Fin (p.pairIndex+1) × Bool) :=
  s.completionExceptions ∪ p.paperCentreSet P

theorem Candidate.CaseTwoPartition.paper_contains_centre_neighbour
    (s : p.CaseTwoPartition P T η b)
    (hSmall : p.completed.supportGraph.degree p.centre < (p.pairIndex+1)/(64*(2^30*P^3)))
    (v : Fin (p.pairIndex+1) × Bool) (hAdj : p.completed.supportGraph.Adj p.centre v) :
    v ∈ s.paperCompletionExceptions := by
  apply mem_union_right
  exact PaperCentreNeighbourhood.contains_neighbour_of_small p.completed.supportGraph p.centre _ hSmall v hAdj

end OverfullWork.NormalizedCanonicalCandidate
