module

public import OverfullWork.CanonicalResidueIteration
public import OverfullWork.CanonicalColouringPullback

@[expose] public section


/-! CMS Case 2 Step 5: the actual regular internal cover and bipartite remainder. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T ell : ℕ} {η ρ : ℝ} {b : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 32000000

theorem Candidate.CaseTwoHallCompletion.exists_factorization
    (a : p.CaseTwoHallCompletion s ell ρ) (hP : 8 ≤ P) (hρ : 0 < ρ) :
    ∃ C : p.completed.EdgeColoring G.maxDegree, C.IsFactorization := by
  obtain ⟨Q,hMono,hCover,hFactors⟩ := a.exists_completed_residue_palette hP hρ
  have hRegular : Q.graph.IsRegularOfDegree (a.middle.seedPalette+(a.fresh+3*a.cap)) := by
    intro v
    rw [←Q.colouring.sum_colour_degree v]
    simp_rw [hFactors]
    simp
  exact MultiGraph.exists_factorization_of_internal_cover p.completed Q.graph s.part G.maxDegree
    (a.middle.seedPalette+(a.fresh+3*a.cap)) a.palette_lt Q.le p.completion.regular hRegular
    ⟨Q.colouring⟩ hCover

theorem Candidate.CaseTwoHallCompletion.source_colourable
    (a : p.CaseTwoHallCompletion s ell ρ) (hP : 8 ≤ P) (hρ : 0 < ρ) : G.EdgeColorable G.maxDegree := by
  obtain ⟨C,_⟩ := a.exists_factorization hP hρ
  exact p.source_colourable_of_completed C

end OverfullWork.NormalizedCanonicalCandidate
