module

public import OverfullWork.HeavyPairPathPacking

@[expose] public section


/-! # Apply the heavy-pair construction to the actual canonical completion

The sparse off-centre budget and star condition are discharged by the
existing candidate. Only the explicit heavy-pair dense reserve, order,
and the previously established no-overfull conclusion are inputs.
This constructs the ordinary paths, not yet the cycles or their residual
factorization.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun HeavyPairBoundary
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 6000000

theorem Candidate.heavy_pair_path_packing (p : Candidate c)
    (b : Fin (p.pairIndex+1) × Bool) (hab : p.centre ≠ b)
    (hNo : ¬ p.completed.HasOverfullSubset G.maxDegree)
    (hn : 10 ≤ 2 * (p.pairIndex+1))
    (hslack : 2 * (p.pairIndex+1) +
      6 * (G.maxDegree - p.completed.mult s(p.centre,b)) + 2 * B + 10 ≤ 2 * G.maxDegree) :
    ∃ e : (Σ w : outside p.centre b, Fin (p.completed.mult s(p.centre,w.val))) ≃
        (Σ w : outside p.centre b, Fin (p.completed.mult s(b,w.val))),
      ∃ f : Fin (G.maxDegree - p.completed.mult s(p.centre,b)) ≃
        (Σ w : outside p.centre b, Fin (p.completed.mult s(p.centre,w.val))),
      Nonempty (DenseBatchPathPacking.Packing
        (p.completed.supportGraph.induce (outside p.centre b : Set (Fin (p.pairIndex+1) × Bool)))
        (G.maxDegree - p.completed.mult s(p.centre,b)) 1
        (fun j _ => (f j).1) (fun j _ => (e (f j)).1)) := by
  have hGraph : p.orderedBase.addCopies (p.completion.L.addCopies p.completion.N) =
      p.completed := by
    apply MultiGraph.ext_mult
    intro t
    exact (Nat.add_assoc _ _ _).symm
  have hreg : (p.orderedBase.addCopies (p.completion.L.addCopies p.completion.N)).IsRegularOfDegree
      G.maxDegree := by
    rw [hGraph]
    exact p.completion.regular
  have hcard : Fintype.card (Fin (p.pairIndex+1) × Bool) = 2 * (p.pairIndex+1) := by
    simp [Nat.mul_comm]
  have hh := exists_boundary_path_packing p.orderedBase (p.completion.L.addCopies p.completion.N)
    G.maxDegree B p.centre b hab p.ordered_star hreg (by rwa [hGraph])
    p.added_off_centre_internal_le (by rwa [hcard]) (by rwa [hGraph, hcard])
  rwa [hGraph] at hh

end OverfullWork.NormalizedCanonicalCandidate
