module

public import OverfullWork.HeavyPairPeeling
public import OverfullWork.HeavyPairSourceScales

@[expose] public section


/-! # Coloured heavy-pair peeling on the actual canonical completion

The cover, its two-colour-per-round colouring, copy capacities, and
regular residue are all constructed from the existing candidate.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun HeavyPairBoundary IndependentSetIdentification
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 6000000

theorem Candidate.heavy_pair_coloured_peeling (p : Candidate c)
    (b : Fin (p.pairIndex+1) × Bool) (hab : p.centre ≠ b)
    (hNo : ¬ p.completed.HasOverfullSubset G.maxDegree)
    (hn : 10 ≤ 2 * (p.pairIndex+1))
    (hslack : 2 * (p.pairIndex+1) +
      6 * (G.maxDegree - p.completed.mult s(p.centre,b)) + 2 * B + 10 ≤ 2 * G.maxDegree) :
    Nonempty (HeavyPairPeeling.Certificate p.completed G.maxDegree
      (G.maxDegree - p.completed.mult s(p.centre,b)) p.centre b) := by
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
  have hh := HeavyPairPeeling.exists_certificate p.orderedBase (p.completion.L.addCopies p.completion.N)
    G.maxDegree B p.centre b hab p.ordered_star hreg (by rwa [hGraph])
    p.added_off_centre_internal_le (by rw [hcard]; exact ⟨p.pairIndex+1, by omega⟩)
    (by rwa [hcard]) (by rwa [hGraph,hcard])
  rwa [hGraph] at hh

theorem Candidate.heavy_pair_peeling_at_source_scale (p : Candidate c)
    (Q : ℕ) (hQ : 2 ≤ Q) (hn : 64 * Q ≤ Fintype.card V)
    (hdense : (Q + 2) * Fintype.card V ≤ 2 * Q * G.maxDegree)
    (hB : B ≤ 6 * (Fintype.card V / (4096 * Q^2)) + 6)
    (hK : K ≤ Fintype.card V / (4096 * Q^2) + 1)
    (b : Fin (p.pairIndex+1) × Bool) (hab : p.centre ≠ b)
    (hNo : ¬ p.completed.HasOverfullSubset G.maxDegree)
    (hHeavy : G.maxDegree - p.completed.mult s(p.centre,b) ≤ Fintype.card V / (64 * Q)) :
    Nonempty (HeavyPairPeeling.Certificate p.completed G.maxDegree
      (G.maxDegree - p.completed.mult s(p.centre,b)) p.centre b) := by
  have hCoords := Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    card_vertices,compl_compl] at hCoords
  have hCore := card_le_univ c.set
  have hl : 2 * (p.pairIndex+1) ≤ Fintype.card V + 1 := by omega
  have hWeak : Fintype.card V ≤ 2 * G.maxDegree := by nlinarith only [hdense,hQ]
  have hL := p.maxDegree_lt_image_order_at_source_scale Q hQ hn hB hK
  apply p.heavy_pair_coloured_peeling b hab hNo (by omega)
  exact source_packing_slack Q (Fintype.card V) _ G.maxDegree B _
    hQ hn hl hB hHeavy hdense

end OverfullWork.NormalizedCanonicalCandidate
