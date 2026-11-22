module

public import OverfullWork.CanonicalHeavyPairPacking
public import OverfullWork.CanonicalImageDegreeRange

@[expose] public section


/-! # Pay the heavy-pair packing reserve from the original source scale

The dense reserve is not left as a new graph-theoretic premise: it
follows from the source density, sparse certificate budgets, and the
displayed heavy-pair cutoff. This module still stops before turning the
paths into coloured cycles and factorizing the residual multigraph.
-/
namespace OverfullWork.HeavyPairBoundary
set_option maxHeartbeats 5000000

theorem scaled_density_of_above_half (ε : ℝ) (Q n d : ℕ)
    (hQε : 1 ≤ ε * (Q : ℝ))
    (hdense : ((1 : ℝ) / 2 + ε) * (n : ℝ) ≤ (d : ℝ)) :
    (Q + 2) * n ≤ 2 * Q * d := by
  have h₁ := mul_le_mul_of_nonneg_left hdense (show 0 ≤ 2 * (Q : ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hQε (Nat.cast_nonneg n)
  exact_mod_cast (show ((Q : ℝ) + 2) * (n : ℝ) ≤ 2 * (Q : ℝ) * (d : ℝ) by
    nlinarith only [h₁,h₂])

theorem source_packing_slack (Q n l d B q : ℕ)
    (hQ : 2 ≤ Q) (hn : 64 * Q ≤ n) (hl : l ≤ n + 1)
    (hB : B ≤ 6 * (n / (4096 * Q^2)) + 6)
    (hq : q ≤ n / (64 * Q)) (hdense : (Q + 2) * n ≤ 2 * Q * d) :
    l + 6 * q + 2 * B + 10 ≤ 2 * d := by
  let k := n / (4096 * Q^2)
  have hcoef : 64 * Q ≤ 4096 * Q^2 := by nlinarith only [hQ]
  have hk : 64 * Q * k ≤ n :=
    (Nat.mul_le_mul_right k hcoef).trans (Nat.mul_div_le n (4096 * Q^2))
  have hqmul : 64 * Q * q ≤ n :=
    (Nat.mul_le_mul_left (64 * Q) hq).trans (Nat.mul_div_le n (64 * Q))
  change B ≤ 6 * k + 6 at hB
  have hBm := Nat.mul_le_mul_left Q hB
  have hreserve : Q * (6 * q + 2 * B + 11) ≤ 2 * n := by
    nlinarith only [hk, hqmul, hn, hBm]
  have hlmul := Nat.mul_le_mul_left Q hl
  nlinarith only [hreserve, hlmul, hdense, hQ]

end OverfullWork.HeavyPairBoundary

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun HeavyPairBoundary IndependentSetIdentification
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 6000000

theorem Candidate.heavy_pair_packing_at_source_scale (p : Candidate c)
    (Q : ℕ) (hQ : 2 ≤ Q) (hn : 64 * Q ≤ Fintype.card V)
    (hdense : (Q + 2) * Fintype.card V ≤ 2 * Q * G.maxDegree)
    (hB : B ≤ 6 * (Fintype.card V / (4096 * Q^2)) + 6)
    (hK : K ≤ Fintype.card V / (4096 * Q^2) + 1)
    (b : Fin (p.pairIndex+1) × Bool) (hab : p.centre ≠ b)
    (hNo : ¬ p.completed.HasOverfullSubset G.maxDegree)
    (hHeavy : G.maxDegree - p.completed.mult s(p.centre,b) ≤ Fintype.card V / (64 * Q)) :
    ∃ e : (Σ w : outside p.centre b, Fin (p.completed.mult s(p.centre,w.val))) ≃
        (Σ w : outside p.centre b, Fin (p.completed.mult s(b,w.val))),
      ∃ f : Fin (G.maxDegree - p.completed.mult s(p.centre,b)) ≃
        (Σ w : outside p.centre b, Fin (p.completed.mult s(p.centre,w.val))),
      Nonempty (DenseBatchPathPacking.Packing
        (p.completed.supportGraph.induce (outside p.centre b : Set (Fin (p.pairIndex+1) × Bool)))
        (G.maxDegree - p.completed.mult s(p.centre,b)) 1
        (fun j _ => (f j).1) (fun j _ => (e (f j)).1)) := by
  have hCoords := Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    card_vertices, compl_compl] at hCoords
  have hCore := card_le_univ c.set
  have hl : 2 * (p.pairIndex+1) ≤ Fintype.card V + 1 := by omega
  have hWeak : Fintype.card V ≤ 2 * G.maxDegree := by
    nlinarith only [hdense, hQ]
  have hL := p.maxDegree_lt_image_order_at_source_scale Q hQ hn hB hK
  apply p.heavy_pair_path_packing b hab hNo (by omega)
  exact source_packing_slack Q (Fintype.card V) _ G.maxDegree B _
    hQ hn hl hB hHeavy hdense

end OverfullWork.NormalizedCanonicalCandidate
