module

public import OverfullWork.CanonicalHeavyPairColouring
public import OverfullWork.HeavyPairFactorizationScales

@[expose] public section


/-! # Actual Delta-colouring in the uniform heavy-pair small-centre branch

All layers, the ordinary residual factorization, their colourings, and
all numeric reserves are constructed. The final theorem chooses its
source scale before the graph. The nonheavy colouring case and the
other terminal branches of G2 are not asserted here.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun HeavyPairBoundary IndependentSetIdentification
open Gate8J2I
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 12000000

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Uniform closure of the heavy-pair branch. No residual colourability,
factorization, or numeric order reserve is assumed after Q,N are chosen. -/
theorem above_half_heavy_factorization_of_completed_no_overfull (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∃ N : ℕ,
    ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),
      N ≤ Fintype.card W → (¬p.completed.HasOverfullSubset G.maxDegree) →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
      B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
      (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
      ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
      G.maxDegree-p.completed.mult s(p.centre,b) ≤ Fintype.card W/(64*Q) →
      Nonempty (p.completed.EdgeColoring G.maxDegree) := by
  obtain ⟨C,hC⟩ := exists_nat_gt (max (4000:ℝ) (64/ε))
  have hCReal : (4000:ℝ) ≤ C := (le_max_left _ _).trans hC.le
  have hCN : 4000 ≤ C := by exact_mod_cast hCReal
  have hCε : 64 ≤ ε*(C:ℝ) := by
    have hh : 64/ε < C := (le_max_right _ _).trans_lt hC
    have ht := (div_lt_iff₀ hε).mp hh
    nlinarith only [ht]
  let Q := max C ((10:ℕ)^24*C^6)
  have hCQ : C ≤ Q := le_max_left _ _
  have hAQ : (10:ℕ)^24*C^6 ≤ Q := le_max_right _ _
  have hQ : 2 ≤ Q := by omega
  have hQε : 1 ≤ ε*(Q:ℝ) := by
    have hcq : (C:ℝ) ≤ Q := by exact_mod_cast hCQ
    have hm := mul_le_mul_of_nonneg_left hcq hε.le
    linarith only [hm,hCε]
  refine ⟨Q,hQ,64*Q,?_⟩
  intro W _ _ G _ B K c p hn hNo hdense hB hK hMin b hab hHeavy
  exact p.heavy_pair_colourable_at_source_scale C Q hCN hQ hCQ hAQ (by omega)
    (scaled_density_of_above_half ε Q _ _ hQε hdense)
    (HeavyPairPeeling.strong_scaled_density ε C _ _ hCε hdense) hB hK b hab hNo hHeavy

end OverfullWork.NormalizedCanonicalCandidate
