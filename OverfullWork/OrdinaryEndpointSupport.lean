module

public import OverfullWork.SeedErrorRateScales
public import OverfullWork.CanonicalRankProfile

@[expose] public section


/-! # Reuse the published rank profile at ordinary missing endpoints

The first two canonical positions are the only exceptions. Rank at
least two gives half-Delta support degree, paying the original B+Y loss.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 20000000

theorem Candidate.rank_ge_two_of_not_anchors (p : Candidate c)
    (v : Fin (p.pairIndex+1) × Bool) (hv₀ : v ≠ (0,false)) (hv₁ : v ≠ (0,true)) : 2 ≤ p.rank v := by
  obtain ⟨j,b⟩ := v
  have hj : j ≠ 0 := by
    intro he
    subst j
    cases b
    · exact hv₀ rfl
    · exact hv₁ rfl
  have hjv : 1 ≤ j.val := by
    have hn : j.val ≠ 0 := fun he => hj (Fin.ext he)
    omega
  cases b <;> simp [Candidate.rank,OrderedCanonicalTransport.pairedIndex] <;> omega

theorem Candidate.ordinary_support_half_bound (p : Candidate c) (hCentre : p.centre=(0,false))
    (v : Fin (p.pairIndex+1) × Bool) (hv₀ : v ≠ (0,false)) (hv₁ : v ≠ (0,true)) :
    (G.maxDegree:ℝ)/2-((B+c.setᶜ.card:ℕ):ℝ) ≤ (p.completed.supportGraph.degree v:ℝ) := by
  have hRank := p.rank_ge_two_of_not_anchors v hv₀ hv₁
  have hProfile := p.completed_rank_profile_real hCentre v (by omega)
  have hPos : (0:ℝ) < p.rank v := by exact_mod_cast (show 0 < p.rank v by omega)
  have hRatio : (1:ℝ)/2 ≤ ((p.rank v-1:ℕ):ℝ)/(p.rank v:ℝ) := by
    apply (le_div_iff₀ hPos).mpr
    have hSub : ((p.rank v-1:ℕ):ℝ)=(p.rank v:ℝ)-1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    have hRankR : (2:ℝ) ≤ p.rank v := by exact_mod_cast hRank
    linarith
  have hMul := mul_le_mul_of_nonneg_right hRatio (Nat.cast_nonneg G.maxDegree : (0:ℝ) ≤ G.maxDegree)
  linarith

end OverfullWork.NormalizedCanonicalCandidate
