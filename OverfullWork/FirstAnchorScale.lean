module

public import OverfullWork.ResidualCentreAnchorSet

@[expose] public section


/-! Choose the source rate below both the nonheavy gap and the protection scale. -/
namespace OverfullWork.FirstAnchorScale
open Finset
open scoped Classical
set_option maxHeartbeats 24000000

noncomputable def rate (P : ℕ) (ρ : ℝ) : ℝ := min ρ (1/(3200*((2^30*P^3:ℕ):ℝ)))

theorem rate_pos (P : ℕ) (hP : 8 ≤ P) (ρ : ℝ) (hρ : 0 < ρ) : 0 < rate P ρ := by
  have hp : 0 < P := by omega
  dsimp only [rate]
  positivity

theorem rate_le_gap (P : ℕ) (ρ : ℝ) : rate P ρ ≤ ρ := min_le_left _ _

theorem cut_large (P m z : ℕ) (hP : 8 ≤ P) (ρ : ℝ)
    (hCut : m/(32*(2^30*P^3)) ≤ z) :
    100*rate P ρ*(m:ℝ) < (z:ℝ)+1 := by
  let d := 2^30*P^3
  have hd : 0 < d := by
    dsimp only [d]
    have hp : 0 < P := by omega
    positivity
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hRate : rate P ρ ≤ 1/(3200*(d:ℝ)) := min_le_right _ _
  have hRateMul : rate P ρ*(3200*(d:ℝ)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hRate
  have hDiv : m < (z+1)*(32*d) := by
    have hh := Nat.div_add_mod m (32*d)
    have hr := Nat.mod_lt m (show 0 < 32*d by positivity)
    change m/(32*d) ≤ z at hCut
    nlinarith
  have hDivR : (m:ℝ) < ((z:ℝ)+1)*(32*(d:ℝ)) := by exact_mod_cast hDiv
  have hMul := mul_le_mul_of_nonneg_right hRateMul (show (0:ℝ) ≤ m from Nat.cast_nonneg _)
  have hCompare : (100*rate P ρ*(m:ℝ))* (32*(d:ℝ)) < ((z:ℝ)+1)*(32*(d:ℝ)) := by nlinarith
  exact (mul_lt_mul_iff_left₀ (show (0:ℝ) < 32*(d:ℝ) by positivity)).mp hCompare

end OverfullWork.FirstAnchorScale
