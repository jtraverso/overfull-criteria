module

public import OverfullWork.HallNeighbourLoss

@[expose] public section


namespace OverfullWork.FirstAnchorScale
set_option maxHeartbeats 24000000

theorem rate_order_bounds (P m r : ℕ) (hP : 8 ≤ P) (ρ : ℝ) (hρ : 0 < ρ)
    (hRobust : (m:ℝ)/(2*((2^30*P^3:ℕ):ℝ)) ≤ r) :
    rate P ρ*(m:ℝ) ≤ (m:ℝ)/3200 ∧ 1600*(rate P ρ*(m:ℝ)) ≤ r := by
  let d := 2^30*P^3
  have hd : 0 < d := by
    have hp : 0 < P := by omega
    dsimp only [d]
    positivity
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hdOne : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hRatePos := (rate_pos P hP ρ hρ).le
  have hRate : rate P ρ ≤ 1/(3200*(d:ℝ)) := min_le_right _ _
  have hRateMul : rate P ρ*(3200*(d:ℝ)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hRate
  have hSmall : 3200*rate P ρ ≤ 1 := by nlinarith
  have hSmallM := mul_le_mul_of_nonneg_right hSmall (show (0:ℝ) ≤ m from Nat.cast_nonneg _)
  constructor
  · nlinarith only [hSmallM]
  · apply (mul_le_mul_iff_left₀ (show (0:ℝ) < 2*(d:ℝ) by positivity)).mp
    calc
      (1600*(rate P ρ*(m:ℝ)))*(2*(d:ℝ)) = (rate P ρ*(3200*(d:ℝ)))*(m:ℝ) := by ring
      _ ≤ m := by simpa using mul_le_mul_of_nonneg_right hRateMul (show (0:ℝ) ≤ m from Nat.cast_nonneg _)
      _ ≤ (r:ℝ)*(2*(d:ℝ)) := (div_le_iff₀ (by positivity)).mp hRobust

end OverfullWork.FirstAnchorScale
