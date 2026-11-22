module

public import OverfullWork.FirstAnchorExceptionChoice

@[expose] public section


namespace OverfullWork.FirstAnchorScale
set_option maxHeartbeats 24000000

theorem threshold_at_source_cutoff (T m : ℕ) (hm : 0 < m) (δ τ : ℝ)
    (hτ : 0 < τ) (hSmall : δ ≤ τ/10000) (hT : 4 ≤ δ*(T:ℝ)) :
    ((m/T:ℕ):ℝ) < τ*(m:ℝ)/32 := by
  have hRateT : 40000 ≤ τ*(T:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hSmall (show (0:ℝ) ≤ T from Nat.cast_nonneg _)
    linarith
  have hFloor : (T:ℝ)*((m/T:ℕ):ℝ) ≤ m := by exact_mod_cast Nat.mul_div_le m T
  have hPay := mul_le_mul_of_nonneg_left hFloor hτ.le
  have hGain := mul_le_mul_of_nonneg_right hRateT (show (0:ℝ) ≤ (m/T:ℕ) from Nat.cast_nonneg _)
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  by_cases hf : m/T=0
  · rw [hf,Nat.cast_zero]
    positivity
  · have hfR : (0:ℝ) < (m/T:ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hf
    nlinarith only [hPay,hGain,hfR]

end OverfullWork.FirstAnchorScale
