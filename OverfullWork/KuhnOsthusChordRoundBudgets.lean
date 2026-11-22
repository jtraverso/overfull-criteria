module

public import OverfullWork.KuhnOsthusChordRoundAssembly

@[expose] public section


/-! Quantitative versions of the inequalities used across the
rounds of Kühn–Osthus Lemma 9.7. -/
namespace OverfullWork.DirectedRobustExpansion

/-- With `q' = f*k`, the paper's `r*k ≤ m/f²` pays the total
deletion in every cluster. The stated lower bound on `f` supplies
the small constant used by the completion theorem. -/
theorem chord_round_count_budget (r f k m : ℕ) (ρ : ℝ)
    (hSize : r*k*f^2 ≤ m) (hF : (16:ℝ) ≤ (ρ/128)^2*(f:ℝ)) :
    ((r*(f*k):ℕ):ℝ) ≤ (ρ/128)^2*(m:ℝ)/16 := by
  have hPay : (r*(f*k))*f ≤ m := by
    simpa only [pow_two,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hSize
  have hPayR : ((r*(f*k):ℕ):ℝ)*(f:ℝ) ≤ m := by exact_mod_cast hPay
  have hh := mul_le_mul_of_nonneg_right hF (Nat.cast_nonneg (r*(f*k)) : (0:ℝ) ≤ _)
  have hh' := mul_le_mul_of_nonneg_left hPayR (sq_nonneg (ρ/128))
  nlinarith only [hh,hh']

/-- The coarse footprint bound after chord realization is compatible
with the smallness required for the free pairs. Here the scale of
one prescribed system is `φ = 8*g²/f`. -/
theorem chord_round_footprint_budget (f g ell m K : ℕ) (ρ : ℝ)
    (hf : 0 < f)
    (hK : (K:ℝ) ≤ (1+26*(ell:ℝ))*(8*(g:ℝ)^2/(f:ℝ))*(m:ℝ))
    (hF : (1+26*(ell:ℝ))*(8*(g:ℝ)^2) ≤ (ρ/512)*(f:ℝ)) :
    (K:ℝ) ≤ (ρ/512)*(m:ℝ) := by
  have hf' : (0:ℝ) < f := by exact_mod_cast hf
  have hScale : (1+26*(ell:ℝ))*(8*(g:ℝ)^2/(f:ℝ)) ≤ ρ/512 := by
    rw [←mul_div_assoc]
    exact (div_le_iff₀ hf').mpr hF
  exact hK.trans (mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg m))

end OverfullWork.DirectedRobustExpansion
