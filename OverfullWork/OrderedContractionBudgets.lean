module

public import OverfullWork.PairedEndpointContraction

@[expose] public section


/-! Pay the change in the endpoint count hypothesis between KLO
Corollary 6.9 (fourth power) and Corollary 6.8 (third power), after the
actual contraction changes both order and robust expansion parameter. -/
namespace OverfullWork.DirectedEndpointContraction

theorem fourth_power_ordered_budget (n p : ℕ) (ν : ℝ)
    (hν : 0 < ν) (hνSmall : ν ≤ 1/16) (hLarge : 16 ≤ ν*(n:ℝ))
    (hP : (p:ℝ) ≤ ν^4*(n:ℝ)) :
    (p:ℝ) ≤ (ν/2)^3*((n-p:ℕ):ℝ) := by
  obtain ⟨hQuarter,_⟩ := fourth_power_contraction_budgets n p ν hν (by linarith) hLarge hP
  have hPN : p≤n := by exact_mod_cast (show (p:ℝ)≤(n:ℝ) by linarith)
  have hCast : ((n-p:ℕ):ℝ)=(n:ℝ)-(p:ℝ) := Nat.cast_sub hPN
  have hHalf : (n:ℝ)/2 ≤ ((n-p:ℕ):ℝ) := by rw [hCast];linarith
  have hCube : 0≤ν^3 := pow_nonneg hν.le _
  have hN : (0:ℝ)≤n := Nat.cast_nonneg n
  have hMul := mul_le_mul_of_nonneg_right hνSmall (mul_nonneg hCube hN)
  have hEndpoint : (p:ℝ)≤ν^3*(n:ℝ)/16 := by nlinarith only [hP,hMul]
  have hCompare := mul_le_mul_of_nonneg_left hHalf (div_nonneg hCube (by norm_num : (0:ℝ)≤8))
  nlinarith only [hEndpoint,hCompare]

theorem contracted_order_threshold (n p N : ℕ)
    (hQuarter : 4*p≤n) (hLarge : 2*N≤n) : N≤n-p := by omega

end OverfullWork.DirectedEndpointContraction
