module

public import OverfullWork.DynamicBudgetMargins

@[expose] public section


/-! # Fix the route-length cap before choosing the seed-error scale

The actual robust rate is floor(m/d)-4H. For large m it dominates
m/(2d). The integer gain floor(m/(4d)) gives a fixed cap 8d+3,
independent of the later error cutoff and graph order.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open scoped Classical
set_option maxHeartbeats 24000000

theorem fixed_layer_round_bound (d m : ℕ) (hd : 0 < d) (hm : 8*d ≤ m) :
    0 < m/(4*d) ∧ m/(m/(4*d))+3 ≤ 8*d+3 := by
  have h4d : 0 < 4*d := by omega
  have hg : 1 ≤ m/(4*d) := (Nat.le_div_iff_mul_le h4d).mpr (by omega)
  have hFloor := Nat.lt_mul_div_succ m h4d
  have hProduct : 4*d*(m/(4*d)+1) ≤ (8*d)*(m/(4*d)) := by nlinarith
  have hRatio : m/(m/(4*d)) < 8*d := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith)
  omega

theorem actual_robust_rate_lower (d m H : ℕ) (hd : 0 < d) (hm : 8*d*(H+1) ≤ m) :
    (m:ℝ)/(2*(d:ℝ)) ≤ (m/d-4*H:ℕ) := by
  have hDiv : 8*(H+1) ≤ m/d := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith)
  have hFloor : (m:ℝ) < (d:ℝ)*((m/d:ℕ)+1) := by exact_mod_cast Nat.lt_mul_div_succ m hd
  have hLarge : 8*(d:ℝ)*((H:ℝ)+1) ≤ m := by exact_mod_cast hm
  have hPos : (0:ℝ) < d := by exact_mod_cast hd
  rw [Nat.cast_sub (show 4*H ≤ m/d by omega)]
  push_cast
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(d:ℝ))).mpr
  nlinarith only [hFloor,hLarge]

end OverfullWork.NormalizedCanonicalCandidate
