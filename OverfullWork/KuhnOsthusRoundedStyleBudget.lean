module

public import OverfullWork.KuhnOsthusPathPartitionBounds

@[expose] public section


/-! Choosing the number of ordinary pieces by floor division removes
the need for an extra divisibility hypothesis in Lemma 8.1. -/
namespace OverfullWork.DirectedRobustExpansion

theorem rounded_style_budget {s n q : ℕ}
    (hq : 2452 ≤ q) (hsq : s ≤ 1226 * (q+1))
    (hs : 3 ≤ s) (hn : s ≤ n) :
    (⌈(n : ℝ) / q⌉₊ : ℝ) + n / ((s : ℝ) - 1) + n / (s : ℝ)
      ≤ 1230 * n / (s : ℝ) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hs1 : (0 : ℝ) < (s : ℝ) - 1 := by
    have : (3 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hQ : (s : ℝ) ≤ (2453 / 2 : ℝ) * q := by
    have h₁ : (s : ℝ) ≤ 1226 * ((q : ℝ) + 1) := by exact_mod_cast hsq
    have h₂ : (2452 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hS : (s : ℝ) ≤ (3 / 2 : ℝ) * ((s : ℝ) - 1) := by
    have : (3 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hA : (n : ℝ) / q ≤ (2453 / 2 : ℝ) * n / s := by
    apply (div_le_div_iff₀ hq0 hs0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hQ hn0]
  have hC : (n : ℝ) / ((s : ℝ) - 1) ≤ (3 / 2 : ℝ) * n / s := by
    apply (div_le_div_iff₀ hs1 hs0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hS hn0]
  have hCeil := (Nat.ceil_lt_add_one (div_nonneg hn0 hq0.le)).le
  have hOne : (1 : ℝ) ≤ n / s := (le_div_iff₀ hs0).mpr (by exact_mod_cast (by simpa using hn : 1*s ≤ n))
  have he : (2453 / 2 : ℝ) * n / s + (3 / 2 : ℝ) * n / s +
      n / s + n / s = 1230 * n / s := by ring
  linarith

end OverfullWork.DirectedRobustExpansion
