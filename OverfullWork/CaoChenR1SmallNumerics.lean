module

public import OverfullWork.CaoChenDischarging

@[expose] public section


/-! # Numerical estimate for the bounded-multiplicity small-root discharge

This file proves only the numerical estimate. The palette-counting and
donation estimates needed to apply it to R1 remain separate obligations.
-/
namespace OverfullWork.CaoChenDischarging

/-- The two possible costs, quadratic in `a` and reciprocal in `a`, cannot
both be small once the root degree exceeds the fourth-power threshold. -/
theorem small_root_fraction_bound {K d a : ℝ} (hK : 1 ≤ K)
    (ha : 0 < a) (had : a ≤ d) (hd : 2 * (K + 2) ^ 4 ≤ d) :
    K ≤ a ^ 2 / (2 * (K + 2) * d) + d / a - 1 := by
  have hB : 0 < K + 2 := by linarith
  have hdpos : 0 < d := ha.trans_le had
  have hden : 0 < 2 * (K + 2) * d := by positivity
  have hfirst : 0 ≤ a ^ 2 / (2 * (K + 2) * d) := by positivity
  by_cases hratio : K + 2 ≤ d / a
  · linarith
  · have hda : d ≤ a * (K + 2) := by
      have := (div_lt_iff₀ ha).mp (lt_of_not_ge hratio)
      nlinarith
    have hsq : d ^ 2 ≤ a ^ 2 * (K + 2) ^ 2 := by
      nlinarith [sq_nonneg (a * (K + 2) - d)]
    have hlarge : 2 * (K + 2) ^ 4 * d ≤ d ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hd hdpos.le]
    have hproduct : (2 * (K + 2) ^ 2 * d) * (K + 2) ^ 2 ≤
        a ^ 2 * (K + 2) ^ 2 := by
      calc
        _ = 2 * (K + 2) ^ 4 * d := by ring
        _ ≤ d ^ 2 := hlarge
        _ ≤ _ := hsq
    have hnum : 2 * (K + 2) ^ 2 * d ≤ a ^ 2 :=
      (mul_le_mul_iff_left₀ (sq_pos_of_pos hB)).mp hproduct
    have hquadratic : K + 2 ≤ a ^ 2 / (2 * (K + 2) * d) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith
    have hratio_one : 1 ≤ d / a := (le_div_iff₀ ha).mpr (by simpa using had)
    linarith

/-- Natural multiplicity-cap form, suitable for the palette-counting API. -/
theorem small_root_fraction_bound_nat {K d : ℕ} {a : ℝ} (hK : 1 ≤ K)
    (ha : 0 < a) (had : a ≤ d) (hd : 2 * (K + 2) ^ 4 ≤ d) :
    (K : ℝ) ≤ a ^ 2 / (2 * ((K : ℝ) + 2) * d) + d / a - 1 := by
  apply small_root_fraction_bound (by exact_mod_cast hK) ha had
  exact_mod_cast hd

/-- With a multiplicity cap paying `ε K ≥ 2`, the same estimate supplies
the factor two in the small-root donation budget. -/
theorem two_le_small_root_scaled_fraction {ε K d a : ℝ} (hε : 0 < ε)
    (hK : 1 ≤ K) (hεK : 2 ≤ ε * K) (ha : 0 < a) (had : a ≤ d)
    (hd : 2 * (K + 2) ^ 4 ≤ d) :
    2 ≤ ε * (a ^ 2 / (2 * (K + 2) * d) + d / a - 1) := by
  exact hεK.trans (mul_le_mul_of_nonneg_left
    (small_root_fraction_bound hK ha had hd) hε.le)

end OverfullWork.CaoChenDischarging
