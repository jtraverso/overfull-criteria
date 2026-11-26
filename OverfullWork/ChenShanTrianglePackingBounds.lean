module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Real Filter
open scoped Topology

private theorem eventually_rpow_dominates_polynomial (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ d : ℝ in atTop, 432 * d ^ 3 ≤ exp (d ^ β) := by
  have hLim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3/β) 1 (by norm_num)).comp
    (tendsto_rpow_atTop hβ)
  have hSmall := hLim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/432))
  filter_upwards [hSmall,eventually_ge_atTop (0 : ℝ)] with d hSmall hd
  change (d ^ β) ^ (3/β) * exp (-1 * d ^ β) < 1/432 at hSmall
  rw [← rpow_mul hd, show β * (3/β) = 3 by field_simp,
    show d ^ (3 : ℝ) = d ^ 3 by norm_cast, neg_one_mul,exp_neg,← div_eq_mul_inv] at hSmall
  have hUpper := (div_lt_iff₀ (exp_pos _)).mp hSmall
  linarith only [hUpper]

/-- For sufficiently large d, Chen–Shan's sampling parameters satisfy the
matching size and weight constraints and the requested error tolerance. -/
theorem eventually_triangle_packing_bounds (Δ₀ ζ : ℝ) (hζ : 0 < ζ) :
    ∀ᶠ d : ℝ in atTop,
      let u := d ^ (2/3 : ℝ)
      let Δ := d + u
      1 ≤ d ∧ Δ₀ ≤ Δ ∧
      432 * d ^ 3 ≤ exp (Δ ^ ((1/900 : ℝ) ^ 2)) ∧
      2 * Δ ^ (3/2 : ℝ) ≤ (d-u) * d ∧ 0 ≤ d-u ∧
      4 * (Δ ^ (-(1/900) : ℝ) + 2 * d ^ (-(1/3) : ℝ)) ≤ ζ := by
  let β : ℝ := (1/900)^2
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hγ : 0 < (1/900 : ℝ) := by norm_num
  have hThird : 0 < (1/3 : ℝ) := by norm_num
  have hHalf := (tendsto_rpow_neg_atTop hThird).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hSmallγ := (tendsto_rpow_neg_atTop hγ).eventually
    (gt_mem_nhds (show (0 : ℝ) < ζ/8 by positivity))
  have hSmallThird := (tendsto_rpow_neg_atTop hThird).eventually
    (gt_mem_nhds (show (0 : ℝ) < ζ/16 by positivity))
  filter_upwards [eventually_ge_atTop (256 : ℝ),eventually_ge_atTop Δ₀,
    eventually_rpow_dominates_polynomial β hβ,hHalf,hSmallγ,hSmallThird]
    with d h256 hBase hN hHalf hSmallγ hSmallThird
  change d ^ (-(1/3) : ℝ) < 1/2 at hHalf
  change d ^ (-(1/900) : ℝ) < ζ/8 at hSmallγ
  change d ^ (-(1/3) : ℝ) < ζ/16 at hSmallThird
  let u := d ^ (2/3 : ℝ)
  let Δ := d + u
  have hd : 1 ≤ d := by linarith only [h256]
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hu : 0 ≤ u := rpow_nonneg hd0.le _
  have hD : d ≤ Δ := le_add_of_nonneg_right hu
  have hu' : d ^ (-(1/3) : ℝ) * d = u := by
    change d ^ (-(1/3) : ℝ) * d = d ^ (2/3 : ℝ)
    conv_lhs => rhs; rw [← rpow_one d]
    rw [← rpow_add hd0]
    congr 1
    norm_num
  have huHalf : u ≤ d/2 := by
    rw [← hu']
    linarith only [mul_le_mul_of_nonneg_right hHalf.le hd0.le]
  have hDD : Δ ≤ 2*d := by dsimp only [Δ]; linarith only [huHalf,hd0]
  have hPower : Δ ^ (3/2 : ℝ) ≤ 4 * d ^ (3/2 : ℝ) := by
    calc
      _ ≤ (2*d) ^ (3/2 : ℝ) := rpow_le_rpow (hd0.le.trans hD) hDD (by norm_num)
      _ = (2:ℝ) ^ (3/2 : ℝ) * d ^ (3/2 : ℝ) := mul_rpow (by norm_num) hd0.le
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (rpow_nonneg hd0.le _)
        have h := rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
          (show (3/2:ℝ) ≤ 2 by norm_num)
        exact h.trans_eq (by norm_num)
  have hSqrt : 16 ≤ d ^ (1/2 : ℝ) := by
    have hConst : (16 : ℝ) ^ (2 : ℝ) = 256 := by norm_num
    have hEq : (256 : ℝ) ^ (1/2 : ℝ) = 16 := by
      rw [← hConst,← rpow_mul (by norm_num : (0:ℝ) ≤ 16)]
      norm_num
    exact hEq ▸ rpow_le_rpow (by norm_num) h256 (by norm_num : 0 ≤ (1/2 : ℝ))
  have hDsq : d ^ (1/2 : ℝ) * d ^ (3/2 : ℝ) = d^2 := by
    rw [← rpow_add hd0,show (1/2:ℝ) + 3/2 = 2 by norm_num]
    norm_cast
  have hHeavy : 2 * Δ ^ (3/2 : ℝ) ≤ (d-u) * d := by
    have h := mul_le_mul_of_nonneg_right hSqrt (rpow_nonneg hd0.le (3/2:ℝ))
    rw [hDsq] at h
    have hDiff := mul_le_mul_of_nonneg_right huHalf hd0.le
    nlinarith only [h,hPower,hDiff]
  have hE : 432 * d^3 ≤ exp (Δ ^ β) :=
    hN.trans (exp_le_exp.mpr (rpow_le_rpow hd0.le hD hβ.le))
  have hQ : Δ ^ (-(1/900) : ℝ) ≤ d ^ (-(1/900) : ℝ) :=
    rpow_le_rpow_of_nonpos hd0 hD (by norm_num)
  exact ⟨hd,hBase.trans hD,hE,hHeavy,by linarith only [huHalf,hd0],
    by linarith only [hQ,hSmallγ,hSmallThird]⟩

end OverfullWork.ChenShan
