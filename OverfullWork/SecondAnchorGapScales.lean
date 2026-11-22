module

public import OverfullWork.CaseTwoInitialAnchors

@[expose] public section


/-! # Pay the second-anchor reserve from nonheavy-pair source scales

The error is 7 eta m + 25 B + 6 floor(m/T) + 36 T + 58.
Four explicit quarter-budget estimates put it below rho m.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open Finset
open scoped Classical
set_option maxHeartbeats 16000000

theorem source_half_order_bound (Q n m Y : ℕ) (hQ : 8 ≤ Q)
    (hCard : n+1=2*m+Y) (hY : Y ≤ n/(4096*Q^2)+1) : n ≤ 3*m := by
  have hCoeff : 3 ≤ 4096*Q^2 := by nlinarith only [hQ]
  have hDiv := (Nat.mul_le_mul_right (n/(4096*Q^2)) hCoeff).trans (Nat.mul_div_le n _)
  omega

theorem pay_second_anchor_source_budget (Q n m Y B : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hQ : 8 ≤ Q) (hCard : n+1=2*m+Y) (hY : Y ≤ n/(4096*Q^2)+1)
    (hB : B ≤ 6*(n/(4096*Q^2))+6)
    (hScale : 3600 ≤ ρ*((4096*Q^2:ℕ):ℝ)) (hOrder : 1200 ≤ ρ*(m:ℝ)) :
    100*(B:ℝ) ≤ ρ*(m:ℝ) := by
  let d := 4096*Q^2
  have hd : 0 < d := by dsimp only [d];positivity
  have hBound : d*B ≤ 6*n+6*d := by
    have hh := Nat.mul_le_mul_left d hB
    have hDiv := Nat.mul_div_le n d
    change B ≤ 6*(n/d)+6 at hB
    nlinarith
  have hBoundR : (d:ℝ)*(B:ℝ) ≤ 6*(n:ℝ)+6*(d:ℝ) := by exact_mod_cast hBound
  have hnmR : (n:ℝ) ≤ 3*(m:ℝ) := by exact_mod_cast source_half_order_bound Q n m Y hQ hCard hY
  have hS := mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hO := mul_le_mul_of_nonneg_right hOrder (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  change 3600*(m:ℝ) ≤ ρ*(d:ℝ)*(m:ℝ) at hS
  have hCompare : (d:ℝ)*(100*(B:ℝ)) ≤ (d:ℝ)*(ρ*(m:ℝ)) := by
    nlinarith only [hBoundR,hnmR,hS,hO]
  exact le_of_mul_le_mul_left hCompare (by exact_mod_cast hd : (0:ℝ) < d)

theorem pay_second_anchor_gap (m B T : ℕ) (η ρ μ Δ : ℝ) (hρ : 0 < ρ)
    (hη : η ≤ ρ/28) (hT : 24 ≤ ρ*(T:ℝ))
    (hB : 100*(B:ℝ) ≤ ρ*(m:ℝ)) (hOrder : 144*(T:ℝ)+232 ≤ ρ*(m:ℝ))
    (hNonheavy : μ+ρ*(m:ℝ) ≤ Δ) :
    μ+(B:ℝ)+η*(m:ℝ)+6*(η*(m:ℝ)+4*(B:ℝ)+((m/T:ℕ):ℝ)+6*(T:ℝ)+9)+4 ≤ Δ := by
  have hEta := mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hDiv : (T:ℝ)*((m/T:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.mul_div_le m T
  have hCut := mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg (m/T) : (0:ℝ) ≤ (m/T:ℕ))
  have hDivρ := mul_le_mul_of_nonneg_left hDiv hρ.le
  have hCutPaid : 24*((m/T:ℕ):ℝ) ≤ ρ*(m:ℝ) := by nlinarith only [hCut,hDivρ]
  linarith

end OverfullWork.NormalizedCanonicalCandidate
