module

public import OverfullWork.DynamicBudgetMargins
public import OverfullWork.SecondAnchorGapScales

@[expose] public section


/-! # Pay a chosen seed-error rate from the original sparse source budget

Choose the finer source scale before T, eta and the graph. Enlarging
the order then pays A0<=delta*m, the numerical input required by the
proved dynamic forbidden/deletion margin theorem.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open Finset
open scoped Classical
set_option maxHeartbeats 20000000

theorem seed_error_rate_of_reserves (m B T : ℕ) (η δ : ℝ) (hδ : 0 < δ)
    (hη : η ≤ δ/4) (hT : 4 ≤ δ*(T:ℝ)) (hB : 100*(B:ℝ) ≤ δ*(m:ℝ))
    (hOrder : 24*(T:ℝ)+36 ≤ δ*(m:ℝ)) :
    η*(m:ℝ)+4*(B:ℝ)+((m/T:ℕ):ℝ)+6*(T:ℝ)+9 ≤ δ*(m:ℝ) := by
  have hEta := mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hDiv : (T:ℝ)*((m/T:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.mul_div_le m T
  have hCut := mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg (m/T) : (0:ℝ) ≤ (m/T:ℕ))
  have hDivδ := mul_le_mul_of_nonneg_left hDiv hδ.le
  have hCutPaid : 4*((m/T:ℕ):ℝ) ≤ δ*(m:ℝ) := by nlinarith only [hCut,hDivδ]
  have hBR : (0:ℝ) ≤ B := Nat.cast_nonneg _
  linarith

theorem exists_uniform_seed_error_scale (δ : ℝ) (hδ : 0 < δ) (Q₀ : ℕ) (hQ₀ : 8 ≤ Q₀) :
    ∃ Q : ℕ, Q₀ ≤ Q ∧ ∀ T : ℕ, 4 ≤ δ*(T:ℝ) →
      ∀ η : ℝ, η ≤ δ/4 → ∃ N : ℕ,
      ∀ n m Y B : ℕ, N ≤ n → n+1=2*m+Y →
        Y ≤ n/(4096*Q^2)+1 → B ≤ 6*(n/(4096*Q^2))+6 →
        η*(m:ℝ)+4*(B:ℝ)+((m/T:ℕ):ℝ)+6*(T:ℝ)+9 ≤ δ*(m:ℝ) := by
  obtain ⟨L,hL⟩ := exists_nat_gt (3600/δ)
  let Q := max Q₀ L
  have h₀Q : Q₀ ≤ Q := le_max_left _ _
  have hQ : 8 ≤ Q := hQ₀.trans h₀Q
  have hLQ : (L:ℝ) ≤ Q := by exact_mod_cast (le_max_right Q₀ L)
  have hScale : 3600 ≤ δ*((4096*Q^2:ℕ):ℝ) := by
    have hδL := (div_lt_iff₀ hδ).mp hL
    have hDen : Q ≤ 4096*Q^2 := by nlinarith only [hQ]
    have hDenR : (Q:ℝ) ≤ ((4096*Q^2:ℕ):ℝ) := by exact_mod_cast hDen
    nlinarith only [hδ,hδL,hLQ,hDenR]
  refine ⟨Q,h₀Q,?_⟩
  intro T hT η hη
  obtain ⟨M,hM⟩ := exists_nat_gt ((max (1200:ℝ) (24*(T:ℝ)+36))/δ)
  refine ⟨3*M,?_⟩
  intro n m Y B hn hCard hY hB
  have hnm := source_half_order_bound Q n m Y hQ hCard hY
  have hMm : M ≤ m := by omega
  have hMmR : (M:ℝ) ≤ m := by exact_mod_cast hMm
  have hOrder : max (1200:ℝ) (24*(T:ℝ)+36) ≤ δ*(m:ℝ) := by
    have hh := (div_lt_iff₀ hδ).mp hM
    nlinarith only [hh,hMmR,hδ]
  have hPaidB := pay_second_anchor_source_budget Q n m Y B δ hδ hQ hCard hY hB hScale
    ((le_max_left _ _).trans hOrder)
  exact seed_error_rate_of_reserves m B T η δ hδ hη hT hPaidB ((le_max_right _ _).trans hOrder)

end OverfullWork.NormalizedCanonicalCandidate
