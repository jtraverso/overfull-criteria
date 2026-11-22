module

public import OverfullWork.OsthusStadenSharedBalancingReserve

@[expose] public section


/-! Integer capacities for the H2 selections of §5.9. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical

/-- Use a fixed fraction of each half-cell for the density estimate.
The degree cap is the normalized demand rounded up, and the previous
layers consume at most half of the available density margin. -/
theorem exists_balancing_pair_budgets
    (m layers bound halfLoss : ℕ) (densityMargin : ℝ)
    (hm : 8 ≤ m) (hTrim : halfLoss+1 ≤ m/4) (hDensity : 0 ≤ densityMargin)
    (hUsed : 2*((layers-1:ℕ):ℝ)*(8*(bound:ℝ)/(m:ℝ)+1) ≤ densityMargin*((m/2:ℕ):ℝ))
    (hNeed : 2*(bound:ℝ) ≤ densityMargin*((m/2:ℕ):ℝ)^2) :
    ∃ cap loss cutoff used : ℕ,
      0 < cutoff ∧ 0 < cap ∧ cutoff = m/2 ∧
      bound ≤ cap*loss ∧ cutoff+loss+halfLoss+1 ≤ m ∧
      (layers-1)*cap ≤ used ∧ (cap:ℝ) ≤ 8*(bound:ℝ)/(m:ℝ)+1 ∧
      0 ≤ densityMargin*(cutoff:ℝ)-(used:ℝ) ∧
      (bound:ℝ) ≤ (densityMargin*(cutoff:ℝ)-(used:ℝ))*(cutoff:ℝ) := by
  let rate := 8*(bound:ℝ)/(m:ℝ)
  let cap := max 1 ⌈rate⌉₊
  let loss := m/4
  let cutoff := m/2
  let used := (layers-1)*cap
  have hmR : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hRate : 0 ≤ rate := by dsimp only [rate]; positivity
  have hCap : (cap:ℝ) ≤ rate+1 := by
    rw [Nat.cast_max]
    exact max_le (by simpa only [Nat.cast_one] using le_add_of_nonneg_left hRate) (Nat.ceil_lt_add_one hRate).le
  have hRateCap : rate ≤ (cap:ℝ) :=
    (Nat.le_ceil rate).trans (by exact_mod_cast le_max_right 1 ⌈rate⌉₊)
  have hSaturation : bound ≤ cap*loss := by
    have hLoss : (m:ℝ)/8 ≤ (loss:ℝ) := by
      have h : m ≤ 8*loss := by dsimp only [loss]; omega
      have h' : (m:ℝ) ≤ 8*(loss:ℝ) := by exact_mod_cast h
      linarith only [h']
    have h : (bound:ℝ) ≤ (cap:ℝ)*(loss:ℝ) := by
      calc
        _ = rate*((m:ℝ)/8) := by dsimp only [rate]; field_simp
        _ ≤ _ := mul_le_mul hRateCap hLoss (by positivity) (Nat.cast_nonneg _)
    exact_mod_cast h
  have hSpent : 2*(used:ℝ) ≤ densityMargin*(cutoff:ℝ) := by
    calc
      _ = (2*((layers-1:ℕ):ℝ))*(cap:ℝ) := by rw [show used = (layers-1)*cap from rfl,Nat.cast_mul]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hCap (by positivity)).trans hUsed
  have hRemain : densityMargin*(cutoff:ℝ)/2 ≤ densityMargin*(cutoff:ℝ)-(used:ℝ) := by
    linarith only [hSpent]
  refine ⟨cap,loss,cutoff,used,by dsimp only [cutoff]; omega,
    (by dsimp only [cap]; omega),rfl,hSaturation,by dsimp only [cutoff,loss]; omega,
    le_rfl,hCap,(by positivity : 0 ≤ densityMargin*(cutoff:ℝ)/2).trans hRemain,?_⟩
  calc
    _ ≤ densityMargin*(cutoff:ℝ)^2/2 := by
      change 2*(bound:ℝ) ≤ densityMargin*(cutoff:ℝ)^2 at hNeed
      linarith only [hNeed]
    _ = (densityMargin*(cutoff:ℝ)/2)*(cutoff:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hRemain (Nat.cast_nonneg _)

end OverfullWork.DirectedRobustExpansion
