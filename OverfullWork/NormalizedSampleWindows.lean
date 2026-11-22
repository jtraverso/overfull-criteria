module

public import OverfullWork.TwoSidedNormalizedLifting

@[expose] public section


/-! Fixed-cardinality sample windows pay the normalized lifting budgets.
All inequalities are deterministic, on the common expectation and error. -/
namespace OverfullWork.TwoSidedClusterQuotient
open scoped Classical
set_option maxHeartbeats 18000000

theorem normalized_sample_windows (n q : ℕ) (z E ρ τ ε : ℝ)
    (hn : 0 < n) (hq : 0 < q) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hτ : 0 < τ) (hτQuarter : τ ≤ 1/4) (hTauQ : 8 ≤ τ*(q:ℝ))
    (hError : 0 ≤ E) (hε : 0 ≤ ε) (hεSmall : ε ≤ ρ/128)
    (hLow : (1-ρ/64)*(n:ℝ) ≤ z*(q:ℝ)) (hHigh : z*(q:ℝ) ≤ (n:ℝ))
    (hErrorQ : E*(q:ℝ) ≤ ρ*(n:ℝ)/1024)
    (hRound : (q:ℝ) ≤ ρ*(n:ℝ)/1024) :
    let m := ⌊z-E⌋₊
    let M := ⌈z+E⌉₊
    0 < m ∧ m ≤ M ∧ n ≤ 2*m*q ∧
      ((M-m:ℕ):ℝ)*(q:ℝ) ≤ ρ*(n:ℝ)/32 ∧
      (M:ℝ)*(q:ℝ) ≤ (1+ρ/32)*(n:ℝ) ∧
      (q:ℝ) ≤ ρ*(n:ℝ)/64 ∧ (M:ℝ) ≤ τ*(n:ℝ)/4 ∧
      ε*(M:ℝ)*(q:ℝ) ≤ ρ*(n:ℝ)/64 ∧ 2*⌈τ*(q:ℝ)⌉₊ ≤ q ∧ 2 ≤ z-E := by
  dsimp only
  let m := ⌊z-E⌋₊
  let M := ⌈z+E⌉₊
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hRhoN := mul_le_mul_of_nonneg_right hρ1 hnR.le
  have hZ : 2 ≤ z-E := by
    by_contra hh
    have hz : z-E < 2 := lt_of_not_ge hh
    have hMult := mul_lt_mul_of_pos_right hz hqR
    nlinarith only [hLow,hErrorQ,hRound,hRhoN,hMult,hnR]
  have hFloorUpper : (m:ℝ) ≤ z-E := Nat.floor_le (by linarith only [hZ])
  have hFloorLower : z-E < (m:ℝ)+1 := Nat.lt_floor_add_one _
  have hCeilLower : z+E ≤ (M:ℝ) := Nat.le_ceil _
  have hCeilUpper : (M:ℝ) < z+E+1 := Nat.ceil_lt_add_one (by linarith only [hZ,hError])
  have hm : 0 < m := by
    have hh : (0:ℝ) < m := by linarith only [hZ,hFloorLower]
    exact_mod_cast hh
  have hmM : m ≤ M := by
    have hh : (m:ℝ) ≤ (M:ℝ) := by linarith only [hFloorUpper,hCeilLower,hError]
    exact_mod_cast hh
  have hLowerQ := mul_lt_mul_of_pos_right hFloorLower hqR
  have hUpperQ := mul_lt_mul_of_pos_right hCeilUpper hqR
  have hMass : n ≤ 2*m*q := by
    have hh : (n:ℝ) ≤ 2*(m:ℝ)*(q:ℝ) := by
      nlinarith only [hLow,hLowerQ,hErrorQ,hRound,hRhoN,hnR]
    exact_mod_cast hh
  have hGap : ((M-m:ℕ):ℝ)*(q:ℝ) ≤ ρ*(n:ℝ)/32 := by
    rw [Nat.cast_sub hmM]
    nlinarith only [hUpperQ,hLowerQ,hErrorQ,hRound]
  have hUpper : (M:ℝ)*(q:ℝ) ≤ (1+ρ/32)*(n:ℝ) := by
    nlinarith only [hUpperQ,hHigh,hErrorQ,hRound]
  have hUpper2 : (M:ℝ)*(q:ℝ) ≤ 2*(n:ℝ) := by
    nlinarith only [hUpper,hRhoN]
  have hCell : (M:ℝ) ≤ τ*(n:ℝ)/4 := by
    have hScaled := mul_le_mul_of_nonneg_left hUpper2 hτ.le
    have hMin := mul_le_mul_of_nonneg_left hTauQ (Nat.cast_nonneg M : (0:ℝ) ≤ M)
    nlinarith only [hScaled,hMin]
  have hSource : ε*(M:ℝ)*(q:ℝ) ≤ ρ*(n:ℝ)/64 := by
    have hScaled := mul_le_mul_of_nonneg_left hUpper2 hε
    have hSmall := mul_le_mul_of_nonneg_right hεSmall hnR.le
    nlinarith only [hScaled,hSmall]
  have hNonvacuous : 2*⌈τ*(q:ℝ)⌉₊ ≤ q := by
    have hCeil : (⌈τ*(q:ℝ)⌉₊:ℝ) < τ*(q:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
    have hCap := mul_le_mul_of_nonneg_right hτQuarter hqR.le
    have hh : (2:ℝ)*(⌈τ*(q:ℝ)⌉₊:ℝ) ≤ (q:ℝ) := by linarith only [hCeil,hCap,hTauQ]
    exact_mod_cast hh
  exact ⟨hm,hmM,hMass,hGap,hUpper,by nlinarith only [hRound,hρ,hnR],hCell,hSource,hNonvacuous,hZ⟩

end OverfullWork.TwoSidedClusterQuotient
