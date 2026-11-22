module

public import OverfullWork.OsthusStadenFactorsFromBalancedLayer

@[expose] public section


/-! Integer margins for completing the κ-factor on every successor pair. -/
namespace OverfullWork.DirectedRobustExpansion

/-- Round the rectangle cutoff and ordinary red load. The density
surplus pays the rounding and the maximum red degree of an endpoint. -/
theorem exists_osthus_staden_dense_factor_margins
    (n κ : ℕ) (ε d redLoad : ℝ)
    (hε : 0 ≤ ε) (hLoad : 0 ≤ redLoad) (hDensity : 0 ≤ d-2*ε)
    (hTarget : (3/4)*(d-2*ε)*(n:ℝ) ≤ (κ:ℝ))
    (hRedSmall : redLoad+1 ≤ (d-2*ε)*(n:ℝ)/12)
    (hResidual : (κ:ℝ)+redLoad+1 ≤ (d-2*ε)*(n:ℝ))
    (hAvail : (κ:ℝ)+2 ≤ (d-3*ε)*(n:ℝ)) :
    ∃ cutoff minDemand : ℕ, OsthusStadenDenseFactorMargins n κ cutoff minDemand ε d ∧
      κ-minDemand = ⌈redLoad⌉₊ := by
  let width := ε*(n:ℝ)
  let cutoff := max 1 ⌈width⌉₊
  let red := ⌈redLoad⌉₊
  let minDemand := κ-red
  have hWidth : 0 ≤ width := by dsimp only [width]; positivity
  have hCutLo : width ≤ (cutoff:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈width⌉₊)
  have hCutHi : (cutoff:ℝ) ≤ width+1 := by
    rw [Nat.cast_max]
    exact max_le (by simpa only [Nat.cast_one] using le_add_of_nonneg_left hWidth) (Nat.ceil_lt_add_one hWidth).le
  have hRedRound : (red:ℝ) ≤ redLoad+1 := (Nat.ceil_lt_add_one hLoad).le
  have hRedPos : 0 ≤ (red:ℝ) := Nat.cast_nonneg _
  have hRedLe : red ≤ κ := by
    exact_mod_cast (show (red:ℝ) ≤ (κ:ℝ) by linarith only [hTarget,hRedSmall,hRedRound,hRedPos])
  have hMin : (minDemand:ℝ) = (κ:ℝ)-(red:ℝ) := Nat.cast_sub hRedLe
  refine ⟨cutoff,minDemand,⟨(by dsimp only [cutoff]; omega),?_,?_,hDensity,Nat.sub_le _ _,?_,?_,?_,?_⟩,?_⟩
  · simpa only [width,mul_comm ε] using hCutLo
  · dsimp only [width] at hCutHi
    linarith only [hCutHi,hAvail]
  · have h : (κ:ℝ) ≤ 2*(minDemand:ℝ) := by
      rw [hMin]
      linarith only [hTarget,hRedSmall,hRedRound,hRedPos]
    exact_mod_cast h
  · rw [hMin]
    linarith only [hTarget,hRedSmall,hRedRound]
  · linarith only [hResidual,hLoad]
  · rw [hMin]
    linarith only [hResidual,hRedRound]
  · dsimp only [minDemand]
    omega

end OverfullWork.DirectedRobustExpansion
