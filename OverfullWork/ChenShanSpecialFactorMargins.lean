module

public import OverfullWork.ChenShanAugmentationBudget
public import OverfullWork.KuhnOsthusExceptionalPairStability
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

/-- Explicit sufficient margins for the integer augmentation cap and
the maximum number of saturated vertices in one subcluster. -/
theorem exists_special_factor_augmentation_margins
    (s b n : ℕ) (d : ℝ) (hd : 0 < d) (hdOne : d ≤ 1)
    (hLarge : 200 ≤ d*n) (hLocal : (b:ℝ) ≤ d*n/100)
    (hGlobal : (s:ℝ)*b ≤ d^3*(n:ℝ)^2/80000) :
    ∃ forbidden cap : ℕ, 0 < cap ∧ 4*s*b ≤ forbidden*cap ∧
      b+forbidden ≤ n ∧ ((b+forbidden+cap : ℕ):ℝ) ≤ d*n/2 := by
  let forbidden := ⌊d*n/100⌋₊
  let cap := ⌈d^2*n/100⌉₊
  have hn : 0 < (n:ℝ) := by by_contra! h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hd.le h]
  have hForbidUpper : (forbidden:ℝ) ≤ d*n/100 := Nat.floor_le (by positivity)
  have hForbidLower : d*n/200 ≤ (forbidden:ℝ) := by
    have h := Nat.lt_floor_add_one (d*n/100)
    change d*n/100 < (forbidden:ℝ)+1 at h
    linarith only [h, hLarge]
  have hCapLower : d^2*n/100 ≤ (cap:ℝ) := Nat.le_ceil _
  have hCapUpper : (cap:ℝ) < d^2*n/100+1 := Nat.ceil_lt_add_one (by positivity)
  have hBudget : (4*(s:ℝ)*b) ≤ (forbidden:ℝ)*(cap:ℝ) := by
    have hProduct := mul_le_mul hForbidLower hCapLower (by positivity) (Nat.cast_nonneg _)
    nlinarith only [hGlobal, hProduct]
  have hDegree : d^2*(n:ℝ) ≤ d*n := by
    apply mul_le_mul_of_nonneg_right _ hn.le
    nlinarith only [mul_nonneg hd.le (sub_nonneg.mpr hdOne)]
  have hSize : d*(n:ℝ) ≤ n := by simpa using mul_le_mul_of_nonneg_right hdOne hn.le
  have hLeft : (b:ℝ)+(forbidden:ℝ) ≤ n := by linarith only [hLocal, hForbidUpper, hSize, hLarge]
  have hRight : (b:ℝ)+(forbidden:ℝ)+(cap:ℝ) ≤ d*n/2 := by
    linarith only [hLocal, hForbidUpper, hCapUpper, hDegree, hLarge]
  have hPos : 0 < (cap:ℝ) := (show 0 < d^2*n/100 by positivity).trans_le hCapLower
  exact ⟨forbidden,cap,by exact_mod_cast hPos,by exact_mod_cast hBudget,
    by exact_mod_cast hLeft,by exact_mod_cast hRight⟩

/-- Explicit choices for residual superregularity and the integer
Hall threshold in the filling reserve. -/
theorem exists_special_factor_filling_margins
    (s b n : ℕ) (ε d : ℝ) (hd : 0 < d) (hdOne : d ≤ 1)
    (hLarge : 200 ≤ d*n) (hLocal : (b:ℝ) ≤ d*n/100)
    (hε : ε ≤ d/64) (hRounds : (s:ℝ) ≤ d^2*n/512) :
    ∃ (η a : ℝ) (r : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 ≤ a ∧
      2*(ε+a) ≤ η ∧ (s:ℝ) ≤ a*((n:ℝ)*η) ∧ 2*η < d ∧
      0 < r ∧ (n:ℝ)*η ≤ (r:ℝ) ∧ (r:ℝ)+(b:ℝ) ≤ (d-η)*(n:ℝ) := by
  let η := d/8
  let a := d/64
  let r := ⌈(n:ℝ)*η⌉₊
  have hnη : (n:ℝ)*η = (d*n)/8 := by dsimp [η]; ring
  have hLowR : (n:ℝ)*η ≤ (r:ℝ) := Nat.le_ceil _
  have hHighR : (r:ℝ) < (n:ℝ)*η+1 := Nat.ceil_lt_add_one (by dsimp [η]; positivity)
  have hR : 0 < (r:ℝ) := by linarith only [hnη, hLarge, hLowR]
  have hBudget : (s:ℝ) ≤ a*((n:ℝ)*η) := by
    have he : a*((n:ℝ)*η) = d^2*n/512 := by dsimp [a, η]; ring
    rw [he]
    exact hRounds
  have hDense : (d-η)*(n:ℝ) = 7*(d*n)/8 := by dsimp [η]; ring
  exact ⟨η,a,r,by dsimp [η]; linarith,by dsimp [η]; linarith,
    by dsimp [a]; linarith,by dsimp [η,a]; linarith,
    hBudget,by dsimp [η]; linarith,by exact_mod_cast hR,hLowR,
    by linarith only [hDense,hnη,hLocal,hHighR,hLarge]⟩

open Finset DirectedRobustExpansion
open scoped Classical

/-- The directed form of a superregular augmentation pair supplies
the neighbor margin needed by the global realization. -/
theorem special_factor_augmentation_room_of_superregular
    {V : Type*} [Fintype V] (D : Digraph V) (L R : Finset V)
    (n need : ℕ) (ε d : ℝ) (hSize : R.card = n)
    (hε : ε ≤ d/2) (hNeed : (need:ℝ) ≤ d*n/2)
    (hPair : IsLowerSuperregularPair D ε d L R) :
    ∀ x ∈ L, need ≤ (R.filter (D.Adj x)).card := by
  intro x hx
  have hDeg := (IsLowerSuperregularPair.physical_lower_bounds D L R d ε hPair).1 x hx
  rw [hSize] at hDeg
  have hMono := mul_le_mul_of_nonneg_right (show d/2 ≤ d-ε by linarith) (Nat.cast_nonneg (α := ℝ) n)
  have h : (need:ℝ) ≤ ((R.filter (D.Adj x)).card:ℝ) := by
    linarith only [hNeed, hMono, hDeg]
  exact_mod_cast h

end OverfullWork.ChenShan
