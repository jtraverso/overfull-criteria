module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

/-- The common order of the two core classes at successive levels of
the nested sets in Step 1 of Theorem 4.15. -/
noncomputable def nestedCoreSize (ρ : ℝ) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | i+1 => ⌈ρ*(nestedCoreSize ρ m i : ℝ)⌉₊

theorem nestedCoreSize_step_lower (ρ : ℝ) (m i : ℕ) :
    ρ*(nestedCoreSize ρ m i : ℝ) ≤ nestedCoreSize ρ m (i+1) :=
  Nat.le_ceil _

theorem nestedCoreSize_step_upper (ρ : ℝ) (hρ : 0 ≤ ρ) (m i : ℕ) :
    (nestedCoreSize ρ m (i+1) : ℝ) < ρ*(nestedCoreSize ρ m i : ℝ)+1 :=
  Nat.ceil_lt_add_one (mul_nonneg hρ (Nat.cast_nonneg _))

theorem nestedCoreSize_two_steps (ρ : ℝ) (hρ : 0 ≤ ρ) (m i : ℕ) :
    ρ^2*(nestedCoreSize ρ m i : ℝ) ≤ nestedCoreSize ρ m (i+2) := by
  calc
    _ = ρ*(ρ*(nestedCoreSize ρ m i : ℝ)) := by ring
    _ ≤ ρ*(nestedCoreSize ρ m (i+1) : ℝ) :=
      mul_le_mul_of_nonneg_left (nestedCoreSize_step_lower ρ m i) hρ
    _ ≤ _ := nestedCoreSize_step_lower ρ m (i+1)

theorem nestedCoreSize_monotone_down (ρ : ℝ) (hρ : ρ ≤ 1) (m i : ℕ) :
    nestedCoreSize ρ m (i+1) ≤ nestedCoreSize ρ m i := by
  change ⌈ρ*(nestedCoreSize ρ m i : ℝ)⌉₊ ≤ nestedCoreSize ρ m i
  apply Nat.ceil_le.mpr
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg (α := ℝ) _)

theorem nestedCoreSize_geometric (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ : ρ ≤ 1/2)
    (m i : ℕ) (hi : 4 ≤ nestedCoreSize ρ m i) :
    (nestedCoreSize ρ m (i+1) : ℝ) ≤ (3/4)*(nestedCoreSize ρ m i : ℝ) := by
  have h4 : (4:ℝ) ≤ nestedCoreSize ρ m i := by exact_mod_cast hi
  have hMul := mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg (α := ℝ) (nestedCoreSize ρ m i))
  have hUp := nestedCoreSize_step_upper ρ hρ₀ m i
  linarith only [hMul,h4,hUp]

/-- The first level below h exists, so the final retained level has
order between h and h/ρ, as required for the bounded absorber. -/
theorem exists_last_nested_core_size (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ : ρ ≤ 1/2)
    (m h : ℕ) (hh : 4 ≤ h) (hm : h ≤ m) :
    ∃ l : ℕ, (∀ i ≤ l, h ≤ nestedCoreSize ρ m i) ∧
      nestedCoreSize ρ m (l+1) < h ∧ (nestedCoreSize ρ m l : ℝ) < h/ρ := by
  have hExit : ∃ k, nestedCoreSize ρ m k < h := by
    by_contra! hAll
    have hDecrease (i : ℕ) : nestedCoreSize ρ m (i+1) < nestedCoreSize ρ m i := by
      have hi := hh.trans (hAll i)
      have hUp := nestedCoreSize_geometric ρ hρ₀.le hρ m i hi
      have hi' : (4:ℝ) ≤ nestedCoreSize ρ m i := by exact_mod_cast hi
      exact_mod_cast (show (nestedCoreSize ρ m (i+1):ℝ) <
        (nestedCoreSize ρ m i:ℝ) by linarith only [hUp,hi'])
    have hBound (i : ℕ) : nestedCoreSize ρ m i + i ≤ m := by
      induction i with
      | zero => simp [nestedCoreSize]
      | succ i ih =>
        have h := hDecrease i
        omega
    have h := hBound (m+1)
    omega
  let k := Nat.find hExit
  have hk : nestedCoreSize ρ m k < h := Nat.find_spec hExit
  have hk₀ : k ≠ 0 := by
    intro hZero
    rw [hZero] at hk
    have hk' : m < h := hk
    omega
  let l := k-1
  have hl : l+1 = k := by dsimp only [l]; omega
  have hl' : nestedCoreSize ρ m (l+1) < h := by rwa [hl]
  refine ⟨l,?_,hl',?_⟩
  · intro i hi
    have hlt : i < Nat.find hExit := by change i < k; omega
    exact Nat.le_of_not_gt (Nat.find_min hExit hlt)
  · apply (lt_div_iff₀ hρ₀).mpr
    have hLow := nestedCoreSize_step_lower ρ m l
    have hHi : (nestedCoreSize ρ m (l+1) : ℝ) < h := by exact_mod_cast hl'
    linarith only [hLow,hHi,show (nestedCoreSize ρ m l:ℝ)*ρ = ρ*nestedCoreSize ρ m l by ring]

/-- The nearest-integer order of the color class at a given level. -/
noncomputable def nestedColorSize (p : ℝ) (n : ℕ) : ℕ :=
  ⌊p*n+1/2⌋₊

theorem nestedColorSize_mono (p : ℝ) (hp : 0 ≤ p) : Monotone (nestedColorSize p) := by
  intro a b hab
  unfold nestedColorSize
  apply Nat.floor_mono
  gcongr

theorem nestedColorSize_error (p : ℝ) (hp : 0 ≤ p) (n : ℕ) :
    |(nestedColorSize p n : ℝ)-p*n| ≤ 1/2 := by
  have h1 := Nat.floor_le (show 0 ≤ p*(n:ℝ)+1/2 by positivity)
  have h2 := Nat.lt_floor_add_one (p*(n:ℝ)+1/2)
  change (nestedColorSize p n : ℝ) ≤ p*n+1/2 at h1
  change p*n+1/2 < (nestedColorSize p n : ℝ)+1 at h2
  exact abs_le.mpr ⟨by linarith only [h2],by linarith only [h1]⟩

theorem nestedColorSize_at_full (k m : ℕ) (hm : 0 < m) :
    nestedColorSize ((k:ℝ)/m) m = k := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  unfold nestedColorSize
  rw [div_mul_cancel₀ _ hm'.ne']
  exact (Nat.floor_eq_iff (by positivity : 0 ≤ (k:ℝ)+1/2)).2
    ⟨by linarith,by linarith⟩

end OverfullWork.ChenShan
