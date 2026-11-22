module

public import OverfullWork.OsthusStadenSpecialExceptionBudget

@[expose] public section


/-! Pay for the H1' clipping errors using the full primary cells. -/
namespace OverfullWork.DirectedRobustExpansion

/-- The two error margins for H1' follow from per-cell rates and the
total volume of the retained primary cells. -/
theorem special_red_profile_error_budget
    (K n M s p ell loss : ℕ) (e trim γ a : ℝ)
    (hEll : 0 < ell) (he : 0 ≤ e) (hTrim : 0 ≤ trim)
    (hVolume : (K:ℝ)*(M:ℝ) ≤ (n:ℝ)) (hLoss : ((loss+1:ℕ):ℝ) ≤ trim*(M:ℝ))
    (hLower : (s:ℝ)*(e/(ell:ℝ)+trim) ≤ γ*a/(180*(p:ℝ)))
    (hUpper : (s:ℝ)*e ≤ γ*a/(3*(p:ℝ))) :
    (K:ℝ)*((s-1:ℕ):ℝ)*((1-e)*(e*(M:ℝ)/(ell:ℝ))+((loss+1:ℕ):ℝ)) ≤
      γ*a*(n:ℝ)/(180*(p:ℝ)) ∧
    (K:ℝ)*((s-1:ℕ):ℝ)*e*(M:ℝ) ≤ γ*a*(n:ℝ)/(3*(p:ℝ)) := by
  have hEllR : 0 < (ell:ℝ) := by exact_mod_cast hEll
  have hs : (((s-1:ℕ):ℝ)) ≤ (s:ℝ) := by exact_mod_cast Nat.sub_le s 1
  have hBase : 0 ≤ (K:ℝ)*((s-1:ℕ):ℝ) := by positivity
  have hPerCell : (1-e)*(e*(M:ℝ)/(ell:ℝ))+((loss+1:ℕ):ℝ) ≤
      (e/(ell:ℝ)+trim)*(M:ℝ) := by
    calc
      _ ≤ (e*(M:ℝ)/(ell:ℝ))+trim*(M:ℝ) :=
        add_le_add (mul_le_of_le_one_left (by positivity) (by linarith only [he])) hLoss
      _ = _ := by ring
  constructor
  · calc
      _ ≤ (K:ℝ)*((s-1:ℕ):ℝ)*((e/(ell:ℝ)+trim)*(M:ℝ)) :=
        mul_le_mul_of_nonneg_left hPerCell hBase
      _ = (((s-1:ℕ):ℝ)*(e/(ell:ℝ)+trim))*((K:ℝ)*(M:ℝ)) := by ring
      _ ≤ ((s:ℝ)*(e/(ell:ℝ)+trim))*(n:ℝ) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hs (by positivity))
          hVolume (by positivity) (by positivity)
      _ ≤ (γ*a/(180*(p:ℝ)))*(n:ℝ) := mul_le_mul_of_nonneg_right hLower (Nat.cast_nonneg _)
      _ = _ := by ring
  · calc
      _ = (((s-1:ℕ):ℝ)*e)*((K:ℝ)*(M:ℝ)) := by ring
      _ ≤ ((s:ℝ)*e)*(n:ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hs he) hVolume (by positivity) (by positivity)
      _ ≤ (γ*a/(3*(p:ℝ)))*(n:ℝ) := mul_le_mul_of_nonneg_right hUpper (Nat.cast_nonneg _)
      _ = _ := by ring

end OverfullWork.DirectedRobustExpansion
