module

public import OverfullWork.OsthusStadenCoreDegreeBudget

@[expose] public section


/-! The quantitative benefit of applying Claim 5.3 to the retained
sets, as used in the degree estimate in §5.6. -/
namespace OverfullWork.DirectedRobustExpansion

/-- The bank grows linearly with the number of original factors times
the number of directional labels in a primary cluster. -/
theorem exceptionalPhaseBankSize_lower (r s p : ℕ) (hs : 2 ≤ s) (hp : 3 ≤ p) :
    2*(r:ℝ)*((s-1:ℕ):ℝ) ≤ 9*(exceptionalPhaseBankSize r (2*s) p:ℝ) := by
  let W := r/(2*p)+1
  let Q := (2*s-1)*(p-1)
  have hQ : 2 ≤ Q := by
    exact (show 1*2 ≤ Q from Nat.mul_le_mul (by omega) (by omega))
  have hW : 1 ≤ W := Nat.le_add_left _ _
  have hSmall : 2 ≤ W*Q := hQ.trans (by simpa only [one_mul] using Nat.mul_le_mul_right Q hW)
  have hBank : W*Q ≤ 3*(exceptionalPhaseBankSize r (2*s) p) := by
    change W*Q ≤ 3*(W*Q/2)
    omega
  have hR : r ≤ (2*p)*W := (Nat.lt_mul_div_succ r (by omega : 0 < 2*p)).le
  have hP : (2:ℝ)*(p:ℝ) ≤ 3*((p-1:ℕ):ℝ) := by exact_mod_cast (show 2*p ≤ 3*(p-1) by omega)
  have hS : (2:ℝ)*((s-1:ℕ):ℝ) ≤ ((2*s-1:ℕ):ℝ) := by exact_mod_cast (show 2*(s-1) ≤ 2*s-1 by omega)
  have hRQ : (r:ℝ) ≤ 3*((p-1:ℕ):ℝ)*(W:ℝ) :=
    (by exact_mod_cast hR : (r:ℝ) ≤ (2*(p:ℝ))*(W:ℝ)).trans
      (mul_le_mul_of_nonneg_right hP (Nat.cast_nonneg _))
  have hQeq : (Q:ℝ) = ((2*s-1:ℕ):ℝ)*((p-1:ℕ):ℝ) := Nat.cast_mul _ _
  have hBankR : (W:ℝ)*(Q:ℝ) ≤ 3*(exceptionalPhaseBankSize r (2*s) p:ℝ) := by exact_mod_cast hBank
  calc
    _ = (r:ℝ)*(2*((s-1:ℕ):ℝ)) := by ring
    _ ≤ (3*((p-1:ℕ):ℝ)*(W:ℝ))*((2*s-1:ℕ):ℝ) :=
      mul_le_mul hRQ hS (by positivity) (by positivity)
    _ = 3*((W:ℝ)*(Q:ℝ)) := by rw [hQeq]; ring
    _ ≤ _ := by linarith only [hBankR]

/-- With the actual reduced floor, the ratio of the number of half
requests to the bank size is bounded independently of the number
of primary clusters. -/
theorem core_exception_clipping_ratio
    (r s p K : ℕ) (a α β γ : ℝ)
    (hs : 2 ≤ s) (hp : 3 ≤ p) (hK : 0 < K)
    (hα : 0 < α) (ha : α ≤ a) (hβ : 0 < β) (hβSmall : β ≤ α/4) (hγ : γ ≤ α/4)
    (hr : r = ⌊(a-γ)*(K:ℝ)/β⌋₊) :
    ((K:ℝ)*((s-1:ℕ):ℝ))/(exceptionalPhaseBankSize r (2*s) p:ℝ) ≤ 9*β/α := by
  let k := exceptionalPhaseBankSize r (2*s) p
  have hk : (0:ℝ) < k := by exact_mod_cast exceptionalPhaseBankSize_pos (show 2 ≤ 2*s by omega) hp
  have hKR : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  have hFloor := (div_lt_iff₀ hβ).mp (Nat.lt_floor_add_one ((a-γ)*(K:ℝ)/β))
  rw [←hr] at hFloor
  have hβK := hβSmall.trans (le_mul_of_one_le_right (by positivity : 0 ≤ α/4) hKR)
  have hMain := mul_le_mul_of_nonneg_right (show 3*α/4 ≤ a-γ by linarith only [ha,hγ]) (Nat.cast_nonneg (α := ℝ) K)
  have hR : (α/2)*(K:ℝ) ≤ (r:ℝ)*β := by nlinarith only [hFloor,hβK,hMain]
  have hBank := exceptionalPhaseBankSize_lower r s p hs hp
  have h₁ := mul_le_mul_of_nonneg_right hR (show 0 ≤ 2*((s-1:ℕ):ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hBank hβ.le
  have hProduct : ((K:ℝ)*((s-1:ℕ):ℝ))*α ≤ (9*β)*(k:ℝ) := by
    change _ ≤ 9*(k:ℝ)*β at h₂
    nlinarith only [h₁,h₂]
  calc
    _ ≤ ((9*β)*(k:ℝ)/α)/(k:ℝ) := by
      apply div_le_div_of_nonneg_right _ hk.le
      exact (le_div_iff₀ hα).mpr hProduct
    _ = _ := by field_simp

/-- The core loss of §5.6 consists of the additive splitting errors and
the clipped share of the geometric loss. The latter only requires
smallness relative to the primary cell size. -/
theorem core_exception_clipping_budget (r s p K m loss : ℕ) (a α β γ ε n split : ℝ)
    (hs : 2 ≤ s) (hp : 3 ≤ p) (hK : 0 < K)
    (hα : 0 < α) (ha : α ≤ a) (hβ : 0 < β) (hβSmall : β ≤ α/4) (hγ : γ ≤ α/4)
    (hr : r = ⌊(a-γ)*(K:ℝ)/β⌋₊)
    (hSplit : (K:ℝ)*((s-1:ℕ):ℝ)*(split*n) ≤ ε*(β*(m:ℝ)))
    (hLoss : 9*((loss+1:ℕ):ℝ) ≤ ε*α*(m:ℝ)) :
    (K:ℝ)*((s-1:ℕ):ℝ)*(split*n+((loss+1:ℕ):ℝ)/(exceptionalPhaseBankSize r (2*s) p:ℝ)) ≤
      ε*(β*((2*m:ℕ):ℝ)) := by
  let k := exceptionalPhaseBankSize r (2*s) p
  have hRatio := core_exception_clipping_ratio r s p K a α β γ hs hp hK hα ha hβ hβSmall hγ hr
  have hClip : (9*β/α)*((loss+1:ℕ):ℝ) ≤ ε*(β*(m:ℝ)) := by
    apply (mul_le_mul_iff_of_pos_right hα).mp
    have hEq : (9*β/α)*((loss+1:ℕ):ℝ)*α = 9*((loss+1:ℕ):ℝ)*β := by field_simp
    rw [hEq]
    nlinarith only [mul_le_mul_of_nonneg_right hLoss hβ.le]
  change (K:ℝ)*((s-1:ℕ):ℝ)*(split*n+((loss+1:ℕ):ℝ)/(k:ℝ)) ≤ _
  have hShare :
      ((K:ℝ)*((s-1:ℕ):ℝ))*(((loss+1:ℕ):ℝ)/(k:ℝ)) ≤ ε*(β*(m:ℝ)) := by
    calc
      _ = (((K:ℝ)*((s-1:ℕ):ℝ))/(k:ℝ))*((loss+1:ℕ):ℝ) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hRatio (Nat.cast_nonneg _)).trans hClip
  rw [Nat.cast_mul,Nat.cast_ofNat]
  linarith only [hSplit,hShare]

end OverfullWork.DirectedRobustExpansion
