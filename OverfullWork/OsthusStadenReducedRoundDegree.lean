module

public import OverfullWork.OsthusStadenReducedBudgets

@[expose] public section


/-! Round the target degree of the reduced multidigraph in (7).
The floor error shares the remaining tolerance in the demands for
Osthus–Staden Lemma 4.1. -/
namespace OverfullWork.DirectedRegularPairs

/-- The same rounded target works for all reduced semidegrees within
the common weighted error. In particular each degree deficit is
nonnegative and lies in the normalized interval for Lemma 4.1. -/
theorem osthus_staden_rounded_reduced_degree (n : ℕ) (α β γ δ ε : ℝ)
    (hβ : 0 < β) (hγ : 0 < γ) (hαγ : γ ≤ α) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hLoss : δ ≤ ε*γ/2) (hRound : β ≤ (ε*γ/2)*(n:ℝ)) :
    let k := ⌊(α-γ)*(n:ℝ)/β⌋₊
    ∀ p : ℕ, (α-δ)*(n:ℝ) ≤ β*(p:ℝ) → β*(p:ℝ) ≤ (α+δ)*(n:ℝ) →
      k ≤ p ∧ (1-ε)*(γ/β)*(n:ℝ) ≤ ((p-k:ℕ):ℝ) ∧
        ((p-k:ℕ):ℝ) ≤ (1+ε)*(γ/β)*(n:ℝ) := by
  intro k p hLower hUpper
  have hN : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hCenter : 0 ≤ (α-γ)*(n:ℝ)/β := div_nonneg (mul_nonneg (sub_nonneg.mpr hαγ) hN) hβ.le
  have hkHi := mul_le_mul_of_nonneg_right (Nat.floor_le hCenter) hβ.le
  have hkLo := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one ((α-γ)*(n:ℝ)/β)) hβ
  change (k:ℝ)*β ≤ _ at hkHi
  change _ < ((k:ℝ)+1)*β at hkLo
  rw [div_mul_cancel₀ _ hβ.ne'] at hkHi hkLo
  have hLoss' : δ ≤ γ := by
    linarith only [hLoss,mul_le_of_le_one_left hγ.le hε₁,hγ]
  have hK : k ≤ p := by
    have h := mul_le_mul_of_nonneg_right hLoss' hN
    have hp : (k:ℝ)*β ≤ (p:ℝ)*β := by linarith only [hkHi,hLower,h]
    exact_mod_cast (mul_le_mul_iff_of_pos_right hβ).mp hp
  have hBudget := mul_le_mul_of_nonneg_right hLoss hN
  have hεγ : 0 ≤ ε*γ*(n:ℝ) := by positivity
  refine ⟨hK,?_,?_⟩
  · apply (mul_le_mul_iff_of_pos_right hβ).mp
    rw [Nat.cast_sub hK]
    have hEq : ((1-ε)*(γ/β)*(n:ℝ))*β = (1-ε)*γ*(n:ℝ) := by
      rw [show (1-ε)*(γ/β)*(n:ℝ)*β = (1-ε)*(n:ℝ)*(γ/β*β) by ring,div_mul_cancel₀ _ hβ.ne']
      ring
    rw [hEq]
    linarith only [hLower,hkHi,hBudget,hεγ]
  · apply (mul_le_mul_iff_of_pos_right hβ).mp
    rw [Nat.cast_sub hK]
    have hEq : ((1+ε)*(γ/β)*(n:ℝ))*β = (1+ε)*γ*(n:ℝ) := by
      rw [show (1+ε)*(γ/β)*(n:ℝ)*β = (1+ε)*(n:ℝ)*(γ/β*β) by ring,div_mul_cancel₀ _ hβ.ne']
      ring
    rw [hEq]
    linarith only [hUpper,hkLo,hBudget,hRound]

end OverfullWork.DirectedRegularPairs
