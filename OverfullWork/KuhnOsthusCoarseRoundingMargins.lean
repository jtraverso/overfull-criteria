module

public import OverfullWork.KuhnOsthusOrderedCoarsePartition

@[expose] public section


/-! Sizes and exceptional losses when rounding the coarse partition
in the opening of the proof of Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion

/-- A sufficiently large host pays for rounding every coarse cluster
and keeps its wound cells above any fixed threshold. The loss from
rounding the label count is controlled before the host is chosen. -/
theorem exists_kuhn_osthus_coarse_rounding_margins (b ℓ kMax M : ℕ) (ε ζ : ℝ)
    (hb : 0 < b) (hℓ : 0 < ℓ) (hMax : 0 < kMax)
    (hε : ε ≤ 1/2) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) :
    ∃ N : ℕ, ∀ n z k m : ℕ, N ≤ n → k ≤ kMax → n = z+m*k →
      (z:ℝ) ≤ ε*(n:ℝ) → 4*((b-1:ℕ):ℝ) ≤ ζ*(k:ℝ) →
      2*(ℓ-1) ≤ m ∧ M ≤ m/ℓ ∧
      ((z+m*(k%b)+(m%ℓ)*((k/b)*b):ℕ):ℝ) ≤ (ε+ζ/2)*(n:ℝ) := by
  let T := max (ℓ*M) ⌈4*((ℓ-1:ℕ):ℝ)/ζ⌉₊
  refine ⟨2*kMax*T,?_⟩
  intro n z k m hN hk hOrder hZ hLabels
  have hVol : ((m*k:ℕ):ℝ) ≤ n := by exact_mod_cast (show m*k ≤ n by omega)
  have hHalf : n ≤ 2*(m*k) := by
    have hOrder' : (n:ℝ) = (z:ℝ)+((m*k:ℕ):ℝ) := by exact_mod_cast hOrder
    have h := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg n)
    exact_mod_cast (show (n:ℝ) ≤ 2*((m*k:ℕ):ℝ) by linarith only [hOrder',hZ,h])
  have hBound : 2*(m*k) ≤ 2*kMax*m := calc
    _ ≤ 2*(m*kMax) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hk)
    _ = _ := by ring
  have hM : T ≤ m := Nat.le_of_mul_le_mul_left (hN.trans (hHalf.trans hBound))
    (by positivity : 0 < 2*kMax)
  have hCut : 4*((ℓ-1:ℕ):ℝ)/ζ ≤ (m:ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈4*((ℓ-1:ℕ):ℝ)/ζ⌉₊ ≤ m from (le_max_right _ _).trans hM))
  have hCell := (div_le_iff₀ hζ).mp hCut
  have hRoom : 2*(ℓ-1) ≤ m := by
    exact_mod_cast (show (2:ℝ)*((ℓ-1:ℕ):ℝ) ≤ m by
      linarith only [hCell,mul_le_of_le_one_left (Nat.cast_nonneg m : (0:ℝ) ≤ m) hζ₁,Nat.cast_nonneg (α := ℝ) (ℓ-1)])
  refine ⟨hRoom,(Nat.le_div_iff_mul_le hℓ).mpr (by rw [mul_comm]; exact (le_max_left _ _).trans hM),?_⟩
  have hb' : ((k%b:ℕ):ℝ) ≤ ((b-1:ℕ):ℝ) := by exact_mod_cast Nat.le_pred_of_lt (Nat.mod_lt k hb)
  have hℓ' : ((m%ℓ:ℕ):ℝ) ≤ ((ℓ-1:ℕ):ℝ) := by exact_mod_cast Nat.le_pred_of_lt (Nat.mod_lt m hℓ)
  have hk' : (((k/b)*b:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.div_mul_le_self k b
  have hA := mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg m)
  have hA' := mul_le_mul_of_nonneg_right hLabels (Nat.cast_nonneg m)
  have hB := mul_le_mul hℓ' hk' (by positivity) (by positivity)
  have hB' := mul_le_mul_of_nonneg_right hCell (Nat.cast_nonneg k)
  have hC := mul_le_mul_of_nonneg_left hVol hζ.le
  push_cast at hB hC ⊢
  linarith only [hZ,hA,hA',hB,hB',hC]

end OverfullWork.DirectedRobustExpansion
