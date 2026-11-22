module

public import OverfullWork.OsthusStadenCoreClippingBudget

@[expose] public section


/-! Choose the core splitting tolerance after the cluster bound and
pay its ordinary load using the same bank as in §5.6. -/
namespace OverfullWork.DirectedRobustExpansion

/-- A single tolerance pays the core splitting error and its share of
the ordinary red cap on every sufficiently large physical host. -/
theorem exists_osthus_staden_core_split_budget
    (Vmax : ℕ) (β tolerance load : ℝ)
    (hβ : 0 < β) (hTolerance : 0 < tolerance) (hLoad : 0 < load) :
    ∃ split : ℝ, 0 < split ∧ ∀ (m volume n : ℝ),
      0 ≤ m → 0 ≤ volume → volume ≤ (Vmax:ℝ) → n ≤ 4*(Vmax:ℝ)*m →
      volume*(split*n) ≤ tolerance*(β*m) ∧ split*n ≤ load*m/2 := by
  let V := (Vmax:ℝ)+1
  let a := tolerance*β/(4*V^2)
  let b := load/(8*V)
  let split := min a b
  have hV : 0 < V := by dsimp only [V]; positivity
  have hSplit : 0 < split := lt_min (by dsimp only [a]; positivity) (by dsimp only [b]; positivity)
  refine ⟨split,hSplit,?_⟩
  intro m volume n hm hv hvmax hn
  have hMax : (Vmax:ℝ) ≤ V := by dsimp only [V]; linarith
  have hn' : n ≤ 4*V*m := hn.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMax (by norm_num)) hm)
  have hErr : split*n ≤ a*(4*V*m) :=
    (mul_le_mul_of_nonneg_left hn' hSplit.le).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  constructor
  · calc
      _ ≤ volume*(a*(4*V*m)) := mul_le_mul_of_nonneg_left hErr hv
      _ ≤ V*(a*(4*V*m)) := mul_le_mul_of_nonneg_right (hvmax.trans hMax) (by dsimp only [a]; positivity)
      _ = _ := by dsimp only [a]; field_simp
  · calc
      _ ≤ split*(4*V*m) := mul_le_mul_of_nonneg_left hn' hSplit.le
      _ ≤ b*(4*V*m) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = _ := by dsimp only [b]; field_simp <;> ring

/-- The ordinary load of core arcs is bounded independently of the
number of primary clusters. The bank size grows with that number, so
the upper bound only requires a small relative exceptional population. -/
theorem osthus_staden_core_cap_from_primary_sizes
    (r K s p m n z : ℕ) (a α β γ exc split load : ℝ)
    (hs : 2 ≤ s) (hp : 3 ≤ p) (hK : 0 < K)
    (hα : 0 < α) (ha : α ≤ a) (hβ : 0 < β) (hβSmall : β ≤ α/4) (hγ : γ ≤ α/4)
    (hExc : 0 ≤ exc) (hr : r = ⌊(a-γ)*(K:ℝ)/β⌋₊)
    (hSize : (n:ℝ) ≤ 2*((((2*s)*p*K:ℕ):ℝ)*((2*m:ℕ):ℝ)))
    (hZ : (z:ℝ) ≤ exc*(n:ℝ)) (hRate : 288*exc*β*(p:ℝ) ≤ α*load)
    (hSplit : split*(n:ℝ) ≤ load*(m:ℝ)/2) :
    (z:ℝ)/(exceptionalPhaseBankSize r (2*s) p:ℝ)+split*(n:ℝ) ≤ load*(m:ℝ) := by
  let k := exceptionalPhaseBankSize r (2*s) p
  have hk : (0:ℝ) < k := by exact_mod_cast exceptionalPhaseBankSize_pos (show 2 ≤ 2*s by omega) hp
  have hS : (s:ℝ) ≤ 2*((s-1:ℕ):ℝ) := by exact_mod_cast (show s ≤ 2*(s-1) by omega)
  have hRatio := core_exception_clipping_ratio r s p K a α β γ hs hp hK hα ha hβ hβSmall hγ hr
  have hVol : (n:ℝ) ≤ (16*(p:ℝ)*(m:ℝ))*((K:ℝ)*((s-1:ℕ):ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hS (show 0 ≤ 8*(K:ℝ)*(p:ℝ)*(m:ℝ) by positivity)
    push_cast at hSize
    nlinarith only [hSize,h]
  have hBefore : (z:ℝ)/(k:ℝ) ≤ load*(m:ℝ)/2 := by
    calc
      _ ≤ (exc*(n:ℝ))/(k:ℝ) := div_le_div_of_nonneg_right hZ hk.le
      _ ≤ (exc*((16*(p:ℝ)*(m:ℝ))*((K:ℝ)*((s-1:ℕ):ℝ))))/(k:ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hVol hExc) hk.le
      _ = (16*exc*(p:ℝ)*(m:ℝ))*(((K:ℝ)*((s-1:ℕ):ℝ))/(k:ℝ)) := by ring
      _ ≤ (16*exc*(p:ℝ)*(m:ℝ))*(9*β/α) := mul_le_mul_of_nonneg_left hRatio (by positivity)
      _ ≤ _ := by
        apply (mul_le_mul_iff_of_pos_right hα).mp
        have hEq : (16*exc*(p:ℝ)*(m:ℝ))*(9*β/α)*α =
            (288*exc*β*(p:ℝ))*(m:ℝ)/2 := by field_simp <;> ring
        rw [hEq]
        nlinarith only [mul_le_mul_of_nonneg_right hRate (Nat.cast_nonneg (α := ℝ) m)]
  exact (add_le_add hBefore hSplit).trans_eq (by ring)

end OverfullWork.DirectedRobustExpansion
