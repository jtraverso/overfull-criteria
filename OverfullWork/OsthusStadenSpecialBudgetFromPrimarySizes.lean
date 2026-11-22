module

public import OverfullWork.OsthusStadenSpecialExceptionRequestBudget

@[expose] public section


/-! Numerical bounds for the actual rounded request count in §5.7. -/
namespace OverfullWork.DirectedRobustExpansion

/-- The incidence bound exported by the primary host and the rounded
deletion count of the bridged layers give a two-sided bound for the
special bank. In particular, its size grows with the cluster count. -/
theorem osthus_staden_special_requests_from_primary_caps
    (r K s p : ℕ) (β ξ loss : ℝ)
    (hs : 4 ≤ s) (hp : 3 ≤ p) (hβ : 0 < β) (hξ : 0 < ξ) (hLoss : 0 ≤ loss)
    (hScale : 1 ≤ ξ*(K:ℝ)/β) (hFill : 4*loss ≤ ξ) (hr : (r:ℝ) ≤ (K:ℝ)/β) :
    let types := ⌈2*(2*ξ*(K:ℝ)/β)+4*loss*(r:ℝ)+1⌉₊
    let k := types*((2*s-1)*(p-1))+1
    let volume := (((2*s)*p*K:ℕ):ℝ)
    0 < k ∧ ξ*volume ≤ (k:ℝ)*β ∧ (k:ℝ)*β ≤ 8*ξ*volume := by
  let scale := ξ*(K:ℝ)/β
  let rate := 2*(2*ξ*(K:ℝ)/β)+4*loss*(r:ℝ)+1
  let types := ⌈rate⌉₊
  let k := types*((2*s-1)*(p-1))+1
  let volume := (((2*s)*p*K:ℕ):ℝ)
  change 0 < k ∧ ξ*volume ≤ (k:ℝ)*β ∧ (k:ℝ)*β ≤ 8*ξ*volume
  have hRate : rate = 4*scale+4*loss*(r:ℝ)+1 := by dsimp only [rate,scale]; ring
  have hTlo : 4*scale ≤ (types:ℝ) := by
    refine (show 4*scale ≤ rate from ?_).trans (Nat.le_ceil rate)
    rw [hRate]
    linarith only [mul_nonneg (show 0 ≤ 4*loss by positivity) (Nat.cast_nonneg (α := ℝ) r)]
  have hThi : (types:ℝ) ≤ 7*scale := by
    have hFill' : 4*loss*(r:ℝ) ≤ scale := by
      exact (mul_le_mul hFill hr (Nat.cast_nonneg _) hξ.le).trans_eq (by dsimp only [scale]; ring)
    refine (Nat.ceil_lt_add_one (show 0 ≤ rate by dsimp only [rate]; positivity)).le.trans ?_
    change 1 ≤ scale at hScale
    rw [hRate]
    linarith only [hFill',hScale]
  have hβscale : scale*β = ξ*(K:ℝ) := by dsimp only [scale]; exact div_mul_cancel₀ _ hβ.ne'
  have hSmall : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
  have hsSmall : (1:ℝ) ≤ ((2*s:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ 2*s by omega)
  have hProd : 1 ≤ scale*((2*s:ℕ):ℝ)*(p:ℝ) := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hScale hsSmall) hSmall
  have hSubS : (1/2)*((2*s:ℕ):ℝ) ≤ ((2*s-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ 2*s by omega),Nat.cast_one]
    have h := (show (2:ℝ) ≤ ((2*s:ℕ):ℝ) by exact_mod_cast (show 2 ≤ 2*s by omega))
    linarith only [h]
  have hSubP : (1/2)*(p:ℝ) ≤ ((p-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ p by omega),Nat.cast_one]
    have h : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (show 2 ≤ p by omega)
    linarith only [h]
  have hLo : scale*((2*s:ℕ):ℝ)*(p:ℝ) ≤ (k:ℝ) := by
    dsimp only [k]
    push_cast [Nat.cast_mul]
    have h := mul_le_mul (mul_le_mul hTlo hSubS (by positivity) (Nat.cast_nonneg _))
      hSubP (by positivity) (by positivity)
    push_cast [Nat.cast_mul] at h
    linarith only [h]
  have hHi : (k:ℝ) ≤ 8*scale*((2*s:ℕ):ℝ)*(p:ℝ) := by
    have hS : ((2*s-1:ℕ):ℝ) ≤ ((2*s:ℕ):ℝ) := by exact_mod_cast Nat.sub_le (2*s) 1
    have hP : ((p-1:ℕ):ℝ) ≤ (p:ℝ) := by exact_mod_cast Nat.sub_le p 1
    have h := mul_le_mul (mul_le_mul hThi hS (by positivity) (by positivity)) hP (by positivity) (by positivity)
    dsimp only [k]
    push_cast [Nat.cast_mul] at h hProd ⊢
    linarith only [h,hProd]
  refine ⟨by dsimp only [k]; omega,?_,?_⟩
  · calc
      _ = (scale*((2*s:ℕ):ℝ)*(p:ℝ))*β := by
        dsimp only [volume]; push_cast
        linear_combination -2*(s:ℝ)*(p:ℝ)*hβscale
      _ ≤ _ := mul_le_mul_of_nonneg_right hLo hβ.le
  · calc
      _ ≤ (8*scale*((2*s:ℕ):ℝ)*(p:ℝ))*β := mul_le_mul_of_nonneg_right hHi hβ.le
      _ = _ := by
        dsimp only [volume]; push_cast
        linear_combination 16*(s:ℝ)*(p:ℝ)*hβscale

/-- A special-vertex splitting tolerance can be chosen using just
the cluster bound, simultaneously for all eventual hosts. The same
choice pays both the lower degree and the ordinary-endpoint cap. -/
theorem exists_osthus_staden_special_split_budget
    (Vmax : ℕ) (β load : ℝ) (hβ : 0 < β) (hLoad : 0 < load) :
    ∃ split : ℝ, 0 < split ∧ ∀ (volume : ℝ), volume ≤ (Vmax:ℝ) →
      split*(2*volume) ≤ β ∧ split*(2*volume) ≤ load := by
  let split := min β load/(2*((Vmax:ℝ)+1))
  have hSplit : 0 < split := div_pos (lt_min hβ hLoad) (by positivity)
  refine ⟨split,hSplit,?_⟩
  intro volume hV
  have hPay : split*(2*volume) ≤ min β load := by
    calc
      _ ≤ split*(2*((Vmax:ℝ)+1)) := mul_le_mul_of_nonneg_left (by linarith only [hV]) hSplit.le
      _ = _ := div_mul_cancel₀ _ (by positivity)
  exact ⟨hPay.trans (min_le_left _ _),hPay.trans (min_le_right _ _)⟩

/-- Pay the special-exception supply and load bounds on every layer
using the same splitting tolerance. The exceptional-set bound is a
relative bound on the population of a layer. -/
theorem exists_osthus_staden_special_budgets_of_sizes
    (Kmax s p : ℕ) (α β γ ξ loss exc load : ℝ)
    (hs : 4 ≤ s) (hp : 3 ≤ p) (hβ : 0 < β) (hγ : 0 ≤ γ) (hξ : 0 < ξ)
    (hLoss : 0 ≤ loss) (hExc : 0 ≤ exc) (hLoad : 0 < load)
    (hFill : 4*loss ≤ ξ) (hSupply : 320*(p:ℝ)*ξ ≤ γ*α) (hCap : 2*exc*β ≤ ξ*load) :
    ∃ split : ℝ, 0 < split ∧
      ∀ (r K m n κ : ℕ) (a : ℝ), K ≤ Kmax → α ≤ a →
        1 ≤ ξ*(K:ℝ)/β → (r:ℝ) ≤ (K:ℝ)/β → (κ:ℝ) ≤ β*((2*m:ℕ):ℝ) →
        let volume := (((2*s)*p*K:ℕ):ℝ)
        let types := ⌈2*(2*ξ*(K:ℝ)/β)+4*loss*(r:ℝ)+1⌉₊
        let k := types*((2*s-1)*(p-1))+1
        volume*((2*m:ℕ):ℝ) ≤ (n:ℝ) →
        (n:ℝ) ≤ 2*volume*((2*m:ℕ):ℝ) →
        (κ:ℝ)+split*(n:ℝ) ≤ (γ*a*(n:ℝ)/(20*(p:ℝ)))/(k:ℝ) ∧
        ∀ z : ℕ, (z:ℝ) ≤ exc*(n:ℝ) →
          (z:ℝ)/(k:ℝ)+split*(n:ℝ) ≤ 4*load*(m:ℝ) := by
  obtain ⟨split,hSplit,hBudget⟩ := exists_osthus_staden_special_split_budget ((2*s)*p*Kmax) β load hβ hLoad
  refine ⟨split,hSplit,?_⟩
  intro r K m n κ a hK ha hScale hr hκ volume types k hOrd hSize
  obtain ⟨hk,hKlo,hKhi⟩ := osthus_staden_special_requests_from_primary_caps r K s p β ξ loss
    hs hp hβ hξ hLoss hScale hFill hr
  have hVol : volume ≤ ((((2*s)*p*Kmax):ℕ):ℝ) := by
    change ((((2*s)*p*K):ℕ):ℝ) ≤ ((((2*s)*p*Kmax):ℕ):ℝ)
    exact_mod_cast Nat.mul_le_mul_left ((2*s)*p) hK
  obtain ⟨hLower,hUpper⟩ := hBudget volume hVol
  have hSupply' := hSupply.trans (mul_le_mul_of_nonneg_left ha hγ)
  have hPay (z : ℕ) (hz : (z:ℝ) ≤ exc*(n:ℝ)) :=
    special_exception_split_degree_budget n (2*m) p k κ z volume ξ β γ a exc split load
      (by omega) hk hβ hξ.le hExc hSplit.le hLoad.le hOrd (by nlinarith only [hSize]) hKlo hKhi
      hSupply' hκ hz hCap hLower hUpper
  refine ⟨(hPay 0 (by push_cast; positivity)).1,?_⟩
  intro z hz
  have h := (hPay z hz).2
  push_cast at h
  nlinarith only [h]

end OverfullWork.DirectedRobustExpansion
