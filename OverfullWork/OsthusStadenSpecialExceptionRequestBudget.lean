module

public import OverfullWork.OsthusStadenSpecialExceptionBudget

@[expose] public section


/-! Keep the request denominator within the margins required in §5.7. -/
namespace OverfullWork.DirectedRobustExpansion

/-- Pad the type budget to give both a lower and an upper bound for the
number used to divide up the available arcs in Claim 5.4. The scale
is ξ times the number of primary clusters, divided by the copy density. -/
theorem exists_special_exception_request_budget (r s p : ℕ) (loss atypical scale : ℝ)
    (hs : 4 ≤ s) (hp : 3 ≤ p) (hLoss : 0 ≤ loss) (hAtypical : 0 ≤ atypical) (hScale : 2 ≤ scale)
    (hBad : atypical ≤ (3/2)*scale) (hFill : 4*loss*(r:ℝ) ≤ scale) :
    ∃ fillCap typeCap : ℕ, 0 < fillCap ∧ 4*loss*(r:ℝ) ≤ (fillCap:ℝ) ∧
      2*atypical+(fillCap:ℝ) ≤ (typeCap:ℝ) ∧
      let request := typeCap*((s-1)*(p-1))+1
      scale*(s:ℝ)*(p:ℝ) ≤ (request:ℝ) ∧ (request:ℝ) ≤ 8*scale*(s:ℝ)*(p:ℝ) := by
  obtain ⟨fillCap,raw,hPos,hFillLo,hRawLo,hRawHi⟩ := exists_special_exception_type_caps r loss atypical hLoss hAtypical
  let typeCap := max raw ⌈2*scale⌉₊
  have htLo : 2*scale ≤ (typeCap:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right raw ⌈2*scale⌉₊)
  have htHi : (typeCap:ℝ) ≤ 5*scale := by
    rw [Nat.cast_max]
    have hc := (Nat.ceil_lt_add_one (show 0 ≤ 2*scale by linarith only [hScale])).le
    exact max_le (by linarith only [hRawHi,hBad,hFill,hScale]) (by linarith only [hc,hScale])
  refine ⟨fillCap,typeCap,hPos,hFillLo,hRawLo.trans (by exact_mod_cast le_max_left raw ⌈2*scale⌉₊),?_⟩
  intro request
  have hsR : 4 ≤ (s:ℝ) := by exact_mod_cast hs
  have hpR : 3 ≤ (p:ℝ) := by exact_mod_cast hp
  have hsSub : (3/4)*(s:ℝ) ≤ ((s-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ s by omega),Nat.cast_one]
    linarith only [hsR]
  have hpSub : (2/3)*(p:ℝ) ≤ ((p-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ p by omega),Nat.cast_one]
    linarith only [hpR]
  have hCoeff := mul_le_mul hsSub hpSub (by positivity) (Nat.cast_nonneg (s-1) : (0:ℝ) ≤ _)
  have hCoeffHi : (((s-1)*(p-1):ℕ):ℝ) ≤ (s:ℝ)*(p:ℝ) := by
    exact_mod_cast Nat.mul_le_mul (Nat.sub_le s 1) (Nat.sub_le p 1)
  have hRoom : 1 ≤ scale*(s:ℝ)*(p:ℝ) := by
    have hsp : 1 ≤ (s:ℝ)*(p:ℝ) := one_le_mul_of_one_le_of_one_le (by linarith only [hsR]) (by linarith only [hpR])
    rw [mul_assoc]
    exact one_le_mul_of_one_le_of_one_le (by linarith only [hScale]) hsp
  dsimp only [request]
  push_cast
  constructor
  · calc
      _ = (2*scale)*((3/4*(s:ℝ))*(2/3*(p:ℝ))) := by ring
      _ ≤ (typeCap:ℝ)*(((s-1:ℕ):ℝ)*((p-1:ℕ):ℝ)) := mul_le_mul htLo hCoeff (by positivity) (Nat.cast_nonneg _)
      _ ≤ _ := by linarith
  · have h := mul_le_mul htHi (show ((s-1:ℕ):ℝ)*((p-1:ℕ):ℝ) ≤ (s:ℝ)*(p:ℝ) by
      simpa only [Nat.cast_mul] using hCoeffHi) (by positivity) (show 0 ≤ 5*scale by linarith only [hScale])
    linarith only [h,hRoom]

end OverfullWork.DirectedRobustExpansion
