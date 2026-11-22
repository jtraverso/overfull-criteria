module

public import OverfullWork.OsthusStadenDenseFactorBudget
public import OverfullWork.OsthusStadenRoundedPackMargins

@[expose] public section


/-! Choose the scales for extracting factors and reusing H3 in
Osthus–Staden §§5.10–5.11. -/
namespace OverfullWork.DirectedRobustExpansion

set_option maxHeartbeats 1600000 in
/-- The extraction and all reuse margins hold with the actual floor
for κ and the loss of one vertex per cell. The prime for the unwinding
may be chosen above the lower bound on p. -/
theorem exists_osthus_staden_closing_scales
    (γ d : ℝ) (hγ : 0 < γ) (hγSmall : γ ≤ 1/8) (hd : 0 < d) (hd₁ : d ≤ 1) :
    ∃ pMin mMin : ℕ, ∃ fraction δ₃ dMerge εMerge νMerge τMerge γMerge redLimit : ℝ,
      0 < fraction ∧ fraction ≤ 1 ∧ 0 < δ₃ ∧ δ₃ ≤ 1 ∧ 0 < dMerge ∧
      0 < εMerge ∧ 0 < νMerge ∧ εMerge+νMerge ≤ τMerge ∧
      16*τMerge ≤ γMerge ∧ γMerge ≤ 1 ∧ δ₃ ≤ εMerge ∧ dMerge ≤ fraction*d-2*δ₃ ∧ 0 < redLimit ∧
      ∀ p m : ℕ, pMin ≤ p → mMin ≤ m →
        let n := 2*m-1
        let κ := ⌊(1-γ)*d*((2*m:ℕ):ℝ)⌋₊
        ∀ redCap : ℝ, 0 ≤ redCap → redCap ≤ redLimit*(m:ℝ) →
        ∃ cutoff minDemand batch : ℕ,
          redCap ≤ ((κ-minDemand:ℕ):ℝ) ∧
          OsthusStadenDenseFactorMargins n κ cutoff minDemand δ₃ ((1-fraction)*d) ∧
          κ ≤ (p-4)*batch ∧
          (batch:ℝ)+νMerge*(n:ℝ) ≤ dMerge*τMerge*(n:ℝ) ∧
          γMerge*(n:ℝ)+(batch:ℝ) ≤ dMerge*(n:ℝ) := by
  let fraction := γ/4
  let dMerge := fraction*d/2
  let τMerge := dMerge/64
  let εMerge := τMerge/4
  let νMerge := dMerge*τMerge/4
  let γMerge := dMerge/2
  let δ₃ := min (γ*d/128) εMerge
  let redLimit := γ*d/32
  have hFrac : 0 < fraction := by dsimp only [fraction]; positivity
  have hFrac₁ : fraction ≤ 1/4 := by dsimp only [fraction]; linarith only [hγSmall]
  have hDM : 0 < dMerge := by dsimp only [dMerge]; positivity
  have hDM₁ : dMerge ≤ 1 := by
    have h := mul_le_mul hFrac₁ hd₁ hd.le (by norm_num : (0:ℝ) ≤ 1/4)
    dsimp only [dMerge]
    linarith only [h]
  have hTM : 0 < τMerge := by dsimp only [τMerge]; positivity
  have hTM₁ : τMerge ≤ 1 := by dsimp only [τMerge]; linarith only [hDM₁]
  have hEM : 0 < εMerge := by dsimp only [εMerge]; positivity
  have hVM : 0 < νMerge := by dsimp only [νMerge]; positivity
  have hδ : 0 < δ₃ := lt_min (by positivity) hEM
  have hδM : δ₃ ≤ εMerge := min_le_right _ _
  have hδγ : δ₃ ≤ γ*d/128 := min_le_left _ _
  have hδd : δ₃ ≤ d/128 := hδγ.trans (by
    have h := mul_le_mul_of_nonneg_right (show γ ≤ 1 by linarith only [hγSmall]) hd.le
    linarith only [h])
  have hδ₁ : δ₃ ≤ 1 := by linarith only [hδd,hd₁]
  have hR : 0 < redLimit := by dsimp only [redLimit]; positivity
  have hRSmall : redLimit ≤ d/128 := by
    have h := mul_le_mul_of_nonneg_right hγSmall hd.le
    dsimp only [redLimit]
    linarith only [h,hd]
  let pMin := ⌈8*d/(dMerge*τMerge)⌉₊+5
  let threshold := max (2:ℝ) (max (64/(γ*d)) (max (64/d) (4/(dMerge*τMerge))))
  obtain ⟨mMin,hmMin⟩ := exists_nat_ge threshold
  refine ⟨pMin,mMin,fraction,δ₃,dMerge,εMerge,νMerge,τMerge,γMerge,redLimit,
    hFrac,(by linarith only [hFrac₁]),hδ,hδ₁,hDM,hEM,hVM,?_,?_,?_,hδM,?_,hR,?_⟩
  · have h := mul_le_mul_of_nonneg_right hDM₁ hTM.le
    dsimp only [εMerge,νMerge]
    linarith only [h,hTM]
  · dsimp only [γMerge,τMerge]; linarith only [hDM]
  · dsimp only [γMerge]; linarith only [hDM₁]
  · dsimp only [dMerge,fraction]
    linarith only [hδγ,mul_pos hγ hd]
  intro p m hp hm n κ redCap hCap hCapSize
  have hM : threshold ≤ (m:ℝ) := hmMin.trans (by exact_mod_cast hm)
  have hm₂ : 2 ≤ m := by exact_mod_cast ((le_max_left _ _).trans hM : (2:ℝ) ≤ (m:ℝ))
  have hp₅ : 5 ≤ p := by dsimp only [pMin] at hp; omega
  have hnM : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show m ≤ n by dsimp only [n]; omega)
  have hnEq : (((2*m:ℕ):ℝ)) = (n:ℝ)+1 := by
    exact_mod_cast (show 2*m = n+1 by dsimp only [n]; omega)
  have hnTwo : (((2*m:ℕ):ℝ)) ≤ 2*(n:ℝ) := by
    exact_mod_cast (show 2*m ≤ 2*n by dsimp only [n]; omega)
  have hNbig : 64 ≤ γ*d*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ (mul_pos hγ hd)).mp ((le_max_left _ _).trans ((le_max_right _ _).trans (hM.trans hnM)))
  have hNbig' : 64 ≤ d*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hd).mp ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (hM.trans hnM))))
  have hMergeBig : 4 ≤ dMerge*τMerge*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ (mul_pos hDM hTM)).mp ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (hM.trans hnM))))
  have hFloorUpper : (κ:ℝ) ≤ (1-γ)*d*((2*m:ℕ):ℝ) := Nat.floor_le
    (mul_nonneg (mul_nonneg (by linarith only [hγSmall]) hd.le) (Nat.cast_nonneg _))
  have hFloorLower : (1-γ)*d*((2*m:ℕ):ℝ) < (κ:ℝ)+1 := Nat.lt_floor_add_one _
  have hκUp : (κ:ℝ) ≤ (1-γ)*d*(n:ℝ)+d := by
    rw [hnEq] at hFloorUpper
    nlinarith only [hFloorUpper,mul_pos hγ hd]
  have hκWide : (κ:ℝ) ≤ 2*d*(n:ℝ) := by
    calc
      _ ≤ (1-γ)*d*((2*m:ℕ):ℝ) := hFloorUpper
      _ ≤ d*((2*m:ℕ):ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hd.le (by linarith only [hγ])) (Nat.cast_nonneg _)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hnTwo hd.le]
  let dFactor := (1-fraction)*d
  have hDlo : d/2 ≤ dFactor-2*δ₃ := by
    have h := mul_le_mul_of_nonneg_right hFrac₁ hd.le
    dsimp only [dFactor]
    nlinarith only [h,hδd,hd]
  have hDhi : dFactor-2*δ₃ ≤ d := by
    dsimp only [dFactor]
    nlinarith only [mul_pos hFrac hd,hδ]
  have hN : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hTarget : (3/4)*(dFactor-2*δ₃)*(n:ℝ) ≤ (κ:ℝ) := by
    rw [hnEq] at hFloorLower
    have h₁ := mul_le_mul_of_nonneg_right hDhi hN
    have h₂ := mul_le_mul_of_nonneg_right hγSmall (show 0 ≤ d*(n:ℝ) by positivity)
    nlinarith only [hFloorLower,hNbig',h₁,h₂,mul_nonneg (show 0 ≤ 1-γ by linarith only [hγSmall]) hd.le]
  have hRS : redCap+1 ≤ (dFactor-2*δ₃)*(n:ℝ)/12 := by
    have h₁ := mul_le_mul hRSmall hnM (Nat.cast_nonneg _) (by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hDlo hN
    nlinarith only [h₁,h₂,hNbig',hCapSize]
  have hδN := mul_le_mul_of_nonneg_right hδγ hN
  have hResolution : (κ:ℝ)+redCap+1 ≤ (dFactor-2*δ₃)*(n:ℝ) := by
    have hRate := mul_le_mul_of_nonneg_left hnM hR.le
    dsimp only [dFactor,fraction,redLimit] at *
    nlinarith only [hκUp,hNbig,hδN,hRate,hCapSize,hd₁]
  have hAvailable : (κ:ℝ)+2 ≤ (dFactor-3*δ₃)*(n:ℝ) := by
    dsimp only [dFactor,fraction] at *
    nlinarith only [hκUp,hNbig,hδN,hd₁]
  obtain ⟨cutoff,minDemand,hDense,hRound⟩ := exists_osthus_staden_dense_factor_margins
    n κ δ₃ dFactor redCap hδ.le hCap (by linarith only [hDlo,hd]) hTarget hRS hResolution hAvailable
  have hCap' : redCap ≤ ((κ-minDemand:ℕ):ℝ) := by rw [hRound]; exact Nat.le_ceil _
  have hpR : 0 < ((p-4:ℕ):ℝ) := by exact_mod_cast (show 0 < p-4 by omega)
  have hpLarge : 8*d ≤ (dMerge*τMerge)*((p-4:ℕ):ℝ) := by
    have h : ⌈8*d/(dMerge*τMerge)⌉₊ ≤ p-4 := by dsimp only [pMin] at hp; omega
    have h' : (⌈8*d/(dMerge*τMerge)⌉₊:ℝ) ≤ ((p-4:ℕ):ℝ) := by exact_mod_cast h
    simpa only [mul_comm ((p-4:ℕ):ℝ) (dMerge*τMerge)] using
      (div_le_iff₀ (mul_pos hDM hTM)).mp ((Nat.le_ceil _).trans h')
  have hReuse : (κ:ℝ)/((p-4:ℕ):ℝ) ≤ dMerge*τMerge*(n:ℝ)/4 := by
    apply (div_le_iff₀ hpR).mpr
    nlinarith only [hκWide,mul_le_mul_of_nonneg_right hpLarge hN]
  obtain ⟨batch,hBatch,hCost,hDegree⟩ := exists_osthus_staden_merge_batch_margins n κ p dMerge νMerge τMerge γMerge hp₅
    (by dsimp only [νMerge]; nlinarith only [hReuse,hMergeBig])
    (by
      have h := mul_le_mul_of_nonneg_right hTM₁ (show 0 ≤ dMerge*(n:ℝ) by positivity)
      dsimp only [γMerge]
      nlinarith only [h,hReuse,hMergeBig])
  exact ⟨cutoff,minDemand,batch,hCap',hDense,hBatch,hCost,hDegree⟩

end OverfullWork.DirectedRobustExpansion
