module

public import OverfullWork.CanonicalDynamicBudget

@[expose] public section


/-! # Nonvacuous margins for the dynamic forbidden and deletion bounds

For fixed positive expansion rate gamma and a fixed route-length cap,
choose a positive seed-error rate delta before the graph. Large order
then pays the integer residue cutoff, both dynamic losses and the
backtracking predecessor reserve. This does not choose the graph layers.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open Finset
open scoped Classical
set_option maxHeartbeats 24000000

theorem exists_dynamic_budget_margins (γ : ℝ) (hγ : 0 < γ) (ell : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∀ A0 : ℝ, 0 ≤ A0 → A0 ≤ δ*(m:ℝ) →
      ∃ h : ℕ, 0 < h ∧ 5*A0 ≤ (h:ℝ) ∧
        ((ell:ℝ)+1)*(6*A0+2)+6*(T:ℝ)+8+
          4*A0*(5+(ell:ℝ)*((m:ℝ)+1))/(h:ℝ) ≤ γ*(m:ℝ)/8 ∧
        2+(Nat.ceil (6*A0):ℝ)+(h:ℝ) ≤ γ*(m:ℝ)/8 ∧
        4+2*(ell:ℝ) < γ*(m:ℝ)-(2+(Nat.ceil (6*A0):ℝ)+(h:ℝ)) := by
  let κ : ℝ := γ/64
  have hκ : 0 < κ := by dsimp only [κ];positivity
  let δ := min (κ/12) (min (γ/(192*((ell:ℝ)+1))) (γ*κ/(64*(5+2*(ell:ℝ)))))
  have hδ : 0 < δ := by dsimp only [δ];apply lt_min <;> positivity
  have hδκ : δ ≤ κ/12 := min_le_left _ _
  have hδell : δ ≤ γ/(192*((ell:ℝ)+1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hδpoly : δ ≤ γ*κ/(64*(5+2*(ell:ℝ))) := (min_le_right _ _).trans (min_le_right _ _)
  have hCoeff : 192*((ell:ℝ)+1)*δ ≤ γ := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 192*((ell:ℝ)+1))).mp hδell
    nlinarith only [hh]
  have hPoly : 64*(5+2*(ell:ℝ))*δ ≤ γ*κ := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 64*(5+2*(ell:ℝ)))).mp hδpoly
    nlinarith only [hh]
  refine ⟨δ,hδ,?_⟩
  intro T
  let C : ℝ := 2*((ell:ℝ)+1)+6*(T:ℝ)+8
  obtain ⟨N,hN⟩ := exists_nat_gt (max (1:ℝ) (32*C/γ))
  refine ⟨N,?_⟩
  intro m hm A0 hA0 hSmall
  have hmR : (N:ℝ) ≤ m := by exact_mod_cast hm
  have hmOne : (1:ℝ) ≤ m := (le_max_left _ _).trans hN.le |>.trans hmR
  have hOrder : 32*C ≤ γ*(m:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp ((le_max_right _ _).trans_lt hN)
    nlinarith only [hh,hmR,hγ]
  let h := Nat.ceil (κ*(m:ℝ))
  have hLower : κ*(m:ℝ) ≤ (h:ℝ) := Nat.le_ceil _
  have hUpper : (h:ℝ) < κ*(m:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have hPosR : (0:ℝ) < h := by nlinarith only [hκ,hmOne,hLower]
  have hPos : 0 < h := by exact_mod_cast hPosR
  have hDeltaM := mul_le_mul_of_nonneg_right hδκ (show (0:ℝ) ≤ m by positivity)
  have hCap : 5*A0 ≤ (h:ℝ) := by nlinarith only [hSmall,hDeltaM,hLower,hA0]
  have hCoeffM := mul_le_mul_of_nonneg_right hCoeff (show (0:ℝ) ≤ m by positivity)
  have hSmallCoeff := mul_le_mul_of_nonneg_left hSmall (show (0:ℝ) ≤ 6*((ell:ℝ)+1) by positivity)
  have hBase : ((ell:ℝ)+1)*(6*A0+2)+6*(T:ℝ)+8 ≤ γ*(m:ℝ)/16 := by
    dsimp only [C] at hOrder
    nlinarith only [hCoeffM,hSmallCoeff,hOrder]
  have hK : 5+(ell:ℝ)*((m:ℝ)+1) ≤ (5+2*(ell:ℝ))*(m:ℝ) := by
    have hmEll := mul_le_mul_of_nonneg_left hmOne (Nat.cast_nonneg ell : (0:ℝ) ≤ ell)
    nlinarith only [hmOne,hmEll]
  have hNum := mul_le_mul hSmall hK (by positivity : (0:ℝ) ≤ 5+(ell:ℝ)*((m:ℝ)+1))
    (show (0:ℝ) ≤ δ*(m:ℝ) by positivity)
  have hPolyM := mul_le_mul_of_nonneg_right hPoly (sq_nonneg (m:ℝ))
  have hDen := mul_le_mul_of_nonneg_right hLower (show (0:ℝ) ≤ γ*(m:ℝ) by positivity)
  have hFraction : 4*A0*(5+(ell:ℝ)*((m:ℝ)+1))/(h:ℝ) ≤ γ*(m:ℝ)/16 := by
    apply (div_le_iff₀ hPosR).mpr
    nlinarith only [hNum,hPolyM,hDen]
  have hMissingCeil : (Nat.ceil (6*A0):ℝ) < 6*A0+1 := Nat.ceil_lt_add_one (by positivity)
  have hDeleted : 2+(Nat.ceil (6*A0):ℝ)+(h:ℝ) ≤ γ*(m:ℝ)/8 := by
    dsimp only [C] at hOrder
    dsimp only [κ] at hUpper hDeltaM
    have hT0 : (0:ℝ) ≤ T := Nat.cast_nonneg _
    have hEll0 : (0:ℝ) ≤ ell := Nat.cast_nonneg _
    nlinarith only [hMissingCeil,hUpper,hDeltaM,hSmall,hOrder,hT0,hEll0]
  refine ⟨h,hPos,hCap,by linarith only [hBase,hFraction],hDeleted,?_⟩
  dsimp only [C] at hOrder
  have hT0 : (0:ℝ) ≤ T := Nat.cast_nonneg _
  nlinarith only [hDeleted,hOrder,hT0]

end OverfullWork.NormalizedCanonicalCandidate
