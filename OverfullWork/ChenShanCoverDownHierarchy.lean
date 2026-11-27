module

public import OverfullWork.ChenShanCoverDownAllLevels
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

/-- A single list of inequalities independent of the level and of the
particular prefixes. The size requirements are enforced by one cutoff. -/
structure CoverDownScalarBounds (ρ η η₀ μ ζ δ ξ cap : ℝ) : Prop where
  densityCost : 18*δ ≤ η*ρ
  probWindow : (8/η)*(16*δ/ρ) ≤ η₀/100
  discrepancy : ξ ≤ η₀*(μ*ρ)/2
  baseDegree : δ+4*ρ+10*μ ≤ η/2
  colorDegree : δ+4*ρ+10*μ ≤ 1/16
  repairSmall : Real.sqrt (4*ξ) ≤ min ((η/2)/32) (1/128)
  repairDensity : δ+4*ρ+10*μ+5*Real.sqrt (4*ξ) ≤ cap
  repairBudget : 5*Real.sqrt (4*ξ) ≤ ζ/2
  matchingCost : 120000*μ^(3/2:ℝ) ≤ η₀*μ*ρ/8
  reservePart : ζ ≤ μ*ρ/8
  exteriorCost : 2*ζ < μ^2*ρ/20
  loadCost : ζ ≤ 10*μ
  protection : 36*μ*ρ^2+ξ+(3/2+η₀)*ζ ≤ 7*η₀*(μ*ρ/4)

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- The protected target class has order at most twelve times (ρ²n),
including the rounded color class. -/
theorem cover_down_protected_part_card
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i+1 ≤ l)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hLower : 1/2 ≤ (k:ℝ)/m) (hUpper : (k:ℝ)/m ≤ 3/2)
    (hn : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ)) (hs : 6 ≤ ρ*(nestedCoreSize ρ m (i+1) : ℝ))
    (c : Fin 3) :
    ((protectedCrossingPart S i c).card : ℝ) ≤ 12*ρ^2*nestedCoreSize ρ m i := by
  have hρn : 0 ≤ ρ*(nestedCoreSize ρ m i : ℝ) := by positivity
  by_cases hl : i+2 ≤ l
  · rw [protectedCrossingPart,ite_eq_left hl]
    obtain ⟨_,_,hN,_⟩ := cover_down_inner_order S i hi hρ hρsmall hUpper hn
    have hS : (nestedCoreSize ρ m (i+1) : ℝ) ≤ 4*ρ*nestedCoreSize ρ m i :=
      (show (nestedCoreSize ρ m (i+1) : ℝ) ≤
        (max (nestedCoreSize ρ m (i+1)) (S.colors (i+1)).card : ℕ) by
          exact_mod_cast le_max_left (nestedCoreSize ρ m (i+1)) (S.colors (i+1)).card).trans hN
    have hW : ((S.colors (i+1)).card : ℝ) ≤ 4*ρ*nestedCoreSize ρ m i :=
      (show ((S.colors (i+1)).card : ℝ) ≤
        (max (nestedCoreSize ρ m (i+1)) (S.colors (i+1)).card : ℕ) by
          exact_mod_cast le_max_right (nestedCoreSize ρ m (i+1)) (S.colors (i+1)).card).trans hN
    have ⟨ha,hb,hw⟩ := protected_prefix_class_sizes S i hl hρ hρsmall hs hLower hUpper
    fin_cases c
    · have heq := card_prefixPart_filter_left S (i+2) (fun _ => True) (fun _ => True) (by simp)
      simp only [filter_true] at heq
      change ((prefixPartVertices S (i+2) 0).card : ℝ) ≤ _
      rw [heq]
      rw [S.leftSize _ hi] at ha
      have hh := mul_le_mul_of_nonneg_left hS (show 0 ≤ 3*ρ by positivity)
      linarith only [ha,hh]
    · have heq := card_prefixPart_filter_right S (i+2) (fun _ => True) (fun _ => True) (by simp)
      simp only [filter_true] at heq
      change ((prefixPartVertices S (i+2) 1).card : ℝ) ≤ _
      rw [heq]
      rw [S.rightSize _ hi] at hb
      have hh := mul_le_mul_of_nonneg_left hS (show 0 ≤ 3*ρ by positivity)
      linarith only [hb,hh]
    · have heq := card_prefixPart_filter_color S (i+2) (fun _ => True) (fun _ => True) (by simp)
      simp only [filter_true] at heq
      change ((prefixPartVertices S (i+2) 2).card : ℝ) ≤ _
      rw [heq]
      have hh := mul_le_mul_of_nonneg_left hW (show 0 ≤ 3*ρ by positivity)
      linarith only [hw,hh]
  · rw [protectedCrossingPart,ite_eq_right hl,card_empty,Nat.cast_zero]
    positivity

/-- One cutoff on the retained core sizes supplies every numerical
obligation of each round from the scalar inequalities. -/
theorem cover_down_levels_of_scalar_bounds_uniform
    {η η₀ μ ζ δmin ξ cap : ℝ} (n₀ N₀ : ℕ)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4) (hη : 0 < η)
    (hμ : 0 ≤ μ) (hδ : 0 < δmin) (hξ : 0 < ξ) :
    ∃ cutoff : ℕ, ∀ δ : ℝ, δmin ≤ δ → CoverDownScalarBounds ρ η η₀ μ ζ δ ξ cap →
      ∀ (A B W : Type u) [Fintype A] [Fintype B] [Fintype W] (m k l : ℕ),
      ∀ (S : NestedTripartitePrefixes A B W ρ m k l),
      (∀ i ≤ l, cutoff ≤ nestedCoreSize ρ m i) →
      1/2 ≤ (k:ℝ)/m → (k:ℝ)/m ≤ 3/2 →
      ∀ i < l, CoverDownLevelBounds S i n₀ N₀ η η₀ μ ζ δ ξ cap := by
  let T := 5184/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3
  obtain ⟨b,hb⟩ := exists_nat_gt (max T (max (6/ρ) (max (1/δmin) (max (1/η) (1/ξ)))))
  refine ⟨max (max n₀ N₀) (max b 1),?_⟩
  intro δ hδle h A B W _ _ _ m k l S hSize hLower hUpper i hi
  have hi' : i+1 ≤ l := by omega
  let n := nestedCoreSize ρ m i
  let s := nestedCoreSize ρ m (i+1)
  have hn := hSize i (by omega)
  have hs := hSize (i+1) hi'
  have hbN : (b:ℝ) ≤ n := by
    exact_mod_cast (le_max_left b 1).trans ((le_max_right _ _).trans hn)
  have hbS : (b:ℝ) ≤ s := by
    exact_mod_cast (le_max_left b 1).trans ((le_max_right _ _).trans hs)
  have hor : (6:ℝ)/ρ < b := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hb)
  have hDelta : (1:ℝ)/δmin < b := (le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hb))
  have hEta : (1:ℝ)/η < b := (le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hb)))
  have hXi : (1:ℝ)/ξ < b := (le_max_right _ _).trans_lt
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hb)))
  have hρn : 6 ≤ ρ*(n:ℝ) := by
    have hh := (div_lt_iff₀ hρ).mp (hor.trans_le hbN)
    linarith only [hh]
  have hρs : 6 ≤ ρ*(s:ℝ) := by
    have hh := (div_lt_iff₀ hρ).mp (hor.trans_le hbS)
    linarith only [hh]
  have hN₀ : 0 ≤ (n:ℝ) := by positivity
  constructor
  · exact (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  · exact (le_max_right _ _).trans ((le_max_left _ _).trans hs)
  · exact hρn
  · have hh := (div_lt_iff₀ hδ).mp (hDelta.trans_le hbN)
    have hd := mul_le_mul_of_nonneg_right hδle hN₀
    linarith only [hh,hd]
  · have hh := (div_lt_iff₀ hη).mp (hEta.trans_le hbN)
    linarith only [hh]
  · exact h.densityCost
  · exact h.probWindow
  · exact h.discrepancy
  · exact ((le_max_left _ _).trans_lt hb).trans_le hbN
  · have hh := (div_lt_iff₀ hξ).mp (hXi.trans_le hbN)
    linarith only [hh]
  · exact h.baseDegree
  · exact h.colorDegree
  · exact h.repairSmall
  · exact h.repairDensity
  · exact h.repairBudget
  · have hM := mul_le_mul_of_nonneg_right h.matchingCost hN₀
    linarith only [hM]
  · have hM := mul_le_mul_of_nonneg_right h.reservePart hN₀
    linarith only [hM]
  · have hnpos : 0 < (n:ℝ) := by
      by_contra! hle
      linarith only [hρn,mul_nonpos_of_nonneg_of_nonpos hρ.le hle]
    have hM := mul_lt_mul_of_pos_right h.exteriorCost hnpos
    linarith only [hM]
  · exact mul_le_mul_of_nonneg_right h.loadCost hN₀
  · intro c
    have hh := cover_down_protected_part_card S i hi' hρ hρsmall hLower hUpper
      (by linarith only [hρn]) hρs c
    have hScale := mul_le_mul_of_nonneg_left hh (show 0 ≤ 3*μ by positivity)
    have hP := mul_le_mul_of_nonneg_right h.protection hN₀
    linarith only [hScale,hP]

theorem cover_down_levels_of_scalar_bounds
    {η η₀ μ ζ δ ξ cap : ℝ} (n₀ N₀ : ℕ)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4) (hη : 0 < η)
    (hμ : 0 ≤ μ) (hδ : 0 < δ) (hξ : 0 < ξ)
    (h : CoverDownScalarBounds ρ η η₀ μ ζ δ ξ cap) :
    ∃ cutoff : ℕ, ∀ (S : NestedTripartitePrefixes A B W ρ m k l),
      (∀ i ≤ l, cutoff ≤ nestedCoreSize ρ m i) →
      1/2 ≤ (k:ℝ)/m → (k:ℝ)/m ≤ 3/2 →
      ∀ i < l, CoverDownLevelBounds S i n₀ N₀ η η₀ μ ζ δ ξ cap := by
  obtain ⟨cutoff,hCut⟩ := cover_down_levels_of_scalar_bounds_uniform.{u}
    n₀ N₀ hρ hρsmall hη hμ hδ hξ
  exact ⟨cutoff,hCut δ le_rfl h A B W m k l⟩

end OverfullWork.ChenShan
