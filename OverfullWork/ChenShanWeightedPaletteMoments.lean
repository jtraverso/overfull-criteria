module

public import OverfullWork.ChenShanConditionalPermutation
public import OverfullWork.ChenShanUniformInclusion
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.UniformSubsetSampling

open Finset
open scoped Classical

variable {W : Type*} [Fintype W]

/-- Finite expectation for the same fixed-size sample as probability. -/
noncomputable def sampleExpectation (s : ℕ) (f : Finset W → ℝ) : ℝ :=
  (∑ X ∈ (univ : Finset W).powersetCard s, f X) / (Fintype.card W).choose s

private theorem expected_indicator_sum {J : Type*} [Fintype J] (s : ℕ)
    (event : J → Finset W → Prop) (a : J → ℝ) :
    sampleExpectation s (fun X => ∑ j, if event j X then a j else 0) =
      ∑ j, (probability s (event j))*a j := by
  let F := (univ : Finset W).powersetCard s
  change (∑ X ∈ F, ∑ j, if event j X then a j else 0)/_ = _
  rw [sum_comm,sum_div]
  apply sum_congr rfl
  intro j _
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  unfold probability
  ring

private theorem sum_mem_as_indicators (w : W → ℝ) (X : Finset W) :
    (∑ x ∈ X, w x) = ∑ x, if x ∈ X then w x else 0 := by
  rw [← sum_filter]
  congr 1
  ext x
  simp

/-- Each weight contributes with its exact marginal inclusion probability. -/
theorem expected_fixed_size_weight (s : ℕ) (hs : s ≤ Fintype.card W) (w : W → ℝ) :
    sampleExpectation s (fun X => ∑ x ∈ X, w x) =
      ((s:ℝ)/Fintype.card W) * ∑ x, w x := by
  calc
    _ = sampleExpectation s (fun X => ∑ x, if x ∈ X then w x else 0) := by
      congr 1
      funext X
      exact sum_mem_as_indicators w X
    _ = ∑ x, probability s (fun X => x ∈ X)*w x := by
      convert expected_indicator_sum s (fun x X => x ∈ X) w using 2
      funext X
      apply sum_congr rfl
      intro x _
      by_cases hx : x ∈ X <;> simp [hx]
    _ = _ := by simp_rw [probability_contains_vertex _ hs,mul_sum]

private theorem probability_same_event (s : ℕ) (P Q : Finset W → Prop)
    (h : ∀ X, P X ↔ Q X) : probability s P = probability s Q := by
  have hf : ((univ : Finset W).powersetCard s).filter P =
      ((univ : Finset W).powersetCard s).filter Q := by
    ext X
    simp [h X]
  unfold probability
  rw [hf]

private theorem pair_inclusion_bound (s : ℕ) (hs : s ≤ Fintype.card W) (x y : W) :
    let p := (s:ℝ)/Fintype.card W
    probability s (fun X => x ∈ X ∧ y ∈ X) ≤ (if x = y then p else 0)+p^2 := by
  intro p
  by_cases h : x = y
  · subst y
    rw [probability_same_event s _ (fun X => x ∈ X) (fun _ => ⟨And.left,fun h => ⟨h,h⟩⟩),
      probability_contains_vertex x hs,ite_eq_left rfl]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [ite_eq_right h,zero_add]
    have hEq : probability s (fun X => x ∈ X ∧ y ∈ X) =
        probability s (fun X => ({x,y} : Finset W) ⊆ X) :=
      probability_same_event s _ _ (fun X => by simp [insert_subset_iff])
    rw [hEq]
    have hPair : ({x,y} : Finset W).card = 2 := by simp [card_insert_of_notMem,h]
    simpa only [hPair] using probability_contains_le ({x,y} : Finset W) hs

private theorem expected_square_fixed_size_weight (s : ℕ) (w : W → ℝ) :
    sampleExpectation s (fun X => (∑ x ∈ X, w x)^2) =
      ∑ z : W × W, probability s (fun X => z.1 ∈ X ∧ z.2 ∈ X)*(w z.1*w z.2) := by
  calc
    _ = sampleExpectation s (fun X => ∑ z : W × W,
        if z.1 ∈ X ∧ z.2 ∈ X then w z.1*w z.2 else 0) := by
      congr 1
      funext X
      rw [sum_mem_as_indicators, pow_two, Fintype.sum_prod_type,sum_mul]
      apply sum_congr rfl
      intro x _
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      by_cases hx : x ∈ X <;> by_cases hy : y ∈ X <;> simp [hx,hy]
    _ = _ := by
      convert expected_indicator_sum s (fun z : W × W => fun X => z.1 ∈ X ∧ z.2 ∈ X)
        (fun z => w z.1*w z.2) using 2
      funext X
      apply sum_congr rfl
      intro z _
      by_cases hz : z.1 ∈ X ∧ z.2 ∈ X <;> simp [hz]

/-- With nonnegative weights, pairwise inclusion probabilities bound
the variance by the sampling fraction times the sum of squared weights. -/
theorem fixed_size_weight_variance_le (s : ℕ) (hs : s ≤ Fintype.card W)
    (w : W → ℝ) (hw : ∀ x, 0 ≤ w x) :
    let p := (s:ℝ)/Fintype.card W
    let Y (X : Finset W) := ∑ x ∈ X, w x
    sampleExpectation s (fun X => (Y X)^2) - (sampleExpectation s Y)^2 ≤ p*(∑ x, (w x)^2) := by
  intro p Y
  have hPair := sum_le_sum (s := (univ : Finset (W × W))) (fun z _ =>
    mul_le_mul_of_nonneg_right (pair_inclusion_bound s hs z.1 z.2) (mul_nonneg (hw z.1) (hw z.2)))
  change (∑ z : W × W, probability s (fun X => z.1 ∈ X ∧ z.2 ∈ X)*(w z.1*w z.2)) ≤
    ∑ z : W × W, ((if z.1 = z.2 then p else 0)+p^2)*(w z.1*w z.2) at hPair
  have hRhs : (∑ z : W × W, ((if z.1 = z.2 then p else 0)+p^2)*(w z.1*w z.2)) =
      p*(∑ x, (w x)^2) + (p*(∑ x, w x))^2 := by
    simp_rw [add_mul]
    rw [sum_add_distrib]
    congr 1
    · rw [Fintype.sum_prod_type,mul_sum]
      apply sum_congr rfl
      intro x _
      rw [sum_eq_single x]
      · simp [pow_two]
      · intro y _ h
        simp [h.symm]
      · simp
    · have hProd : (∑ z : W × W, w z.1*w z.2) = (∑ x, w x)^2 := by
        rw [Fintype.sum_prod_type,pow_two,sum_mul]
        exact sum_congr rfl (fun x _ => (mul_sum univ w (w x)).symm)
      rw [← mul_sum,hProd]
      ring
  rw [hRhs] at hPair
  dsimp only [Y]
  rw [expected_square_fixed_size_weight,expected_fixed_size_weight s hs]
  exact sub_le_iff_le_add.mpr hPair

private theorem expected_centered_square (s : ℕ) (hs : s ≤ Fintype.card W)
    (Y : Finset W → ℝ) (μ : ℝ) :
    sampleExpectation s (fun X => (Y X - μ)^2) =
      sampleExpectation s (fun X => (Y X)^2) - 2*μ*sampleExpectation s Y + μ^2 := by
  let F := (univ : Finset W).powersetCard s
  let n : ℝ := (Fintype.card W).choose s
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast Nat.choose_pos hs
  have hCard : (F.card:ℝ) = n := by simp [F,n,card_powersetCard]
  change (∑ X ∈ F, (Y X - μ)^2)/n =
    (∑ X ∈ F, (Y X)^2)/n - 2*μ*((∑ X ∈ F, Y X)/n) + μ^2
  have hp (X : Finset W) : (Y X-μ)^2 = (Y X)^2- (2*μ)*Y X+μ^2 := by ring
  simp only [hp,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,hCard]
  field_simp

/-- One-sided Chebyshev for the finite uniform subset model. -/
theorem sample_probability_above_mean_le (s : ℕ) (hs : s ≤ Fintype.card W)
    (Y : Finset W → ℝ) (b : ℝ) (hb : sampleExpectation s Y < b) :
    probability s (fun X => b < Y X) ≤
      (sampleExpectation s (fun X => (Y X)^2) - (sampleExpectation s Y)^2) /
        (b - sampleExpectation s Y)^2 := by
  let μ := sampleExpectation s Y
  let F := (univ : Finset W).powersetCard s
  let n : ℝ := (Fintype.card W).choose s
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast Nat.choose_pos hs
  have hb' : 0 < b - μ := sub_pos.mpr hb
  have hInd :
      sampleExpectation s (fun X => if b < Y X then (b-μ)^2 else 0) =
        probability s (fun X => b < Y X) * (b-μ)^2 := by
    have h := expected_indicator_sum (J := Unit) s (fun _ X => b < Y X) (fun _ => (b-μ)^2)
    simpa only [Fintype.sum_unique] using h
  have hCompare :
      sampleExpectation s (fun X => if b < Y X then (b-μ)^2 else 0) ≤
        sampleExpectation s (fun X => (Y X-μ)^2) := by
    apply div_le_div_of_nonneg_right _ hn.le
    apply sum_le_sum
    intro X _
    by_cases hh : b < Y X
    · rw [ite_eq_left hh]
      exact pow_le_pow_left₀ hb'.le (by linarith only [hh]) 2
    · rw [ite_eq_right hh]
      exact sq_nonneg _
  rw [hInd,expected_centered_square s hs] at hCompare
  apply (le_div_iff₀ (sq_pos_of_pos hb')).mpr
  change probability s (fun X => b < Y X) * (b-μ)^2 ≤
    sampleExpectation s (fun X => (Y X)^2) - μ^2
  nlinarith only [hCompare]

end OverfullWork.UniformSubsetSampling

namespace OverfullWork.ChenShan

open Finset UniformSubsetSampling

/-- The expectation estimate in (5.4), allowing a palette drawn only
from the permitted colors. The weights count copies of each color. -/
theorem expected_palette_edge_count
    {W : Type*} [Fintype W] (s k : ℕ) (hs : s ≤ Fintype.card W) (hk : 0 < k)
    (hW : (511/512 : ℝ)*k ≤ Fintype.card W)
    (w : W → ℝ) (E : ℝ) (hE : 0 ≤ E) (hWeight : (∑ x, w x) ≤ E) :
    sampleExpectation s (fun X => ∑ x ∈ X, w x) ≤ (33/32 : ℝ)*((s:ℝ)/k)*E := by
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hLower : 0 < (511/512 : ℝ)*k := by positivity
  have hFraction : (s:ℝ)/Fintype.card W ≤ (512/511:ℝ)*((s:ℝ)/k) := by
    calc
      _ ≤ (s:ℝ)/((511/512:ℝ)*k) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hLower hW
      _ = _ := by ring
  rw [expected_fixed_size_weight s hs]
  calc
    _ ≤ ((s:ℝ)/Fintype.card W)*E := mul_le_mul_of_nonneg_left hWeight (by positivity)
    _ ≤ ((512/511:ℝ)*((s:ℝ)/k))*E := mul_le_mul_of_nonneg_right hFraction hE
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (512/511:ℝ) ≤ 33/32) (by positivity)) hE


/-- Quantitative form of the upper-tail estimate for the large edge
sets in (5.4). Each weight is bounded by the per-color edge budget B. -/
theorem palette_edge_count_tail
    {W : Type*} [Fintype W] (s k : ℕ) (hs : s ≤ Fintype.card W) (hs₀ : 0 < s) (hk : 0 < k)
    (hW : (511/512 : ℝ)*k ≤ Fintype.card W)
    (w : W → ℝ) (B E : ℝ) (hB : 0 ≤ B) (hE : 0 < E)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hTotal : (∑ x, w x) ≤ E) :
    let fraction := (s:ℝ)/k
    probability s (fun X => (5/4 : ℝ)*fraction*E < ∑ x ∈ X, w x) ≤
      ((33/32 : ℝ)*fraction*B*E) / (((7/32 : ℝ)*fraction*E)^2) := by
  intro fraction
  let Y (X : Finset W) := ∑ x ∈ X, w x
  let μ := sampleExpectation s Y
  have hf : 0 < fraction := by dsimp [fraction]; positivity
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hFraction : (s:ℝ)/Fintype.card W ≤ (33/32:ℝ)*fraction := by
    calc
      _ ≤ (s:ℝ)/((511/512:ℝ)*k) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hW
      _ = (512/511:ℝ)*fraction := by dsimp [fraction]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) hf.le
  have hSqs : ∑ x, (w x)^2 ≤ B*E := by
    calc
      _ ≤ ∑ x, B*w x := by
        apply sum_le_sum
        intro x _
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (hw x).2 (hw x).1
      _ = B*(∑ x, w x) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hTotal hB
  have hVar : sampleExpectation s (fun X => (Y X)^2) - μ^2 ≤
      (33/32:ℝ)*fraction*B*E := by
    have h := fixed_size_weight_variance_le s hs w (fun x => (hw x).1)
    dsimp only at h
    exact (h.trans (mul_le_mul hFraction hSqs
      (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))).trans_eq (by ring)
  have hMean : μ ≤ (33/32:ℝ)*fraction*E := expected_palette_edge_count s k hs hk hW w E hE.le hTotal
  have hδ : 0 < (7/32:ℝ)*fraction*E := by positivity
  have hGap : (7/32:ℝ)*fraction*E ≤ (5/4:ℝ)*fraction*E - μ := by linarith only [hMean]
  have hAbove : μ < (5/4:ℝ)*fraction*E := sub_pos.mp (hδ.trans_le hGap)
  have hCheb := sample_probability_above_mean_le s hs Y ((5/4:ℝ)*fraction*E) hAbove
  calc
    _ ≤ _ := hCheb
    _ ≤ ((33/32:ℝ)*fraction*B*E) / (((5/4:ℝ)*fraction*E-μ)^2) :=
      div_le_div_of_nonneg_right hVar (sq_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hδ)
      (pow_le_pow_left₀ hδ.le hGap 2)

end OverfullWork.ChenShan
