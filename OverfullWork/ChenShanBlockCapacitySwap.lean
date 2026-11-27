module

public import OverfullWork.ChenShanBlockPartSampling
public import OverfullWork.ChenShanSwapVarianceStep
public import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V E Z : Type*} [Fintype V] [Fintype E]

/-- Count the incidences of the indexed internal edges, including
separate incidences of parallel copies. -/
noncomputable def internalEdgeIncidences (x y : E → V) (v : V) : ℝ :=
  ∑ e, (eventIndicator (x e = v) + eventIndicator (y e = v))

/-- Capacity (5.5) as a function of the included vertices. -/
noncomputable def subsetBlockCapacity (x y : E → V) (S : Finset Z)
    (w : Z → V → ℝ) (cap : Z → ℝ) (w₁ w₂ : ℝ) (T : Finset V) : ℝ :=
  w₂*(∑ e, eventIndicator (x e ∈ T ∧ y e ∈ T)) +
    ∑ z ∈ S, min (w₁*(∑ v ∈ T, w z v)) (cap z)

/-- The vertex weight used for the exchange estimate in (5.6). -/
noncomputable def blockCapacityInfluence (x y : E → V) (S : Finset Z)
    (w : Z → V → ℝ) (w₁ w₂ : ℝ) (v : V) : ℝ :=
  w₂*internalEdgeIncidences x y v + w₁*(∑ z ∈ S, w z v)

private theorem abs_indicator_sub_le_one (P Q : Prop) :
    |eventIndicator P - eventIndicator Q| ≤ 1 := by
  by_cases hP : P <;> by_cases hQ : Q <;> norm_num [eventIndicator,hP,hQ]

omit [Fintype V] in
private theorem internal_count_swap_bound (x y : E → V) (T U : Finset V) (u v : V)
    (hSame : ∀ q, q ≠ u → q ≠ v → (q ∈ T ↔ q ∈ U)) :
    |(∑ e, eventIndicator (x e ∈ T ∧ y e ∈ T)) -
      ∑ e, eventIndicator (x e ∈ U ∧ y e ∈ U)|
      ≤ internalEdgeIncidences x y u + internalEdgeIncidences x y v := by
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  unfold internalEdgeIncidences
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro e _
  have hNonneg (P : Prop) : 0 ≤ eventIndicator P := by
    by_cases h : P <;> simp [eventIndicator,h]
  have hOne (P : Prop) (h : P) : eventIndicator P = 1 := by simp [eventIndicator,h]
  by_cases h : x e = u ∨ y e = u ∨ x e = v ∨ y e = v
  · apply (abs_indicator_sub_le_one _ _).trans
    rcases h with h | h | h | h
    · rw [hOne _ h]
      linarith only [hNonneg (y e = u),hNonneg (x e = v),hNonneg (y e = v)]
    · rw [hOne _ h]
      linarith only [hNonneg (x e = u),hNonneg (x e = v),hNonneg (y e = v)]
    · rw [hOne _ h]
      linarith only [hNonneg (x e = u),hNonneg (y e = u),hNonneg (y e = v)]
    · rw [hOne _ h]
      linarith only [hNonneg (x e = u),hNonneg (y e = u),hNonneg (x e = v)]
  · push Not at h
    obtain ⟨hxu,hyu,hxv,hyv⟩ := h
    have hEq := congrArg eventIndicator
      (propext (and_congr (hSame _ hxu hxv) (hSame _ hyu hyv)))
    rw [hEq,sub_self,abs_zero]
    exact add_nonneg (add_nonneg (hNonneg _) (hNonneg _)) (add_nonneg (hNonneg _) (hNonneg _))

private theorem degree_weight_swap_bound (w : V → ℝ) (hw : ∀ q, 0 ≤ w q)
    (T U : Finset V) (u v : V) (huv : u ≠ v)
    (hSame : ∀ q, q ≠ u → q ≠ v → (q ∈ T ↔ q ∈ U)) :
    |(∑ q ∈ T, w q) - ∑ q ∈ U, w q| ≤ w u + w v := by
  have hInd (F : Finset V) : (∑ q ∈ F, w q) = ∑ q, eventIndicator (q ∈ F)*w q := by
    unfold eventIndicator
    simp_rw [ite_mul,one_mul,zero_mul]
    rw [← sum_filter]
    congr 1
    ext q
    simp
  rw [hInd T,hInd U,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  have hAt (q : V) : |eventIndicator (q ∈ T)*w q-eventIndicator (q ∈ U)*w q| ≤
      (if q = u then w u else 0)+(if q = v then w v else 0) := by
    by_cases hu : q = u
    · subst q
      rw [ite_eq_left rfl,ite_eq_right huv,add_zero,← sub_mul,abs_mul,abs_of_nonneg (hw u)]
      exact (mul_le_mul_of_nonneg_right (abs_indicator_sub_le_one _ _) (hw u)).trans_eq (one_mul _)
    · by_cases hv : q = v
      · subst q
        rw [ite_eq_right hu,ite_eq_left rfl,zero_add,← sub_mul,abs_mul,abs_of_nonneg (hw v)]
        exact (mul_le_mul_of_nonneg_right (abs_indicator_sub_le_one _ _) (hw v)).trans_eq (one_mul _)
      · rw [ite_eq_right hu,ite_eq_right hv,hSame q hu hv,sub_self,abs_zero,add_zero]
  have h := sum_le_sum (s := (univ : Finset V)) (fun q _ => hAt q)
  simpa only [sum_add_distrib,sum_ite_eq',mem_univ,ite_true] using h

/-- Changing only the membership of u and v changes (5.5) by at most
the sum of their influence weights. In particular this applies to every
swap inside one sampled part. -/
theorem block_capacity_swap_abs_le (x y : E → V) (S : Finset Z)
    (w : Z → V → ℝ) (cap : Z → ℝ) (w₁ w₂ : ℝ) (T U : Finset V) (u v : V)
    (huv : u ≠ v) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : ∀ z ∈ S, ∀ q, 0 ≤ w z q)
    (hSame : ∀ q, q ≠ u → q ≠ v → (q ∈ T ↔ q ∈ U)) :
    |subsetBlockCapacity x y S w cap w₁ w₂ T-subsetBlockCapacity x y S w cap w₁ w₂ U| ≤
      blockCapacityInfluence x y S w w₁ w₂ u + blockCapacityInfluence x y S w w₁ w₂ v := by
  let D (F : Finset V) := ∑ e, eventIndicator (x e ∈ F ∧ y e ∈ F)
  let g (F : Finset V) (z : Z) := min (w₁*(∑ q ∈ F, w z q)) (cap z)
  have hD := mul_le_mul_of_nonneg_left (internal_count_swap_bound x y T U u v hSame) hw₂
  have hC (z : Z) (hz : z ∈ S) :
      |g T z-g U z| ≤ w₁*(w z u+w z v) := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self,abs_zero,max_eq_left (abs_nonneg _),← mul_sub,abs_mul,abs_of_nonneg hw₁]
    exact mul_le_mul_of_nonneg_left (degree_weight_swap_bound (w z) (hw z hz) T U u v huv hSame) hw₁
  have hS := (abs_sum_le_sum_abs (s := S) (fun z => g T z-g U z)).trans (sum_le_sum hC)
  rw [sum_sub_distrib,← mul_sum,sum_add_distrib] at hS
  change |(w₂*D T+∑ z ∈ S, g T z) - (w₂*D U+∑ z ∈ S, g U z)| ≤ _
  rw [show (w₂*D T+∑ z ∈ S, g T z) - (w₂*D U+∑ z ∈ S, g U z) =
    w₂*(D T-D U)+((∑ z ∈ S, g T z)-(∑ z ∈ S, g U z)) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg hw₂]
  change w₂*|D T-D U| + |(∑ z ∈ S, g T z) - ∑ z ∈ S, g U z| ≤ _
  have hPair := add_le_add hD hS
  unfold blockCapacityInfluence
  nlinarith only [hPair]


/-- The squared influence budget used to pass from (5.6) to the
variance of the capacity. The cap and the swap estimate use the
same vertex weights. -/
theorem block_capacity_influence_sq_sum (x y : E → V) (S : Finset Z)
    (w : Z → V → ℝ) (w₁ w₂ a : ℝ)
    (hw₁ : 0 ≤ w₁) (hScale : w₁ ≤ w₂) (ha : 0 ≤ a)
    (hw : ∀ z ∈ S, ∀ v, 0 ≤ w z v)
    (hDegree : ∀ v, internalEdgeIncidences x y v + (∑ z ∈ S, w z v) ≤ a) :
    (∑ v, (blockCapacityInfluence x y S w w₁ w₂ v)^2) ≤
      2*w₂^2*a*((Fintype.card E:ℝ)+(∑ z ∈ S, ∑ v, w z v)) := by
  let F := blockCapacityInfluence x y S w w₁ w₂
  have hw₂ : 0 ≤ w₂ := hw₁.trans hScale
  have hi (v : V) : 0 ≤ internalEdgeIncidences x y v := by
    unfold internalEdgeIncidences
    apply sum_nonneg
    intro e _
    unfold eventIndicator
    positivity
  have hs (v : V) : 0 ≤ ∑ z ∈ S, w z v := sum_nonneg (fun z hz => hw z hz v)
  have hF (v : V) : 0 ≤ F v := add_nonneg (mul_nonneg hw₂ (hi v)) (mul_nonneg hw₁ (hs v))
  have hCap (v : V) : F v ≤ w₂*a := by
    have h := mul_le_mul_of_nonneg_right hScale (hs v)
    have h' := mul_le_mul_of_nonneg_left (hDegree v) hw₂
    dsimp [F,blockCapacityInfluence]
    nlinarith only [h,h']
  have hEdgeSum : (∑ v, internalEdgeIncidences x y v) = 2*(Fintype.card E:ℝ) := by
    simp only [internalEdgeIncidences]
    rw [sum_comm]
    simp only [sum_add_distrib,eventIndicator,sum_ite_eq,mem_univ,ite_true,
      sum_const,card_univ,nsmul_eq_mul]
    ring
  have hS : (∑ v, F v) ≤ 2*w₂*((Fintype.card E:ℝ)+(∑ z ∈ S, ∑ v, w z v)) := by
    simp only [F,blockCapacityInfluence,sum_add_distrib,← mul_sum,hEdgeSum]
    rw [sum_comm (s := (univ : Finset V)) (t := S)]
    have hBound : 0 ≤ ∑ z ∈ S, ∑ v, w z v := sum_nonneg (fun z hz =>
      sum_nonneg (fun v _ => hw z hz v))
    have h₁ := mul_le_mul_of_nonneg_right hScale hBound
    have h₂ := mul_nonneg hw₂ hBound
    nlinarith only [h₁,h₂]
  have hSq : (∑ v, (F v)^2) ≤ (w₂*a)*(∑ v, F v) := by
    rw [mul_sum]
    apply sum_le_sum
    intro v _
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hCap v) (hF v)
  have h := hSq.trans (mul_le_mul_of_nonneg_left hS (mul_nonneg hw₂ ha))
  convert h using 1
  ring


/-- Variance of the capacity when only one part is sampled and the
set of selected vertices outside that sample is held fixed. -/
theorem block_capacity_fixed_part_variance (x y : E → V) (S : Finset Z)
    (w : Z → V → ℝ) (cap : Z → ℝ) (w₁ w₂ : ℝ)
    (P R : Finset V) (s : ℕ) (hs : s ≤ P.card)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : ∀ z ∈ S, ∀ v, 0 ≤ w z v) :
    uniformBlockVariance (fun T : ↥(P.powersetCard s) =>
      subsetBlockCapacity x y S w cap w₁ w₂ (R ∪ T.val)) ≤
      4*((s:ℝ)/P.card)*(∑ v ∈ P, (blockCapacityInfluence x y S w w₁ w₂ v)^2) := by
  classical
  refine fixed_size_swap_variance P s hs
    (fun T => subsetBlockCapacity x y S w cap w₁ w₂ (R ∪ T))
    (blockCapacityInfluence x y S w w₁ w₂) ?_
  intro T _ u _ v _ huv _ _
  apply block_capacity_swap_abs_le x y S w cap w₁ w₂ _ _ u v huv hw₁ hw₂ hw
  intro q hqu hqv
  simp only [mem_union, mem_insert, hqu, hqv, false_or]

end OverfullWork.ChenShan
