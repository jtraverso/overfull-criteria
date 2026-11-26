module

public import OverfullWork.ChenShanReserveJointDegreeCommon
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- Mean bounds for an inner class in (R2), allowing both possible
degree centers and the rounding and deletion allowance. -/
theorem reserve_inner_count_mean {I : Type*} [Fintype I]
    (p : I → ℝ) (N : Finset I) {μ t : ℝ} (hμ : 0 < μ)
    (hLower : 15*t/32 ≤ (N.card : ℝ)) (hUpper : (N.card : ℝ) ≤ 97*t/32)
    (hP : ∀ e ∈ N, (15/16)*μ ≤ p e ∧ p e ≤ (17/16)*μ) (ht : 0 ≤ t) :
    3*μ*t/8 ≤ mean p N ∧ mean p N ≤ 7*μ*t/2 := by
  have hLo : ((15/16)*μ)*(N.card : ℝ) ≤ mean p N := by
    unfold mean
    rw [mul_comm ((15/16)*μ),← nsmul_eq_mul,← sum_const]
    exact sum_le_sum fun e he => (hP e he).1
  have hHi : mean p N ≤ ((17/16)*μ)*(N.card : ℝ) := by
    unfold mean
    rw [mul_comm ((17/16)*μ),← nsmul_eq_mul,← sum_const]
    exact sum_le_sum fun e he => (hP e he).2
  have hl := mul_le_mul_of_nonneg_left hLower (show 0 ≤ (15/16)*μ by positivity)
  have hh := mul_le_mul_of_nonneg_left hUpper (show 0 ≤ (17/16)*μ by positivity)
  have hμt := mul_nonneg hμ.le ht
  exact ⟨by linarith only [hl,hLo,hμt],by linarith only [hh,hHi,hμt]⟩

theorem reserve_inner_count_bounds {μ t expected actual D : ℝ}
    (ht : 0 ≤ μ*t) (hLower : 3*μ*t/8 ≤ expected) (hUpper : expected ≤ 7*μ*t/2)
    (hD : D ≤ μ*t/8) (hCount : |actual-expected| ≤ D) :
    μ*t/4 ≤ actual ∧ actual ≤ 4*μ*t :=
  ⟨by linarith only [hLower,hD,(abs_le.mp hCount).1],
    by linarith only [ht,hUpper,hD,(abs_le.mp hCount).2]⟩

/-- The two neighborhoods of each outer vertex in the crossing cycle
have the same scale before sampling. -/
theorem crossing_outer_degree_window
    {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    {S : NestedTripartitePrefixes A B W ρ m k l} {i : ℕ} {δ : ℝ}
    (hb : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hi : i+1 ≤ l) (hm : 0 < m)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4) (hInit : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hδ : 0 ≤ δ) (hSmall : 64*δ ≤ ρ)
    (hHalf : 1/2 ≤ (k:ℝ)/m) (hK : (k:ℝ)/m ≤ 3/2)
    (j : Fin 6) (hj : j=1 ∨ j=3 ∨ j=5) (a : CrossingPart S i j) :
    let t : ℝ := ρ*nestedCoreSize ρ m i
    let out := reserveOutDegree (crossingArc S i F P Q j (crossingNext j)) a
    let inn := reserveInDegree (crossingArc S i F P Q (crossingNext.symm j) j) a
    (15*t/32 ≤ out ∧ out ≤ 97*t/32) ∧ (15*t/32 ≤ inn ∧ inn ≤ 97*t/32) := by
  dsimp only
  let n : ℝ := nestedCoreSize ρ m i
  let s : ℝ := nestedCoreSize ρ m (i+1)
  have hn : 0 ≤ n := by dsimp [n]; positivity
  obtain ⟨hs,hS,_⟩ := nested_crossing_core_window hρ hρsmall hInit
  change ρ*n ≤ s at hs
  change s ≤ 2*ρ*n at hS
  have hs₀ : 0 ≤ s := by dsimp [s]; positivity
  have hpL := mul_le_mul_of_nonneg_right hHalf hs₀
  have hpU := mul_le_mul_of_nonneg_right hK hs₀
  have hB := mul_le_mul_of_nonneg_right hSmall hn
  have hSwap : s/m*k = ((k:ℝ)/m)*s := by ring
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hCancel : s/m*m = s := div_mul_cancel₀ _ hmR.ne'
  have hCenter : ρ*n/2 ≤ crossingDegreeCenter ρ m k i j ∧
      crossingDegreeCenter ρ m k i j ≤ 3*ρ*n := by
    rcases hj with rfl | rfl | rfl
    · change ρ*n/2 ≤ s/m*k ∧ s/m*k ≤ 3*ρ*n
      rw [hSwap]
      exact ⟨by linarith only [hs,hpL],by linarith only [hS,hpU]⟩
    · change ρ*n/2 ≤ s/m*k ∧ s/m*k ≤ 3*ρ*n
      rw [hSwap]
      exact ⟨by linarith only [hs,hpL],by linarith only [hS,hpU]⟩
    · change ρ*n/2 ≤ s/m*m ∧ s/m*m ≤ 3*ρ*n
      rw [hCancel]
      exact ⟨by linarith only [hs,hInit],by linarith only [hS,hInit]⟩
  obtain ⟨ho,hi'⟩ := crossing_cycle_degree_errors hb hi (mul_nonneg hδ hn) j a
  have ho' := abs_le.mp ho
  have hi'' := abs_le.mp hi'
  exact ⟨⟨by linarith only [hCenter.1,hB,ho'.1],by linarith only [hCenter.2,hB,ho'.2]⟩,
    ⟨by linarith only [hCenter.1,hB,hi''.1],by linarith only [hCenter.2,hB,hi''.2]⟩⟩

/-- Each part of the protected level has size at most 3ρ times the
corresponding part of the previous level, including rounded color sizes. -/
theorem protected_prefix_class_sizes
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i+2 ≤ l)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hRound : 6 ≤ ρ*(nestedCoreSize ρ m (i+1) : ℝ))
    (hHalf : 1/2 ≤ (k:ℝ)/m) (hK : (k:ℝ)/m ≤ 3/2) :
    ((S.left (i+2)).card : ℝ) ≤ 3*ρ*(S.left (i+1)).card ∧
    ((S.right (i+2)).card : ℝ) ≤ 3*ρ*(S.right (i+1)).card ∧
    ((S.colors (i+2)).card : ℝ) ≤ 3*ρ*(S.colors (i+1)).card := by
  let s : ℝ := nestedCoreSize ρ m (i+1)
  let t : ℝ := nestedCoreSize ρ m (i+2)
  let p : ℝ := (k:ℝ)/m
  have ht : t < ρ*s+1 := nestedCoreSize_step_upper ρ hρ.le m (i+1)
  have hs : i+1 ≤ l := by omega
  have hR : t ≤ 3*ρ*s := by linarith only [ht,hRound]
  refine ⟨by rw [S.leftSize _ hi,S.leftSize _ hs]; exact hR,
    by rw [S.rightSize _ hi,S.rightSize _ hs]; exact hR,?_⟩
  have hP : 0 ≤ p := by linarith only [hHalf]
  have hP' := mul_le_mul_of_nonneg_left ht.le hP
  have hLow : p*s-1/2 ≤ ((S.colors (i+1)).card : ℝ) := by
    have h := (abs_le.mp (S.crossing_color_sizes hs).1).1
    linarith only [h]
  have hUp : ((S.colors (i+2)).card : ℝ) ≤ p*t+1/2 := by
    have h := (abs_le.mp (S.crossing_color_sizes (i:=i+1) hi).1).2
    linarith only [h]
  have hC := mul_le_mul_of_nonneg_left hLow (show 0 ≤ 3*ρ by positivity)
  have hT : 0 ≤ ρ*s := by linarith only [hRound]
  have hPS := mul_le_mul_of_nonneg_right hHalf hT
  nlinarith only [hP',hK,hρsmall,hC,hUp,hPS,hRound]


/-- The pointwise probability tolerance from Lemma 4.12 implies the
bounds used in the (R2) mean estimates. -/
theorem reserve_probability_window {p μ η₀ : ℝ} (hμ : 0 < μ)
    (hη₀ : η₀ ≤ 1/80) (hp : |p-μ| ≤ μ*η₀/100) :
    (15/16)*μ ≤ p ∧ p ≤ (17/16)*μ := by
  have hTol := mul_le_mul_of_nonneg_left hη₀ hμ.le
  have hAbs := abs_le.mp hp
  exact ⟨by linarith only [hTol,hAbs.1,hμ],by linarith only [hTol,hAbs.2,hμ]⟩

/-- Applied to the cyclic arc slots, (R2) has a lower and an upper
mean bound in both inner parts adjacent to any outer vertex. -/
theorem crossing_r2_reserve_means
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (prob : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → ℝ)
    {μ δ η₀ : ℝ} (hμ : 0 < μ) (hη₀ : η₀ ≤ 1/80)
    (hBounds : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hi : i+1 ≤ l) (hm : 0 < m) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hInit : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hδ : 0 ≤ δ) (hSmall : 64*δ ≤ ρ)
    (hHalf : 1/2 ≤ (k:ℝ)/m) (hK : (k:ℝ)/m ≤ 3/2)
    (hProb : ∀ j a b, crossingArc S i F P Q j (crossingNext j) a b →
      |prob ⟨j,a,b⟩-μ| ≤ μ*η₀/100) :
    let E := fun j => crossingArc S i F P Q j (crossingNext j)
    let t : ℝ := ρ*nestedCoreSize ρ m i
    (∀ j, (j=1 ∨ j=3 ∨ j=5) → ∀ a : CrossingPart S i j,
      3*μ*t/8 ≤ mean prob (cyclicOutNeighbors crossingNext E j a) ∧
        mean prob (cyclicOutNeighbors crossingNext E j a) ≤ 7*μ*t/2) ∧
    (∀ j, (crossingNext j=1 ∨ crossingNext j=3 ∨ crossingNext j=5) →
      ∀ b : CrossingPart S i (crossingNext j),
      3*μ*t/8 ≤ mean prob (cyclicInNeighbors crossingNext E j b) ∧
        mean prob (cyclicInNeighbors crossingNext E j b) ≤ 7*μ*t/2) := by
  dsimp only
  let E := fun j => crossingArc S i F P Q j (crossingNext j)
  let t : ℝ := ρ*nestedCoreSize ρ m i
  have ht : 0 ≤ t := by linarith only [hInit]
  constructor
  · intro j hj a
    have h := (crossing_outer_degree_window hBounds hi hm hρ hρsmall hInit hδ hSmall
      hHalf hK j hj a).1
    have he : ((cyclicOutNeighbors crossingNext E j a).card : ℝ) =
        reserveOutDegree (E j) a := by rw [cyclicOutNeighbors,card_map]; rfl
    apply reserve_inner_count_mean prob _ hμ (by rw [he]; exact h.1) (by rw [he]; exact h.2) _ ht
    intro e he'
    obtain ⟨b,hb,rfl⟩ := mem_map.mp he'
    exact reserve_probability_window hμ hη₀ (hProb j a b (mem_filter.mp hb).2)
  · intro j hj b
    have h := (crossing_outer_degree_window hBounds hi hm hρ hρsmall hInit hδ hSmall
      hHalf hK (crossingNext j) hj b).2
    have transport (x : Fin 6) (hx : x=j)
        (hxBound : 15*t/32 ≤ reserveInDegree (crossingArc S i F P Q x (crossingNext j)) b ∧
          reserveInDegree (crossingArc S i F P Q x (crossingNext j)) b ≤ 97*t/32) :
        15*t/32 ≤ reserveInDegree (E j) b ∧ reserveInDegree (E j) b ≤ 97*t/32 := by
      subst x
      exact hxBound
    have h' := transport _ (crossingNext.symm_apply_apply j) h
    have he : ((cyclicInNeighbors crossingNext E j b).card : ℝ) =
        reserveInDegree (E j) b := by rw [cyclicInNeighbors,card_map]; rfl
    apply reserve_inner_count_mean prob _ hμ (by rw [he]; exact h'.1) (by rw [he]; exact h'.2) _ ht
    intro e he'
    obtain ⟨a,ha,rfl⟩ := mem_map.mp he'
    exact reserve_probability_window hμ hη₀ (hProb j a b (mem_filter.mp ha).2)

end OverfullWork.ChenShan
