module

public import OverfullWork.ChenShanOrderedPairSampling
public import OverfullWork.ChenShanNestedSizes
public import OverfullWork.ChenShanHypergeometricTail
import OverfullWork.TwoSidedRobustSampling

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real UniformSubsetSampling
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]

theorem nestedCoreSize_lower_for_lookahead (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ : ρ ≤ 1)
    (m i r : ℕ) (hr : r ≤ 2) :
    ρ^2*(nestedCoreSize ρ m i : ℝ) ≤ nestedCoreSize ρ m (i+r) := by
  have hCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  have hPow : ρ^2 ≤ ρ := by nlinarith only [mul_nonneg hρ₀ (sub_nonneg.mpr hρ)]
  rcases hCases with rfl|rfl|rfl
  · exact mul_le_of_le_one_left (Nat.cast_nonneg _) (hPow.trans hρ)
  · exact (mul_le_mul_of_nonneg_right hPow (Nat.cast_nonneg _)).trans
      (nestedCoreSize_step_lower ρ m i)
  · exact nestedCoreSize_two_steps ρ hρ₀ m i

/-- With the source and target sizes comparable to the core size,
every ordered pair has the same exponentially summable error budget. -/
theorem failsDegreeSample_nested_card_le
    (E : A → B → Prop) (S : ℕ → Finset A) (T : ℕ → Finset B)
    (ρ ξ : ℝ) (m l : ℕ) (hρ₀ : 0 ≤ ρ) (hρ : ρ ≤ 1)
    (hξ₀ : 0 ≤ ξ) (hξ : ξ ≤ 1) (hn : 0 < Fintype.card A)
    (hSource : ∀ i ≤ l, ((S i).card : ℝ) ≤ 3*nestedCoreSize ρ m i)
    (hTarget : ∀ j ≤ l,
      (nestedCoreSize ρ m j : ℝ)/4 ≤ (T j).card ∧
        ((T j).card : ℝ) ≤ 3*nestedCoreSize ρ m j) :
    (((univ : Finset (Equiv.Perm A × Equiv.Perm B)).filter (fun z =>
      failsDegreeSample E S T (nestedCoreSize ρ m) l ξ z.1 z.2)).card : ℝ) ≤
      (∑ i : Fin (l+1), 18*(nestedCoreSize ρ m i : ℝ)*
        exp (-(ξ^2*ρ^2/144)*nestedCoreSize ρ m i)) *
      ((Fintype.card (Equiv.Perm A) : ℝ)*Fintype.card (Equiv.Perm B)) := by
  let s := nestedCoreSize ρ m
  let a := ξ^2*ρ^2/144
  let bound (i : ℕ) := 2*exp (-a*s i)
  have hTail (i : ℕ) (_hi : i ≤ l) (r : ℕ) (hr : r ≤ 2)
      (hj : i+r ≤ l) (v : A) :
      probability (T (i+r)).card (fun X => ξ*s (i+r) < sampledDegreeError E v X) ≤ bound i := by
    let k := (T (i+r)).card
    let e := ξ/3
    have hSize : e*k ≤ ξ*s (i+r) := by
      have hh := mul_le_mul_of_nonneg_left (hTarget (i+r) hj).2 (show 0 ≤ e by positivity)
      change e*k ≤ e*(3*s (i+r)) at hh
      dsimp only [e] at hh ⊢
      linarith only [hh]
    have hUpper := fixed_size_intersection_two_sided (card_le_univ (T (i+r))) (univ.filter (E v))
      e (by dsimp [e]; positivity) (by dsimp [e]; linarith only [hξ])
    have hLo : ρ^2*(s i : ℝ)/4 ≤ k :=
      (div_le_div_of_nonneg_right (nestedCoreSize_lower_for_lookahead ρ hρ₀ hρ m i r hr)
        (by norm_num)).trans (hTarget _ hj).1
    have hExponent : -(e^2*k)/4 ≤ -a*s i := by
      have hMul := mul_le_mul_of_nonneg_left hLo (sq_nonneg e)
      dsimp only [e,a] at hMul ⊢
      nlinarith only [hMul]
    apply le_trans _ (hUpper.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hExponent) (by norm_num)))
    apply probability_mono_on_card
    intro X hX hFail
    have h := hSize.trans hFail.le
    unfold sampledDegreeError at h
    rwa [hX] at h
  have h := failsDegreeSample_card_le E S T s l ξ bound hn (fun _ => by positivity) hTail
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro i _
  have hi : i.val ≤ l := by omega
  have hh := mul_le_mul_of_nonneg_right (hSource i.1 hi) (exp_pos (-a*s i)).le
  dsimp only [bound]
  nlinarith only [hh,show a = ξ^2*ρ^2/144 from rfl,show s i = nestedCoreSize ρ m i from rfl]

end OverfullWork.ChenShan
