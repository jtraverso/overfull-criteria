module

public import OverfullWork.ChenShanCrossingArcEncoding
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

/-- The probability of either bad count in an (R3) test is exponentially
small. The upper estimate applies to every pair of distinct vertices.
The lower estimate applies when the candidate set has size at least ρn/3. -/
theorem common_neighbor_test_failure {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℝ) (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (f : J × Bool ↪ I) (T : Finset J) {μ ρ n : ℝ}
    (hμ : 0 < μ) (hρ : 0 < ρ) (hn : 0 < n)
    (hp : ∀ j ∈ T, ∀ b, μ/2 ≤ p (f (j,b)) ∧ p (f (j,b)) ≤ 2*μ)
    (hCard : (T.card : ℝ) ≤ 8*ρ*n) :
    let hits (s : I → Bool) := count T (fun j => s (f (j,false)) && s (f (j,true)))
    (∑ s ∈ univ.filter (fun s : I → Bool => 50*μ^2*ρ*n < hits s ∨
        (ρ*n/3 ≤ (T.card : ℝ) ∧ hits s < μ^2*ρ*n/20)), mass p s) ≤
      2*Real.exp (-(μ^2*ρ*n/204800)) := by
  dsimp only
  let q (j : J) := p (f (j,false))*p (f (j,true))
  let hits (s : I → Bool) := count T (fun j => s (f (j,false)) && s (f (j,true)))
  let b := μ^2*ρ*n
  have hb : 0 < b := by dsimp [b]; positivity
  have hUpper : mean q T ≤ 32*b := by
    calc
      _ ≤ ∑ _j ∈ T, (2*μ)*(2*μ) := sum_le_sum fun j hj =>
        mul_le_mul (hp j hj false).2 (hp j hj true).2 (hp₀ _) (by positivity)
      _ = (T.card : ℝ)*((2*μ)*(2*μ)) := by simp [nsmul_eq_mul]
      _ ≤ (8*ρ*n)*((2*μ)*(2*μ)) := mul_le_mul_of_nonneg_right hCard (by positivity)
      _ = _ := by dsimp [b]; ring
  have hLower (hT : ρ*n/3 ≤ (T.card : ℝ)) : b/12 ≤ mean q T := by
    calc
      _ = (ρ*n/3)*((μ/2)*(μ/2)) := by dsimp [b]; ring
      _ ≤ (T.card : ℝ)*((μ/2)*(μ/2)) := mul_le_mul_of_nonneg_right hT (by positivity)
      _ = ∑ _j ∈ T, (μ/2)*(μ/2) := by simp [nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun j hj =>
        mul_le_mul (hp j hj false).1 (hp j hj true).1 (by positivity) (hp₀ _)
  have hSubset : univ.filter (fun s : I → Bool => 50*b < hits s ∨
      (ρ*n/3 ≤ (T.card : ℝ) ∧ hits s < b/20)) ⊆
        univ.filter (fun s => b/40 ≤ |hits s-mean q T|) := by
    intro s hs
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases (mem_filter.mp hs).2 with h | ⟨hT,h⟩
    · exact (show b/40 ≤ hits s-mean q T by linarith only [hUpper,h,hb]).trans (le_abs_self _)
    · exact (show b/40 ≤ -(hits s-mean q T) by linarith only [hLower hT,h,hb]).trans (neg_le_abs _)
  have hRate : (b/40)^2/(4*(32*b)) = b/204800 := by field_simp; ring
  have hTail := pair_count_abs_tail p hp₀ hp₁ f T (show 0 < 32*b by positivity)
    hUpper (show 0 ≤ b/40 by positivity) (show b/40 ≤ 2*(32*b) by linarith only [hb])
  rw [hRate] at hTail
  have hMono := sum_le_sum_of_subset_of_nonneg (f := mass p) hSubset
    (fun s _ _ => mass_nonneg p hp₀ hp₁ s)
  have hScale (x : ℝ) : x*b = x*μ^2*ρ*n := by dsimp [b]; ring
  simpa only [hScale,b] using hMono.trans hTail

end OverfullWork.ChenShan
