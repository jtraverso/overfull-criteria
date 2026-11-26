module

public import OverfullWork.ChenShanReserveNeighborhoodGeometry
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

/-- A single Bernoulli sample meets all five reserve requirements.
The individual count sets refer to the same arc coordinates, and
the common-neighbor tests are given by disjoint pairs of coordinates. -/
theorem exists_sample_satisfying_reserve_tests
    {I V J H J₂ J₄ J₅ : Type*} [Fintype I] [Fintype V] [Fintype J] [Fintype H]
    {K : J → Type*} [∀ j, Fintype (K j)]
    (p : I → ℝ) (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (In Out : V → Finset I) (T : (j : J) → Finset (K j)) (f : (j : J) → K j × Bool ↪ I)
    (Extra : H → Finset I) (test₂ : J₂ → H) (test₄ : J₄ → H × H)
    (test₅ : J₅ → H) (protectedSize : J₅ → ℕ)
    {μ ρ ξ n C η₀ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) (hξ : 0 < ξ) (hn : 0 < n)
    (hη₀ : 0 ≤ η₀) (hη₀small : η₀ ≤ 1/40)
    (hBal : ∀ v, mean p (In v) = mean p (Out v))
    (hUpper : ∀ v, mean p (Out v) ≤ 4*μ*n)
    (hLocal : ∀ j x, x ∈ T j → ∀ b, μ/2 ≤ p (f j (x,b)) ∧ p (f j (x,b)) ≤ 2*μ)
    (hCard : ∀ j, ((T j).card : ℝ) ≤ 8*ρ*n)
    (hExtra : ∀ j, mean p (Extra j) ≤ 4*μ*n)
    (hMean₂ : ∀ j, 3*μ*(ρ*n)/8 ≤ mean p (Extra (test₂ j)) ∧
      mean p (Extra (test₂ j)) ≤ 7*μ*(ρ*n)/2)
    (hScale₂ : min (ξ*n/2) (μ*n) ≤ μ*(ρ*n)/8)
    (hMean₄ : ∀ j, (1/2+19*η₀)*mean p (Extra (test₄ j).1) ≤ mean p (Extra (test₄ j).2))
    (hScale₄ : ∀ j, min (ξ*n/2) (μ*n) ≤ η₀*mean p (Extra (test₄ j).1))
    (hProb₅ : ∀ j, ∀ e ∈ Extra (test₅ j), p e ≤ 3*μ)
    (hCard₅ : ∀ j, (Extra (test₅ j)).card ≤ protectedSize j)
    (hTests : (2*(Fintype.card V : ℝ)+Fintype.card H)+Fintype.card J ≤ C*n^2)
    (hLarge : 54*C/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 < n) :
    let hits (j : J) (s : I → Bool) :=
      count (T j) (fun x => s (f j (x,false)) && s (f j (x,true)))
    ∃ s : I → Bool,
      (∀ v, |count (Out v) s-count (In v) s| ≤ ξ*n ∧
        count (Out v) s+count (In v) s ≤ 10*μ*n) ∧
      (∀ j, μ*(ρ*n)/4 ≤ count (Extra (test₂ j)) s ∧ count (Extra (test₂ j)) s ≤ 4*μ*(ρ*n)) ∧
      (∀ j, hits j s ≤ 50*μ^2*ρ*n ∧
        (ρ*n/3 ≤ ((T j).card : ℝ) → μ^2*ρ*n/20 ≤ hits j s)) ∧
      (∀ j, (1/2+8*η₀)*count (Extra (test₄ j).1) s ≤ count (Extra (test₄ j).2) s) ∧
      (∀ j, count (Extra (test₅ j)) s ≤ 3*μ*(protectedSize j : ℝ)+ξ*n) := by
  dsimp only
  have hD₀ : 0 ≤ min (ξ*n/2) (μ*n) := le_min (by positivity) (by positivity)
  obtain ⟨s,hDegree,hPair,hCount⟩ := exists_reserve_with_additional_counts
    p hp₀ hp₁ In Out T f Extra hμ hρ hξ hn hBal hUpper hExtra hLocal hCard hTests hLarge
  refine ⟨s,hDegree,?_,hPair,?_,?_⟩
  · intro j
    exact reserve_inner_count_bounds (by positivity) (hMean₂ j).1 (hMean₂ j).2
      hScale₂ (hCount (test₂ j))
  · intro j
    have hMean₀ : 0 ≤ mean p (Extra (test₄ j).1) :=
      sum_nonneg fun e _ => hp₀ e
    exact reserve_sample_neighborhood_ratio hη₀ hη₀small hMean₀ hD₀ (hScale₄ j)
      (hMean₄ j) (hCount (test₄ j).1) (hCount (test₄ j).2)
  · intro j
    have hb : min (ξ*n/2) (μ*n) ≤ ξ*n := by
      have h := min_le_left (ξ*n/2) (μ*n)
      linarith only [h,mul_nonneg hξ.le hn.le]
    have hc := reserve_sample_protected_prefix_count p (Extra (test₅ j)) s (hProb₅ j)
      ((hCount (test₅ j)).trans hb)
    have hSize : ((Extra (test₅ j)).card : ℝ) ≤ protectedSize j := by exact_mod_cast hCard₅ j
    have hMul : 3*μ*((Extra (test₅ j)).card : ℝ) ≤ 3*μ*(protectedSize j : ℝ) :=
      mul_le_mul_of_nonneg_left hSize (by positivity)
    exact hc.trans (by linarith only [hMul])

end OverfullWork.ChenShan
