module

public import OverfullWork.OsthusStadenPackFromBalancedLayers

@[expose] public section


/-! Rounded counts for the rotation batches and the final Hamilton pack. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical

/-- Round the number of factors using one cut family, while keeping
the two reserve margins for reuse. -/
theorem exists_osthus_staden_merge_batch_margins
    (n κ p : ℕ) (d ν τ γ : ℝ) (hp : 5 ≤ p)
    (hCost : (κ:ℝ)/((p-4:ℕ):ℝ)+1+ν*(n:ℝ) ≤ d*τ*(n:ℝ))
    (hDegree : γ*(n:ℝ)+(κ:ℝ)/((p-4:ℕ):ℝ)+1 ≤ d*(n:ℝ)) :
    ∃ batch : ℕ, κ ≤ (p-4)*batch ∧
      (batch:ℝ)+ν*(n:ℝ) ≤ d*τ*(n:ℝ) ∧
      γ*(n:ℝ)+(batch:ℝ) ≤ d*(n:ℝ) := by
  let rate := (κ:ℝ)/((p-4:ℕ):ℝ)
  let batch := ⌈rate⌉₊
  have hpR : (0:ℝ) < (p-4:ℕ) := by exact_mod_cast (show 0 < p-4 by omega)
  have hUp : (batch:ℝ) ≤ rate+1 := (Nat.ceil_lt_add_one (by dsimp only [rate]; positivity)).le
  have hLow : rate ≤ (batch:ℝ) := Nat.le_ceil _
  refine ⟨batch,?_,?_,?_⟩
  · have h := (div_le_iff₀ hpR).mp hLow
    rw [mul_comm] at h
    exact_mod_cast h
  · linarith only [hUp,hCost]
  · linarith only [hUp,hDegree]

/-- The actual integer floors in (7) and (20) satisfy the final cycle
count when the input rates pay the two rounding losses. Here m is
the size of a half of an adapted p-cell before the one-vertex trim. -/
theorem osthus_staden_cycle_count_of_rounded_degrees
    (r₀ s p κ K m n r : ℕ) (a β γ η e₀ es ep eκ em : ℝ)
    (ha : 0 ≤ a) (hβ : 0 < β) (hs : 0 < s) (hp : 0 < p)
    (h₀ : 0 ≤ e₀) (hEs : 0 ≤ es) (hEp : 0 ≤ ep) (hEκ : 0 ≤ eκ) (hEm : 0 ≤ em)
    (hr : a*(n:ℝ) = (r:ℝ))
    (hr₀ : r₀ = ⌊(a-γ)*(K:ℝ)/β⌋₊)
    (hκ : κ = ⌊(1-γ)*(1-5*γ)*β*((2*m:ℕ):ℝ)⌋₊)
    (hOrig : γ*(K:ℝ)+β ≤ e₀*(a*(K:ℝ)))
    (hS : 1 ≤ es*((2*s:ℕ):ℝ)) (hP : 1 ≤ ep*(p:ℝ))
    (hK : 1 ≤ (eκ-6*γ)*(β*((2*m:ℕ):ℝ)))
    (hVolume : (1-em)*(n:ℝ) ≤ (K:ℝ)*((((2*s)*p*(2*m)):ℕ):ℝ))
    (hη : e₀+es+ep+eκ+em ≤ η) :
    (1-η)*(r:ℝ) ≤ ((r₀*((2*s-1)*(p-1))*κ:ℕ):ℝ) := by
  have hrFloor : (a-γ)*(K:ℝ)/β < (r₀:ℝ)+1 := by
    rw [hr₀]
    exact Nat.lt_floor_add_one _
  have hOrig' : (1-e₀)*(a*(K:ℝ)) ≤ (r₀:ℝ)*β := by
    have h := (div_lt_iff₀ hβ).mp hrFloor
    nlinarith only [h,hOrig]
  have hs' : (1-es)*((2*s:ℕ):ℝ) ≤ ((2*s-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ 2*s by omega),Nat.cast_one]
    linarith only [hS]
  have hp' : (1-ep)*(p:ℝ) ≤ ((p-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ p by omega),Nat.cast_one]
    linarith only [hP]
  have hκFloor : (1-γ)*(1-5*γ)*β*((2*m:ℕ):ℝ) < (κ:ℝ)+1 := by
    rw [hκ]
    exact Nat.lt_floor_add_one _
  have hκ' : (1-eκ)*(β*((2*m:ℕ):ℝ)) ≤ (κ:ℝ) := by
    have hγsq : 0 ≤ 5*γ^2*β*((2*m:ℕ):ℝ) := by positivity
    nlinarith only [hK,hκFloor,hγsq]
  have hCount : (1-eκ)*(β*((((2*s)*p*(2*m)):ℕ):ℝ)) ≤
      (κ:ℝ)*(((2*s:ℕ):ℝ)*(p:ℝ)) := by
    rw [Nat.cast_mul,Nat.cast_mul]
    calc
      _ = ((1-eκ)*(β*((2*m:ℕ):ℝ)))*(((2*s:ℕ):ℝ)*(p:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hκ' (by positivity)
  exact osthus_staden_approximate_cycle_count r₀ (2*s) p κ K ((2*s)*p*(2*m)) n r
    a β η e₀ es ep eκ em ha hβ (by omega) hp h₀ hEs hEp hEκ hEm hr hOrig' hs' hp' hCount hVolume hη

end OverfullWork.DirectedRobustExpansion
