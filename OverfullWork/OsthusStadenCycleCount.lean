module

public import OverfullWork.OsthusStadenLayerUnwinding

@[expose] public section


/-! The final count in Osthus–Staden §5.11. Losses are measured on the
actual rounded multiplicities and cell sizes. -/
namespace OverfullWork.DirectedRobustExpansion

private theorem mul_with_relative_losses {x y X Y a b : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : (1-a)*X ≤ x) (h₂ : (1-b)*Y ≤ y) :
    (1-(a+b))*(X*Y) ≤ x*y := by
  by_cases h : a+b ≤ 1
  · have hProd := mul_le_mul h₁ h₂ (mul_nonneg (by linarith only [h,ha]) hY) hx
    have hErr := mul_nonneg (mul_nonneg ha hb) (mul_nonneg hX hY)
    nlinarith only [hProd,hErr]
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith only [h]) (mul_nonneg hX hY)).trans
      (mul_nonneg hx hy)

/-- If each layer supplies `κ` cycles, the exact index count gives the
approximation bound with separate margins for the two refinements, the
retained cluster volume, the original factor degree, and the final
degree per layer. -/
theorem osthus_staden_approximate_cycle_count
    (r₀ s p κ L m n r : ℕ) (α β η e₀ es ep eκ em : ℝ)
    (hα : 0 ≤ α) (hβ : 0 < β) (hsPos : 0 < s) (hpPos : 0 < p)
    (h₀ : 0 ≤ e₀) (hs : 0 ≤ es) (hp : 0 ≤ ep) (hκ : 0 ≤ eκ) (hm : 0 ≤ em)
    (hR : α*(n:ℝ) = (r:ℝ))
    (hOrig : (1-e₀)*(α*(L:ℝ)) ≤ (r₀:ℝ)*β)
    (hS : (1-es)*(s:ℝ) ≤ ((s-1:ℕ):ℝ))
    (hP : (1-ep)*(p:ℝ) ≤ ((p-1:ℕ):ℝ))
    (hK : (1-eκ)*(β*(m:ℝ)) ≤ (κ:ℝ)*((s:ℝ)*(p:ℝ)))
    (hM : (1-em)*(n:ℝ) ≤ (L:ℝ)*(m:ℝ))
    (hη : e₀+es+ep+eκ+em ≤ η) :
    (1-η)*(r:ℝ) ≤ ((r₀*((s-1)*(p-1))*κ:ℕ):ℝ) := by
  have h1 := mul_with_relative_losses (by positivity) (Nat.cast_nonneg s)
    (by positivity) (Nat.cast_nonneg (s-1)) h₀ hs hOrig hS
  have h2 := mul_with_relative_losses (by positivity) (Nat.cast_nonneg p)
    (by positivity) (Nat.cast_nonneg (p-1)) (add_nonneg h₀ hs) hp h1 hP
  have h3 := mul_with_relative_losses (by positivity) (by positivity)
    (by positivity) (by positivity) (add_nonneg (add_nonneg h₀ hs) hp) hκ h2 hK
  let e := e₀+es+ep+eκ
  let cycles := ((r₀*((s-1)*(p-1))*κ:ℕ):ℝ)
  have he : 0 ≤ e := by unfold e; positivity
  have hCycle : (1-e)*(α*((L:ℝ)*(m:ℝ))) ≤ cycles := by
    have hPos : 0 < β*((s:ℝ)*(p:ℝ)) :=
      mul_pos hβ (mul_pos (by exact_mod_cast hsPos) (by exact_mod_cast hpPos))
    apply (mul_le_mul_iff_of_pos_right hPos).mp
    dsimp [e,cycles]
    push_cast
    nlinarith only [h3]
  have hProduct : (1-em)*(r:ℝ) ≤ α*((L:ℝ)*(m:ℝ)) := by
    rw [←hR]
    nlinarith only [mul_le_mul_of_nonneg_left hM hα]
  by_cases h : 1 ≤ e
  · have hη1 : 1 ≤ η := by dsimp [e] at h; linarith only [h,hη,hm]
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hη1]) (Nat.cast_nonneg r)).trans
      (by positivity)
  · have hMul := mul_le_mul_of_nonneg_left hProduct (by linarith only [h] : 0 ≤ 1-e)
    have hErr := mul_nonneg (mul_nonneg he hm) (Nat.cast_nonneg r : (0:ℝ) ≤ _)
    have hTot : e+em ≤ η := hη
    have hOrd := mul_le_mul_of_nonneg_right hTot (Nat.cast_nonneg r : (0:ℝ) ≤ _)
    nlinarith only [hCycle,hMul,hErr,hOrd]

end OverfullWork.DirectedRobustExpansion
