module

public import OverfullWork.KuhnOsthusPreprocessingScales

@[expose] public section


/-! Compatible local margins in Lemma 8.6 and Corollary 8.5. -/
namespace OverfullWork.DirectedRobustExpansion

/-- Choose a scale for the physical regularity error before constructing
the partition. The exceptional factors from Lemma 7.6 then leave enough
neighbours in each style to sample the extender of Lemma 8.6. -/
theorem exists_kuhn_osthus_preprocessing_pair_scales
    (d ε : ℝ) (hd : 0 < d) (hd₁ : d ≤ 1) (hε : 0 < ε) :
    ∃ ξCap ξ δ cMax : ℝ, 0 < ξCap ∧ 0 < ξ ∧ 0 ≤ δ ∧ 0 < cMax ∧
      ξ ≤ ε ∧ ξ ≤ 1 ∧ 4*ξ ≤ ε*d ∧ ξ ≤ d/4 ∧
      ∀ ξ₀ θ : ℝ, 0 ≤ ξ₀ → ξ₀ ≤ ξCap → θ ≤ d/2 → θ ≤ 1/2 →
      ∀ r m : ℕ, (r:ℝ) ≤ cMax*(m:ℝ) →
        ξ₀ ≤ ξ ∧ 2*(ξ₀+δ) ≤ ξ ∧ θ ≤ d-ξ₀ ∧
        (r:ℝ) ≤ δ*((m:ℝ)*ξ) ∧ (r:ℝ) ≤ (ξ-ξ₀)*(m:ℝ) ∧
        (1/200:ℝ) ≤ (1-θ)/50 ∧
        (1/200:ℝ)*d*(m:ℝ)+(r:ℝ) ≤ (1-θ)*((d-ξ₀)*(m:ℝ)/50) := by
  let ξ := min (ε/2) (min (ε*d/8) (d/4))
  have hξ : 0 < ξ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hξε : ξ ≤ ε/2 := min_le_left _ _
  have hξp : ξ ≤ ε*d/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hξd : ξ ≤ d/4 := (min_le_right _ _).trans (min_le_right _ _)
  let δ := ξ/8
  let cMax := min (δ*ξ) (min (ξ/2) (d/400))
  refine ⟨ξ/4,ξ,δ,cMax,by positivity,hξ,by dsimp only [δ]; positivity,
    lt_min (by dsimp only [δ]; positivity) (lt_min (by positivity) (by positivity)),
    by linarith only [hε,hξε],by linarith only [hd₁,hξd],
    by linarith only [hξp,hε,hd,mul_pos hε hd],hξd,?_⟩
  intro ξ₀ θ hξ₀ hCap hθd hθ m₀ m hRate
  have hRate₁ := hRate.trans (mul_le_mul_of_nonneg_right (min_le_left (δ*ξ) _) (Nat.cast_nonneg m))
  have hc₂ : cMax ≤ ξ/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc₃ : cMax ≤ d/400 := (min_le_right _ _).trans (min_le_right _ _)
  have hDensity : 3*d/4 ≤ d-ξ₀ := by linarith only [hξd,hCap,hξ]
  have hHalf : (1:ℝ)/2 ≤ 1-θ := by linarith only [hθ]
  have hAvail : (1/2:ℝ)*((3*d/4)*(m:ℝ)/50) ≤ (1-θ)*((d-ξ₀)*(m:ℝ)/50) := by
    apply mul_le_mul hHalf _ (by positivity) (by linarith only [hHalf])
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _)) (by norm_num)
  refine ⟨by linarith only [hξ,hCap],by dsimp only [δ]; linarith only [hξ,hCap],
    by linarith only [hθd,hDensity,hd],?_,?_,by linarith only [hθ],?_⟩
  · linarith only [hRate₁]
  · exact hRate.trans (mul_le_mul_of_nonneg_right
      (hc₂.trans (by linarith only [hCap,hξ])) (Nat.cast_nonneg m))
  · linarith only [hAvail,hRate,mul_le_mul_of_nonneg_right hc₃ (Nat.cast_nonneg m)]

/-- The sampling error can be chosen after the extender density and
an upper bound on the number of clusters. The same error works for
all realized cluster counts within that bound. -/
theorem exists_kuhn_osthus_preprocessing_sampling_error (ε d₀ : ℝ) (J : ℕ)
    (hε : 0 < ε) (hd₀ : 0 < d₀) (hJ : 0 < J) :
    ∃ η : ℝ, 0 < η ∧ η ≤ d₀/400 ∧
      ∀ n : ℕ, 0 < n → n ≤ J →
        4*η ≤ ε^3*(d₀/(n:ℝ)) ∧ 2*η ≤ d₀/(n:ℝ) ∧
        η ≤ (d₀/(n:ℝ))^2 ∧ 4*η ≤ d₀ := by
  let b := d₀/(J:ℝ)
  have hb : 0 < b := div_pos hd₀ (by exact_mod_cast hJ)
  let η := min (d₀/400) (min (ε^3*b/4) (min (b/2) (b^2)))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have he : η ≤ d₀/400 := min_le_left _ _
  have hcut : η ≤ ε^3*b/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hmax : η ≤ b/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcodeg : η ≤ b^2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨η,hη,he,?_⟩
  intro n hn hnJ
  have hB : b ≤ d₀/(n:ℝ) := div_le_div_of_nonneg_left hd₀.le (by exact_mod_cast hn) (by exact_mod_cast hnJ)
  refine ⟨?_,by linarith only [hmax,hB],hcodeg.trans ?_,by linarith only [hd₀,he]⟩
  · linarith only [hcut,mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ ε^3)]
  · rw [pow_two,pow_two]
    exact mul_self_le_mul_self hb.le hB

/-- A relative leftover rate chosen after the extender density meets
the two endpoint budgets in Corollary 8.5. The upper bound on the
number of clusters makes that choice uniform. -/
theorem kuhn_osthus_preprocessing_residual_endpoint_budgets
    (r r₀ s n J m : ℕ) (ε ζ' d₀ η ηS : ℝ)
    (hs : 0 < s) (hn : 0 < n) (hnJ : n ≤ J)
    (hε : 0 < ε) (hεSmall : ε ≤ 1/100) (hζ : ζ' ≤ 1/1000)
    (hd₀ : 0 < d₀) (hη : 0 ≤ η) (hηS : ηS ≤ d₀/400)
    (hRate : η ≤ ε^2*(d₀/(J:ℝ))/((s:ℝ)*(J:ℝ)))
    (hr : r ≤ 2*n*(50*m)) (hr₀ : r₀ = ⌊η*(r:ℝ)⌋₊) :
    ((r₀*s:ℕ):ℝ) ≤ ε*(d₀/(n:ℝ))*((2*ε)*(50*m)) ∧
      ζ'*d₀*(50*m)+((r₀*s:ℕ):ℝ) ≤ 21*((d₀/200-ηS)*(50*m)) := by
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hJ : (0:ℝ) < J := hnR.trans_le (by exact_mod_cast hnJ)
  have hEnv : (r:ℝ) ≤ 2*(J:ℝ)*(50*(m:ℝ)) := by
    exact_mod_cast hr.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hnJ))
  have hFloor : (r₀:ℝ) ≤ η*(r:ℝ) := by rw [hr₀]; exact Nat.floor_le (by positivity)
  have hηBound := (le_div_iff₀ (mul_pos hsR hJ)).mp hRate
  have hSpend : ((r₀*s:ℕ):ℝ) ≤ 2*ε^2*(d₀/(J:ℝ))*(50*(m:ℝ)) := by
    push_cast
    have hLeft := mul_le_mul_of_nonneg_right (hFloor.trans (mul_le_mul_of_nonneg_left hEnv hη)) hsR.le
    have hRight := mul_le_mul_of_nonneg_right hηBound (by positivity : 0 ≤ 2*(50*(m:ℝ)))
    linarith only [hLeft,hRight]
  have hD : d₀/(J:ℝ) ≤ d₀/(n:ℝ) := div_le_div_of_nonneg_left hd₀.le hnR (by exact_mod_cast hnJ)
  have hPay := hSpend.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 2*ε^2))
      (by positivity : 0 ≤ 50*(m:ℝ)))
  refine ⟨by linarith only [hPay],?_⟩
  have hDen : d₀/(J:ℝ) ≤ d₀ := div_le_self hd₀.le (by exact_mod_cast (show 1 ≤ J by omega))
  have hEps : 2*ε^2 ≤ 1/1000 := by
    nlinarith only [mul_le_mul_of_nonneg_right hεSmall hε.le,hεSmall]
  have hFlat : 2*ε^2*(d₀/(J:ℝ)) ≤ d₀/1000 := by
    linarith only [mul_le_mul hEps hDen (by positivity : 0 ≤ d₀/(J:ℝ)) (by norm_num : (0:ℝ) ≤ 1/1000)]
  have hStyle : (2/1000:ℝ)*d₀ ≤ 21*(d₀/200-ηS) := by linarith only [hd₀,hηS]
  have hS := mul_le_mul_of_nonneg_right hStyle (by positivity : 0 ≤ 50*(m:ℝ))
  have hL := mul_le_mul_of_nonneg_right hFlat (by positivity : 0 ≤ 50*(m:ℝ))
  have hZ := mul_le_mul_of_nonneg_right hζ (by positivity : 0 ≤ d₀*(50*(m:ℝ)))
  linarith only [hSpend,hS,hL,hZ]

end OverfullWork.DirectedRobustExpansion
