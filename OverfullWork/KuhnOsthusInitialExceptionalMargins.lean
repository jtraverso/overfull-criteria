module

public import OverfullWork.KuhnOsthusExceptionalStageBudgets

@[expose] public section


/-! Choose the common exceptional proportion and the coarse cluster
threshold before applying directed regularity. -/
namespace OverfullWork.DirectedRobustExpansion

/-- The path-cover scales and capacity denominator of Lemma 7.6 can
be fixed before choosing interval lengths and style counts. -/
theorem exists_wound_factor_packing_scales (d : ℝ) (hd : 0 < d) (hd₁ : d ≤ 1) :
    ∃ (ε ν τ γ : ℝ) (c : ℕ),
      0 < ε ∧ ε ≤ 1 ∧ 0 < ν ∧ ε+ν ≤ τ ∧ 16*τ ≤ γ ∧ γ ≤ 1 ∧
      6*ε ≤ d ∧ ν ≤ (d-2*ε)*τ ∧ γ ≤ d-2*ε ∧ 32 ≤ c ∧ 20 ≤ (c:ℝ)*ε ∧
      ∀ m : ℕ, max (2*c) ⌈1/ε⌉₊ ≤ m → 2*c ≤ m ∧ 1 ≤ ε*(m:ℝ) := by
  let γ := d/2
  let τ := d/64
  let ε := τ/4
  let ν := (d-2*ε)*τ/4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hdε : 0 < d-2*ε := by dsimp [ε,τ]; linarith only [hd]
  have hν : 0 < ν := by dsimp only [ν]; positivity
  have hν' : ν ≤ τ/4 := by
    have h := mul_le_mul_of_nonneg_right (show d-2*ε ≤ 1 by linarith only [hd₁,hε]) hτ.le
    dsimp only [ν]
    linarith
  let c := max 32 ⌈20/ε⌉₊
  have hc : 20/ε ≤ (c:ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈20/ε⌉₊ ≤ c from le_max_right _ _))
  have hCap := (div_le_iff₀ hε).mp hc
  refine ⟨ε,ν,τ,γ,c,hε,?_,hν,?_,?_,?_,?_,?_,?_,le_max_left _ _,hCap,?_⟩
  · dsimp [ε,τ]; linarith only [hd₁]
  · dsimp only [ε]; linarith only [hν',hτ]
  · dsimp [τ,γ]; linarith only [hd]
  · dsimp [γ]; linarith only [hd₁]
  · dsimp [ε,τ]; linarith only [hd]
  · dsimp only [ν]; linarith only [mul_pos hdε hτ]
  · dsimp [γ,ε,τ]; linarith only [hd]
  · intro m hm
    have hCut : 1/ε ≤ (m:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈1/ε⌉₊ ≤ m from (le_max_right _ _).trans hm))
    exact ⟨(le_max_left _ _).trans hm,by simpa only [mul_comm] using (div_le_iff₀ hε).mp hCut⟩

/-- A coarse cluster threshold suffices for the reduced routing
requirements on every winding interval. -/
theorem exists_wound_reduced_route_margins (α μ τ : ℝ)
    (hμ : 0 < μ) (hμτ : μ ≤ τ) (hτ : τ ≤ 1/4) (hα : 6*τ ≤ α) :
    ∃ kMin : ℕ, ∀ k b : ℕ, kMin ≤ k → 0 < b →
      2 ≤ τ*(k:ℝ) ∧ 8 ≤ (μ^2/2)*((b*k:ℕ):ℝ) ∧
        (2*τ+(μ^2/2)/2)*((b*k:ℕ):ℝ)+2 ≤ α*((b*k:ℕ):ℝ) := by
  have hτpos : 0 < τ := hμ.trans_le hμτ
  have hαpos : 0 < α := by linarith only [hτpos,hα]
  let kMin := max ⌈2/τ⌉₊ (max ⌈16/μ^2⌉₊ ⌈4/α⌉₊)
  refine ⟨kMin,?_⟩
  intro k b hk hb
  have hCut (x : ℝ) (hx : ⌈x⌉₊ ≤ kMin) : x ≤ (k:ℝ) :=
    (Nat.le_ceil x).trans (by exact_mod_cast hx.trans hk)
  have hτk := (div_le_iff₀ hτpos).mp (hCut (2/τ) (le_max_left _ _))
  have hμk := (div_le_iff₀ (sq_pos_of_pos hμ)).mp
    (hCut (16/μ^2) ((le_max_left _ _).trans (le_max_right _ _)))
  have hαk := (div_le_iff₀ hαpos).mp (hCut (4/α) ((le_max_right _ _).trans (le_max_right _ _)))
  have hBk : (k:ℝ) ≤ ((b*k:ℕ):ℝ) := by exact_mod_cast Nat.le_mul_of_pos_left k hb
  have hBk0 : (0:ℝ) ≤ ((b*k:ℕ):ℝ) := Nat.cast_nonneg _
  have hμτ' : μ^2 ≤ τ := by
    have hμ₁ : μ ≤ 1 := by linarith only [hμτ,hτ]
    have h := mul_le_of_le_one_right hμ.le hμ₁
    linarith only [h,hμτ]
  have hα' : 2*τ+(μ^2/2)/2 ≤ α/2 := by linarith only [hα,hμτ',hτpos]
  have hμ' := mul_le_mul_of_nonneg_left hBk (sq_nonneg μ)
  have hα'k := mul_le_mul_of_nonneg_left hBk hαpos.le
  have hProd := mul_le_mul_of_nonneg_right hα' hBk0
  exact ⟨by linarith only [hτk],by linarith only [hμk,hμ'],by linarith only [hαk,hα'k,hProd]⟩

set_option maxHeartbeats 700000 in
/-- Bound all three applications of Lemma 7.6 by the same exceptional
proportion. The loss budget is measured against one whole cluster.
Increasing the coarse cluster count pays for that loss independently
of the order in which the densities of the reserves were chosen. -/
theorem exists_wound_factor_global_margins
    (Λ c : ℕ) (α θ μ D ζMax : ℝ) (hc : 0 < c)
    (hα : 0 < α) (hθ : 0 < θ) (hμ : 0 < μ) (hD : 0 ≤ D) (hζMax : 0 < ζMax) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1/2 ∧ ζ ≤ ζMax ∧ ∃ kMin : ℕ,
      ∀ (L k base m K l b z r priorLoss : ℕ) (σ : ℝ),
        kMin ≤ k → 0 < l → 6 ≤ b → 0 < m → σ ≤ 1/2 →
        L = l*b → base = K*m → K*l ≤ Λ →
        (z:ℝ) ≤ ζ*((z+L*k*base:ℕ):ℝ) →
        ((K*l*r+priorLoss:ℕ):ℝ) ≤ D*(base:ℝ) →
        (((4*c+2)*z+K*l*r+priorLoss:ℕ):ℝ) <
          (α/3*(k:ℝ))*((b-3:ℕ):ℝ)*((1-σ)*(θ*(α/3)*(m:ℝ))) ∧
        (z:ℝ)*(8/(μ^2/2)+6) < ((m:ℝ)/(2*(c:ℝ)))*((μ^2/2)*((b*k:ℕ):ℝ)/16) := by
  let E := θ*(α/3)^2
  let F := 8/(μ^2/2)+6
  let R := (μ^2/2)/(32*(c:ℝ))
  let A := (Λ:ℝ)+1
  let C := 4*(c:ℝ)+2
  have hc' : (0:ℝ) < c := by exact_mod_cast hc
  have hE : 0 < E := by dsimp [E]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  let ζ := min (min (1/2:ℝ) ζMax) (min (E/(32*A*C)) (R/(4*A*F)))
  have hζ : 0 < ζ := lt_min (lt_min (by norm_num) hζMax) (lt_min (by positivity) (by positivity))
  have hζHalf : ζ ≤ 1/2 := (min_le_left _ _).trans (min_le_left _ _)
  have hζUpper : ζ ≤ ζMax := (min_le_left _ _).trans (min_le_right _ _)
  let kMin := max 1 ⌈16*A*D/E⌉₊
  refine ⟨ζ,hζ,hζHalf,hζUpper,kMin,?_⟩
  intro L k base m K l b z r priorLoss σ hkMin hl hb hm hσ hWinding hCell hSlots hZ hDegrees
  have hk : 0 < k := by have h := (le_max_left 1 ⌈16*A*D/E⌉₊).trans hkMin; omega
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hL : 0 < L := by rw [hWinding]; exact Nat.mul_pos hl (by omega)
  have hχ : 0 ≤ D/(k:ℝ) := div_nonneg hD hkR.le
  have hSize : (z:ℝ) ≤ (2*ζ)*((L*k*base:ℕ):ℝ) := by
    rw [Nat.cast_add] at hZ
    linarith only [hZ,mul_le_mul_of_nonneg_right hζHalf (Nat.cast_nonneg z : (0:ℝ) ≤ z)]
  have hDegrees' : ((K*l*r+priorLoss:ℕ):ℝ) ≤ (D/(k:ℝ))*((L*k*base:ℕ):ℝ) := by
    refine hDegrees.trans ?_
    have hLe : (base:ℝ) ≤ (L:ℝ)*base := by exact_mod_cast Nat.le_mul_of_pos_left base hL
    calc
      _ ≤ D*((L:ℝ)*base) := mul_le_mul_of_nonneg_left hLe hD
      _ = _ := by push_cast; field_simp
  have hZE : ζ*(32*A*C) ≤ E :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hZR : ζ*(4*A*F) ≤ R :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  have hAΛ : (Λ:ℝ) ≤ A := by dsimp [A]; linarith
  have hCut : 16*A*D/E ≤ (k:ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈16*A*D/E⌉₊ ≤ k from (le_max_right _ _).trans hkMin))
  have hDA := (div_le_iff₀ hE).mp hCut
  have hRate : A*(D/(k:ℝ)) ≤ E/16 := calc
    _ = A*D/(k:ℝ) := (mul_div_assoc _ _ _).symm
    _ ≤ E/16 := (div_le_iff₀ hkR).mpr (by linarith only [hDA])
  have hEndpoint : (Λ:ℝ)*(C*(2*ζ)+D/(k:ℝ)) < E/4 := by
    have h := mul_le_mul_of_nonneg_right hAΛ (show 0 ≤ C*(2*ζ)+D/(k:ℝ) by positivity)
    linarith only [h,hZE,hRate,hE]
  have hRouting : (Λ:ℝ)*(2*ζ)*F < R := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAΛ
      (show 0 ≤ 2*ζ by positivity)) hF.le
    linarith only [h,hZR,hR]
  exact wound_factor_counts_from_common_density L k base m K l b c z Λ r priorLoss
    α θ σ μ (2*ζ) (D/(k:ℝ)) hWinding hCell hSlots hb hk hm hc hα.le hθ.le hσ hμ
    (by positivity) hχ hSize hDegrees' hEndpoint hRouting

end OverfullWork.DirectedRobustExpansion
