module

public import OverfullWork.InitialTwoSidedRobustData
public import OverfullWork.TwoSidedRobustSampling

@[expose] public section


/-! The robust parameter is fixed before the sampling fraction. Only
the regularity tolerance and eventual order threshold depend on it. -/
namespace OverfullWork.BipartiteRegularitySource
open scoped Classical
set_option maxHeartbeats 18000000

theorem exists_sampling_regular_error (ν c θ d : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hd : 0 < d) :
    ∃ ε : ℝ,0 < ε ∧ ε ≤ θ/6 ∧ ε ≤ θ^4/1024 ∧
      12*ε/θ ≤ c/2 ∧ 4*(12*ε/θ)/c ≤ (ν/2)/128 ∧
      4*(12*ε/θ)/c+d/4 ≤ (d-ε)-12*ε/θ := by
  let ε := min (θ/12) (min (θ^4/1024) (min (ν*θ*c/24576) (θ*c*d/384)))
  have hε : 0 < ε := by dsimp only [ε];positivity
  have hA : ε ≤ θ/12 := min_le_left _ _
  have hB : ε ≤ θ^4/1024 := (min_le_right _ _).trans (min_le_left _ _)
  have hC : ε ≤ ν*θ*c/24576 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hD : ε ≤ θ*c*d/384 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hE0 : 12*ε/θ ≤ ν*c/2048 := by
    apply (div_le_iff₀ hθ).mpr
    nlinarith only [hC]
  have hSample : 4*(12*ε/θ)/c ≤ ν/512 := by
    apply (div_le_iff₀ hc).mpr
    nlinarith only [hE0]
  have hSampleD : 4*(12*ε/θ)/c ≤ d/8 := by
    have hBound : 48*ε/(θ*c) ≤ d/8 := by
      apply (div_le_iff₀ (mul_pos hθ hc)).mpr
      nlinarith only [hD]
    convert hBound using 1 <;> ring
  have hEpsE0 : ε ≤ 12*ε/θ := by
    apply (le_div_iff₀ hθ).mpr
    have hh := mul_le_mul_of_nonneg_left hθ1 hε.le
    nlinarith only [hh,hε]
  have hE0Sample : 12*ε/θ ≤ 4*(12*ε/θ)/c := by
    apply (le_div_iff₀ hc).mpr
    have hh := mul_le_mul_of_nonneg_left hc1 (show 0 ≤ 12*ε/θ by positivity)
    have hp : 0 ≤ 12*ε/θ := by positivity
    linarith only [hh,hp]
  have hE0C : 12*ε/θ ≤ c/2 := by
    have hh := mul_le_mul_of_nonneg_right hν1 hc.le
    nlinarith only [hE0,hh,hc]
  refine ⟨ε,hε,by linarith only [hA,hθ],hB,hE0C,?_,?_⟩
  · linarith only [hSample,hν]
  · linarith only [hEpsE0,hE0Sample,hSampleD,hd]

end OverfullWork.BipartiteRegularitySource
