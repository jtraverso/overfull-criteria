module

public import OverfullWork.ChenShanCoverDownHierarchy
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

/-- Choose the scalar parameters in the order of (4.18). The inequalities
hold for every later density error between zero and the discrepancy
parameter. The packing tolerance is fixed before choosing rho. -/
theorem exists_cover_down_scalar_parameters {η cap : ℝ}
    (hη : 0 < η) (hηhalf : η ≤ 1/2) (hcap : 0 < cap) :
    ∃ η₀ ρ μ ζ ξ : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/80 ∧ 40*η₀ ≤ η ∧
      0 < ρ ∧ ρ ≤ 1/4 ∧ ρ ≤ min η (1/2)/128 ∧
      0 < μ ∧ 10*μ ≤ 1 ∧ 0 < ζ ∧ 0 < ξ ∧ ξ ≤ 1 ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ξ →
        let δ := 4*ε+10*ξ+20*μ/ρ
        0 < δ ∧ CoverDownScalarBounds ρ η η₀ μ ζ δ ξ cap := by
  let η₀ := η/100
  have hη₀ : 0 < η₀ := by positivity
  let a := min (η/4) (min (1/32) (cap/4))
  have ha : 0 < a := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  obtain ⟨ρ,hρ,hρlt⟩ := exists_between
    (show 0 < min (min η (1/2)/128) (min (1/4) (min (a/4) (η₀/72))) from
      lt_min (div_pos (lt_min hη (by norm_num)) (by norm_num))
        (lt_min (by norm_num) (lt_min (by positivity) (by positivity))))
  have hρs := lt_min_iff.mp hρlt
  have hρs' := lt_min_iff.mp hρs.2
  have hρabs := hρs.1.le
  have hρcap := hρs'.1.le
  have hρa := (lt_min_iff.mp hρs'.2).1.le
  have hρprot := (lt_min_iff.mp hρs'.2).2.le
  let w := 40/ρ
  let c := (8/η)*(16*w/ρ)
  let t := η₀*ρ/(8*120000)
  have hw : 0 < w := by positivity
  have hc : 0 < c := by positivity
  have ht : 0 < t := by positivity
  obtain ⟨μ,hμ,hμlt⟩ := exists_between
    (show 0 < min (1/10) (min (a/(w+10)) (min (η*ρ/(18*w)) (min ((η₀/100)/c) (t^2)))) from
      lt_min (by norm_num) (lt_min (by positivity)
        (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))
  have hμs := lt_min_iff.mp hμlt
  have hμa := lt_min_iff.mp hμs.2
  have hμd := lt_min_iff.mp hμa.2
  have hμc := lt_min_iff.mp hμd.2
  have hμcap : 10*μ ≤ 1 := by linarith only [hμs.1]
  have hA : μ*(w+10) ≤ a := (le_div_iff₀ (by positivity : 0 < w+10)).mp hμa.1.le
  have hD : μ*(18*w) ≤ η*ρ := (le_div_iff₀ (by positivity : 0 < 18*w)).mp hμd.1.le
  have hC : μ*c ≤ η₀/100 := (le_div_iff₀ hc).mp hμc.1.le
  have hSqrt : Real.sqrt μ ≤ t := (Real.sqrt_le_iff).mpr ⟨ht.le,hμc.2.le⟩
  obtain ⟨ζ,hζ,hζlt⟩ := exists_between
    (show 0 < min (μ*ρ/8) (min (μ^2*ρ/40) (min (10*μ) ((η₀*μ*ρ/4)/(3/2+η₀)))) from
      lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hζs := lt_min_iff.mp hζlt
  have hζd := lt_min_iff.mp hζs.2
  have hζc := lt_min_iff.mp hζd.2
  have hζprot : ζ*(3/2+η₀) ≤ η₀*μ*ρ/4 :=
    (le_div_iff₀ (by positivity : 0 < 3/2+η₀)).mp hζc.2.le
  let q := min (min (η/64) (1/128)) (min (cap/10) (ζ/10))
  have hq : 0 < q := lt_min (lt_min (by positivity) (by norm_num))
    (lt_min (by positivity) (by positivity))
  obtain ⟨ξ,hξ,hξlt⟩ := exists_between
    (show 0 < min 1 (min (η₀*μ*ρ/4) (min ((20*μ/ρ)/14) (q^2/4))) from
      lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hξs := lt_min_iff.mp hξlt
  have hξp := lt_min_iff.mp hξs.2
  have hξq := lt_min_iff.mp hξp.2
  have hSq : Real.sqrt (4*ξ) ≤ q := by
    refine (Real.sqrt_le_iff).mpr ⟨hq.le,?_⟩
    linarith only [hξq.2]
  have hRepairCap : Real.sqrt (4*ξ) ≤ cap/10 := hSq.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRepairBudget : Real.sqrt (4*ξ) ≤ ζ/10 := hSq.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨η₀,ρ,μ,ζ,ξ,hη₀,?_,?_,hρ,hρcap,hρabs,hμ,hμcap,hζ,hξ,hξs.1.le,?_⟩
  · dsimp only [η₀]
    linarith only [hηhalf]
  · dsimp only [η₀]
    linarith only [hη]
  intro ε hε hεξ δ
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hLinear : δ ≤ w*μ := by
    calc
      δ ≤ 20*μ/ρ+20*μ/ρ := by
        dsimp only [δ]
        linarith only [hξq.1,hεξ]
      _ = w*μ := by dsimp only [w]; ring
  have hSum : δ+4*ρ+10*μ ≤ 2*a := by linarith only [hLinear,hA,hρa]
  have hDensity := mul_le_mul_of_nonneg_left hLinear (show 0 ≤ (18:ℝ) by norm_num)
  have hRatio := mul_le_mul_of_nonneg_right hLinear (show 0 ≤ (8/η)*(16/ρ) by positivity)
  have hcEq : c = (8/η)*(16/ρ)*w := by dsimp only [c]; ring
  have hRatioEq : δ*((8/η)*(16/ρ)) = (8/η)*(16*δ/ρ) := by ring
  have hBudget : (120000:ℝ)*Real.sqrt μ ≤ η₀*ρ/8 := by
    linarith only [show Real.sqrt μ ≤ η₀*ρ/(8*120000) from hSqrt]
  have hBudget' := mul_le_mul_of_nonneg_right hBudget hμ.le
  refine ⟨hδ,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · linarith only [hDensity,hD]
  · rw [hcEq] at hC
    rw [← hRatioEq]
    linarith only [hRatio,hC]
  · linarith only [hξp.1,mul_nonneg hη₀.le (mul_nonneg hμ.le hρ.le)]
  · linarith only [hSum,show a ≤ η/4 from min_le_left _ _]
  · linarith only [hSum,show a ≤ 1/32 from (min_le_right _ _).trans (min_le_left _ _)]
  · have h := hSq.trans (min_le_left _ _)
    convert h using 1 <;> ring
  · linarith only [hSum,hRepairCap,show a ≤ cap/4 from
      (min_le_right _ _).trans (min_le_right _ _)]
  · linarith only [hRepairBudget]
  · rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hμ,Real.rpow_one,← Real.sqrt_eq_rpow]
    linarith only [hBudget']
  · exact hζs.1.le
  · linarith only [hζd.1]
  · exact hζc.1.le
  · have hh := mul_le_mul_of_nonneg_right hρprot (show 0 ≤ 36*μ*ρ by positivity)
    have hh' : 0 ≤ η₀*μ*ρ := by positivity
    linarith only [hh,hh',hξp.1,hζprot]

end OverfullWork.ChenShan
