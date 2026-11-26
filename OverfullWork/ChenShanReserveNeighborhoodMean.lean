module

public import OverfullWork.ChenShanReserveDegreeSampling
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

/-- The deterministic mean comparison in (R4). A common neighborhood
occupying at least half plus 20η of the candidates still occupies more
than half plus 19η in expectation after weighting the candidates. -/
theorem reserve_neighborhood_mean_ratio {I : Type*} [Fintype I]
    (p : I → ℝ) (S T : Finset I) {μ η : ℝ}
    (hS : S.Nonempty) (hT : T ⊆ S)
    (hμ : 0 < μ) (hη : 0 < η) (hηsmall : η ≤ 1/40)
    (hP : ∀ e ∈ S, |p e-μ| ≤ μ*η/100)
    (hCount : (1/2+20*η)*(S.card : ℝ) ≤ T.card) :
    (1/2+19*η)*mean p S < mean p T := by
  have hPointLo (e : I) (he : e ∈ S) : μ*(1-η/100) ≤ p e := by
    linarith only [(abs_le.mp (hP e he)).1]
  have hPointHi (e : I) (he : e ∈ S) : p e ≤ μ*(1+η/100) := by
    linarith only [(abs_le.mp (hP e he)).2]
  have hLoWeight : 0 ≤ μ*(1-η/100) := by
    apply mul_nonneg hμ.le
    linarith only [hηsmall]
  have hLo : μ*(1-η/100)*(T.card : ℝ) ≤ mean p T := by
    unfold mean
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun e he => hPointLo e (hT he)
  have hHi : mean p S ≤ μ*(1+η/100)*(S.card : ℝ) := by
    unfold mean
    rw [mul_comm (μ*(1+η/100)), ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hPointHi
  have hDiff : (1/2+19*η)*(1+η/100) < (1-η/100)*(1/2+20*η) := by
    have hP' := mul_le_mul_of_nonneg_left hηsmall hη.le
    nlinarith only [hP',hη]
  have hCard : (0:ℝ) < S.card := by exact_mod_cast hS.card_pos
  calc
    _ ≤ (1/2+19*η)*(μ*(1+η/100)*(S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hHi (by positivity)
    _ = ((1/2+19*η)*(1+η/100))*(μ*(S.card : ℝ)) := by ring
    _ < ((1-η/100)*(1/2+20*η))*(μ*(S.card : ℝ)) :=
      mul_lt_mul_of_pos_right hDiff (mul_pos hμ hCard)
    _ = (μ*(1-η/100))*((1/2+20*η)*(S.card : ℝ)) := by ring
    _ ≤ μ*(1-η/100)*(T.card : ℝ) := mul_le_mul_of_nonneg_left hCount hLoWeight
    _ ≤ _ := hLo


/-- Intersecting a large neighborhood with a nearly complete one loses
at most the missing neighbors. This is the deterministic input to (R3). -/
theorem reserve_common_neighborhood_lower {I : Type*}
    (S T U : Finset I) (hS : S ⊆ U) {a d : ℝ}
    (hDegree : a ≤ (S.card : ℝ)) (hMissing : ((U \ T).card : ℝ) ≤ d) :
    a-d ≤ ((S ∩ T).card : ℝ) := by
  have hDiff : S \ (S ∩ T) ⊆ U \ T := by
    intro v hv
    obtain ⟨hvS,hvNot⟩ := mem_sdiff.mp hv
    exact mem_sdiff.mpr ⟨hS hvS,fun hvT => hvNot (mem_inter.mpr ⟨hvS,hvT⟩)⟩
  have hSplit : (((S \ (S ∩ T)).card : ℝ)) + ((S ∩ T).card : ℝ) = S.card := by
    exact_mod_cast card_sdiff_add_card_eq_card (inter_subset_left : S ∩ T ⊆ S)
  have hCard : (((S \ (S ∩ T)).card : ℝ)) ≤ ((U \ T).card : ℝ) := by
    exact_mod_cast card_le_card hDiff
  linarith only [hDegree,hMissing,hSplit,hCard]


/-- Absolute concentration with error at most η times the expected
total count transfers the mean margin to the sampled neighborhood. -/
theorem reserve_sample_neighborhood_ratio {μ ν x y D η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1/40) (hμ : 0 ≤ μ)
    (hD : 0 ≤ D) (hD' : D ≤ η*μ)
    (hMean : (1/2+19*η)*μ ≤ ν)
    (hCount : |x-μ| ≤ D) (hGood : |y-ν| ≤ D) :
    (1/2+8*η)*x ≤ y := by
  have hc : 0 ≤ 1/2+8*η := by positivity
  have hc' : 1/2+8*η ≤ 1 := by linarith only [hηsmall]
  have hErr := mul_le_of_le_one_left hD hc'
  have hημ := mul_nonneg hη hμ
  have hx := mul_le_mul_of_nonneg_left
    (show x ≤ μ+D by linarith only [(abs_le.mp hCount).2]) hc
  linarith only [hx,hErr,hημ,hD',hMean,(abs_le.mp hGood).1]


/-- A neighborhood count with a mean in the range required in (R2)
satisfies the paper's bounds after an absolute error of μρn/4. -/
theorem reserve_sample_neighborhood_size {μ ρ n expected actual : ℝ}
    (hScale : 0 ≤ μ*ρ*n)
    (hLower : μ*ρ*n/2 ≤ expected) (hUpper : expected ≤ 3*μ*ρ*n)
    (hCount : |actual-expected| ≤ μ*ρ*n/4) :
    μ*ρ*n/4 ≤ actual ∧ actual ≤ 4*μ*ρ*n :=
  ⟨by linarith only [hLower,(abs_le.mp hCount).1],
    by linarith only [hScale,hUpper,(abs_le.mp hCount).2]⟩

/-- A count restricted to the next protected prefix has the upper bound
in (R5) once its probabilities are bounded by 3μ. -/
theorem reserve_sample_protected_prefix_count {I : Type*} [Fintype I]
    (p : I → ℝ) (S : Finset I) (sample : I → Bool) {μ n ξ : ℝ}
    (hP : ∀ e ∈ S, p e ≤ 3*μ)
    (hSample : |count S sample-mean p S| ≤ ξ*n) :
    count S sample ≤ 3*μ*(S.card : ℝ)+ξ*n := by
  have hMean : mean p S ≤ 3*μ*(S.card : ℝ) := by
    unfold mean
    rw [mul_comm (3*μ), ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hP
  linarith only [hMean,(abs_le.mp hSample).2]

end OverfullWork.ChenShan
