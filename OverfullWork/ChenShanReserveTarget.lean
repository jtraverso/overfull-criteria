module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

/-- The target margin in Lemma 4.12 deviates from the uncorrected
margin by at most four times the relative error in the edge counts
and vertex degrees. The same bound for the other shore follows
by exchanging the degrees. -/
theorem reserve_target_deviation (e average totalIn totalOut μ θ degree oppositeDegree : ℝ)
    (he : 0 < e) (hμ : 0 ≤ μ) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/4)
    (hdegree : 0 ≤ degree)
    (hAverage : |average-e| ≤ θ*e) (hIn : |totalIn-e| ≤ θ*e)
    (hOut : |totalOut-e| ≤ θ*e)
    (hDegree : |oppositeDegree-degree| ≤ θ*degree) :
    |μ * average * (degree+oppositeDegree)/(totalIn+totalOut) - μ*degree|
      ≤ 4*μ*θ*degree := by
  have hθe := mul_le_mul_of_nonneg_right hθ' he.le
  have hAv := abs_le.mp hAverage
  have hI := abs_le.mp hIn
  have hO := abs_le.mp hOut
  have hAverageNN : 0 ≤ average := by linarith only [hAv.1,hθe,he]
  have hAverageUpper : average ≤ 5/4*e := by linarith only [hAv.2,hθe]
  have hTotalLower : 3/2*e ≤ totalIn+totalOut := by linarith only [hI.1,hO.1,hθe]
  have hTotalPos : 0 < totalIn+totalOut := by linarith only [hTotalLower,he]
  have hCounts : |2*average-(totalIn+totalOut)| ≤ 4*θ*e := by
    apply abs_le.mpr
    constructor <;> linarith only [hAv.1,hAv.2,hI.1,hI.2,hO.1,hO.2]
  rw [show μ * average * (degree+oppositeDegree)/(totalIn+totalOut) - μ*degree =
    (μ * (average*(oppositeDegree-degree) + (2*average-(totalIn+totalOut))*degree)) /
      (totalIn+totalOut) by field_simp [hTotalPos.ne']; ring]
  rw [abs_div,abs_of_pos hTotalPos,abs_mul,abs_of_nonneg hμ]
  apply (div_le_iff₀ hTotalPos).mpr
  have hTerm₁ : |average*(oppositeDegree-degree)| ≤ (5/4*e)*(θ*degree) := by
    rw [abs_mul,abs_of_nonneg hAverageNN]
    exact mul_le_mul hAverageUpper hDegree (abs_nonneg _) (by positivity)
  have hTerm₂ : |(2*average-(totalIn+totalOut))*degree| ≤ (4*θ*e)*degree := by
    rw [abs_mul,abs_of_nonneg hdegree]
    exact mul_le_mul_of_nonneg_right hCounts hdegree
  have hNumerator : |average*(oppositeDegree-degree) + (2*average-(totalIn+totalOut))*degree|
      ≤ 6*θ*e*degree := by
    have hTri := abs_add_le (average*(oppositeDegree-degree)) ((2*average-(totalIn+totalOut))*degree)
    nlinarith only [hTerm₁,hTerm₂,hTri,mul_nonneg (mul_nonneg hθ he.le) hdegree]
  calc
    _ ≤ μ * (6*θ*e*degree) := mul_le_mul_of_nonneg_left hNumerator hμ
    _ = (4*μ*θ*degree) * (3/2*e) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hTotalLower (by positivity)

end OverfullWork.ChenShan
