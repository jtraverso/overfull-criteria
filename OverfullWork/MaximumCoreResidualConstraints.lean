module

public import OverfullWork.MaximumCoreSafeRound

@[expose] public section


/-! The same top-three residual satisfies the input of joint normalization. -/
namespace OverfullWork.MaximumCoreThreeCrossRound
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun CleanedSourceVAL
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem Round.residual_constraints {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ}
    {c : Certificate G B K} {U : Finset V} (r : Round G c.set U)
    (hReady : IsReady G c.setᶜ) (hU : U ⊆ c.setᶜ) (hThree : U.card=3)
    (hTop : ∀ u ∈ U, ∀ v ∈ c.setᶜ, v ∉ U → G.degree v ≤ G.degree u)
    (hSmall : 4*(B+K+2)+1 ≤ G.maxDegree) :
    (∀ v ∈ c.setᶜ, (G\r.matching).degree v < (G\r.matching).maxDegree) ∧
    (∀ y ∈ c.setᶜ, ∀ z ∈ c.setᶜ, y ≠ z →
      (G\r.matching).degree y+(G\r.matching).degree z < (G\r.matching).maxDegree+2) := by
  let R := G\r.matching
  have hMax : R.maxDegree=G.maxDegree-1 := r.residual_maxDegree
  have hPoint : ∀ v ∈ c.setᶜ, R.degree v+(if v ∈ U then 1 else 0)=G.degree v := by
    intro v hv
    have hh : R.degree v+r.matching.degree v=G.degree v := by
      simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
    rwa [r.complementary_degrees v hv] at hh
  have hBudget : (∑ v ∈ c.setᶜ, G.degree v) ≤ G.maxDegree+B := by have hh := c.budget;omega
  have hOutside : ∀ v ∈ c.setᶜ, v ∉ U → 3*G.degree v ≤ G.maxDegree+B := by
    intro v hv hvU
    have hSum := sum_le_sum (s := U) (fun u hu => hTop u hu v hv hvU)
    have hSub := sum_le_sum_of_subset_of_nonneg hU (f := fun u => G.degree u) (fun _ _ _ => Nat.zero_le _)
    simp only [sum_const,smul_eq_mul,hThree] at hSum
    omega
  change (∀ v ∈ c.setᶜ, R.degree v < R.maxDegree) ∧
    (∀ y ∈ c.setᶜ, ∀ z ∈ c.setᶜ, y ≠ z → R.degree y+R.degree z < R.maxDegree+2)
  constructor
  · intro v hv
    have hh := hPoint v hv
    by_cases hvU : v ∈ U
    · rw [if_pos hvU] at hh
      have hOld := hReady.1 v hv
      omega
    · rw [if_neg hvU] at hh
      have hBound := hOutside v hv hvU
      omega
  · intro y hy z hz hyz
    have hY := hPoint y hy
    have hZ := hPoint z hz
    have hPair := c.light_pairs y hy z hz hyz
    by_cases hyU : y ∈ U
    · rw [if_pos hyU] at hY
      split_ifs at hZ <;> omega
    · by_cases hzU : z ∈ U
      · rw [if_neg hyU] at hY
        rw [if_pos hzU] at hZ
        omega
      · rw [if_neg hyU] at hY
        rw [if_neg hzU] at hZ
        have hBoundY := hOutside y hy hyU
        have hBoundZ := hOutside z hz hzU
        omega

end OverfullWork.MaximumCoreThreeCrossRound
