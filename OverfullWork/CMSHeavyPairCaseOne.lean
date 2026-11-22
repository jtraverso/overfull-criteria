module

public import OverfullWork.CMSHeavyPairFactorization
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


/-! The heavy multiplicity threshold and the ranked degree profiles
in the source statement of CMS §5.2, Case 1. -/
namespace OverfullWork.HeavyPairPeeling
open Finset SimpleGraph MultiGraph HeavyPairBoundary RobustExpansion
open scoped Classical
universe u

/-- Case 1 of CMS Theorem 4.2. The ranks are zero-based and only the
vertices outside the heavy pair need the two ordinary degree profiles. -/
theorem cms_theorem_4_2_case_one
    (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ → ∃ ηMax : ℝ, 0 < ηMax ∧
      ∀ η : ℝ, 0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (M : MultiGraph V) (d : ℕ) (a b : V) (rank : V → ℕ), a ≠ b →
          N ≤ Fintype.card V → Even (Fintype.card V) →
          M.IsRegularOfDegree d → ¬ M.HasOverfullSubset d →
          α*(Fintype.card V:ℝ) ≤ (d:ℝ) → IsRealRobust M.supportGraph ν τ →
          (d:ℝ)-η^((1:ℝ)/7)*(Fintype.card V:ℝ) ≤ (M.mult s(a,b):ℝ) →
          (∀ x : outside a b, 2 ≤ rank x.val) →
          (∀ x : outside a b, ((rank x.val-1:ℕ):ℝ)/(rank x.val:ℝ)*(d:ℝ)-
            6*η*(Fintype.card V:ℝ) ≤ (M.supportGraph.degree x.val:ℝ)) →
          (∀ x : outside a b, (d:ℝ)-(M.mult s(a,x.val):ℝ)-6*η*(Fintype.card V:ℝ) ≤
            (M.supportGraph.degree x.val:ℝ)) →
          Nonempty (M.EdgeColoring d) := by
  obtain ⟨τ,hτ,hFactor⟩ := cms_heavy_pair_colourable.{u} α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨η₀,hη₀,hN⟩ := hFactor ν hν hντ
  let rate := min ν α/32
  have hRate : 0 < rate := div_pos (lt_min hν hα) (by norm_num)
  let ηMax := min η₀ (rate^7)
  have hηMax : 0 < ηMax := lt_min hη₀ (pow_pos hRate _)
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax'
  obtain ⟨N,hApply⟩ := hN η (hηMax'.trans (min_le_left _ _))
  have hηPow : η^((1:ℝ)/7) ≤ rate := by
    calc
      _ ≤ (rate^7)^((1:ℝ)/7) :=
        Real.rpow_le_rpow hη (hηMax'.trans (min_le_right _ _)) (by norm_num)
      _ = (rate^((7:ℕ):ℝ))^((1:ℝ)/7) := by rw [Real.rpow_natCast]
      _ = rate^(((7:ℕ):ℝ)*((1:ℝ)/7)) := (Real.rpow_mul hRate.le _ _).symm
      _ = rate := by norm_num
  refine ⟨N,?_⟩
  intro V _ _ M d a b rank hab hSize hEven hReg hNo hDegree hRob hHeavy hRank hProfile hLocal
  refine hApply M d a b hab hSize hEven hReg hNo hDegree hRob ?_ ?_ hLocal
  · have hBundle := M.mult_pair_le_degree a b
    rw [hReg a] at hBundle
    rw [Nat.cast_sub hBundle]
    change (d:ℝ)-(M.mult s(a,b):ℝ) ≤ rate*(Fintype.card V:ℝ)
    linarith only [hHeavy,mul_le_mul_of_nonneg_right hηPow (Nat.cast_nonneg (α := ℝ) (Fintype.card V))]
  · intro x
    have hRankTwo := hRank x
    have hr : 0 < (rank x.val:ℝ) := by exact_mod_cast (show 0 < rank x.val by omega)
    have hHalf : (1:ℝ)/2 ≤ ((rank x.val-1:ℕ):ℝ)/(rank x.val:ℝ) := by
      apply (le_div_iff₀ hr).mpr
      rw [Nat.cast_sub (by omega : 1 ≤ rank x.val),Nat.cast_one]
      have hRankR : (2:ℝ) ≤ (rank x.val:ℝ) := by exact_mod_cast hRankTwo
      linarith only [hRankR]
    nlinarith only [hProfile x,mul_le_mul_of_nonneg_right hHalf (Nat.cast_nonneg (α := ℝ) d)]

end OverfullWork.HeavyPairPeeling
