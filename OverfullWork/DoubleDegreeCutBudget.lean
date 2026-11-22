module

public import OverfullWork.ExponentialSigning

@[expose] public section


/-! A graph-independent threshold pays for both semidegree rows at every
vertex and all pairs of vertex subsets in a directed edge selection. -/
namespace OverfullWork.DoubleDegreeCutBudget
open Real
set_option maxHeartbeats 14000000

theorem eventual_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ,∀ n : ℕ,N ≤ n →
      4*(n:ℝ)*exp (-(ε^2*(n:ℝ))/8)+
        2*(4:ℝ)^n*exp (-(ε^2*(n:ℝ)^2)/8) < 1 := by
  let c := ε^2/8
  have hc : 0 < c := by dsimp only [c];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (max (8/c) (32/c^2)))
  refine ⟨N,?_⟩
  intro n hn
  have hNR : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1:ℝ) < n := (le_max_left _ _).trans_lt (hN.trans_le hNR)
  have hn8 : 8/c < (n:ℝ) := (le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt (hN.trans_le hNR))
  have hn16 : 32/c^2 < (n:ℝ) := (le_max_right _ _).trans_lt
    ((le_max_right _ _).trans_lt (hN.trans_le hNR))
  have hcn : (8:ℝ) < c*n := by
    have hh := (div_lt_iff₀ hc).mp hn8
    nlinarith only [hh]
  have hcn2 : (32:ℝ) < c^2*n := by
    have hh := (div_lt_iff₀ (sq_pos_of_pos hc)).mp hn16
    nlinarith only [hh]
  have hExp := Real.pow_div_factorial_le_exp (c*n) (by positivity : (0:ℝ) ≤ c*n) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one] at hExp
  have hQuad := mul_lt_mul_of_pos_right hcn2 (show (0:ℝ) < n by linarith)
  have hExpLarge : 16*(n:ℝ) < exp (c*n) := by nlinarith only [hExp,hQuad]
  have hDegree : 4*(n:ℝ)*exp (-(c*n)) < 1/4 := by
    rw [exp_neg,←div_eq_mul_inv,div_lt_iff₀ (exp_pos _)]
    nlinarith only [hExpLarge]
  have hExpOne : (2:ℝ) ≤ exp 1 := by have hh := add_one_le_exp (1:ℝ);norm_num at hh ⊢;exact hh
  have hExpTwo : (4:ℝ) ≤ exp 2 := by
    have hh := mul_le_mul hExpOne hExpOne (by norm_num : (0:ℝ) ≤ 2) (exp_pos 1).le
    rw [←exp_add] at hh
    norm_num at hh ⊢
    exact hh
  have hFour : (4:ℝ)^n ≤ exp (2*(n:ℝ)) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hExpTwo n
    simpa only [←exp_nat_mul,mul_comm] using hh
  have hCut : (4:ℝ)^n*exp (-(c*(n:ℝ)^2)) ≤ exp (-2) := by
    calc
      _ ≤ exp (2*(n:ℝ))*exp (-(c*(n:ℝ)^2)) :=
        mul_le_mul_of_nonneg_right hFour (exp_pos _).le
      _ = exp (2*(n:ℝ)-c*(n:ℝ)^2) := by rw [←exp_add];rfl
      _ ≤ _ := by
        apply exp_le_exp.mpr
        have hh := mul_lt_mul_of_pos_right hcn (show (0:ℝ) < n by linarith)
        nlinarith only [hh,hn1]
  have hThree : (3:ℝ)*exp (-2) ≤ 1 := by
    have hh := add_one_le_exp (2:ℝ)
    rw [exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
    linarith only [hh]
  have hLinear : -(ε^2*(n:ℝ))/8=-(c*n) := by dsimp only [c];ring
  have hQuadratic : -(ε^2*(n:ℝ)^2)/8=-(c*(n:ℝ)^2) := by dsimp only [c];ring
  rw [hLinear,hQuadratic]
  nlinarith only [hDegree,hCut,hThree]

end OverfullWork.DoubleDegreeCutBudget
