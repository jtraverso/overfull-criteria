module

public import OverfullWork.UniformSamplingProfiles

@[expose] public section


/-! A prechosen order threshold makes simultaneous fixed-size profile
failure at most n^(-2), for any linearly bounded profile family. -/
namespace OverfullWork.UniformSamplingBudget
open Finset Real
set_option maxHeartbeats 18000000

theorem eventual_bound (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N : ℕ,∀ n : ℕ,N ≤ n →
      2*C*(n:ℝ)*((n:ℝ)+1)*exp (-ε^2*(n:ℝ)/2) ≤ 1/(n:ℝ)^2 := by
  let c := ε^2/2
  have hc : 0 < c := by dsimp only [c];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (960*C/c^5))
  refine ⟨N,?_⟩
  intro n hn
  have hNR : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1:ℝ) < n := (le_max_left _ _).trans_lt (hN.trans_le hNR)
  have hOrder : 960*C < c^5*(n:ℝ) := by
    have hh := (le_max_right 1 (960*C/c^5)).trans_lt (hN.trans_le hNR)
    have hh' := (div_lt_iff₀ (pow_pos hc 5)).mp hh
    nlinarith only [hh']
  have hScale := mul_lt_mul_of_pos_right hOrder (pow_pos (show (0:ℝ) < n by linarith only [hn1]) 4)
  have hExp := Real.pow_div_factorial_le_exp (c*n) (by positivity : (0:ℝ) ≤ c*n) 5
  norm_num only [Nat.factorial,Nat.cast_ofNat,Nat.cast_one] at hExp
  have hExpLarge : 4*C*(n:ℝ)^4 < exp (c*n) := by
    have hNonneg := mul_nonneg hC.le (pow_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) 4)
    nlinarith only [hScale,hExp,hNonneg]
  have hPoly : 2*C*(n:ℝ)*((n:ℝ)+1)*(n:ℝ)^2 ≤ 4*C*(n:ℝ)^4 := by
    have hh := mul_le_mul_of_nonneg_left (show (n:ℝ)+1 ≤ 2*(n:ℝ) by linarith only [hn1])
      (show (0:ℝ) ≤ 2*C*(n:ℝ)^3 by positivity)
    nlinarith only [hh]
  have hBound : 2*C*(n:ℝ)*((n:ℝ)+1) ≤ exp (c*n)/(n:ℝ)^2 := by
    apply (le_div_iff₀ (pow_pos (show (0:ℝ) < n by linarith only [hn1]) 2)).mpr
    exact hPoly.trans hExpLarge.le
  have hFinal := mul_le_mul_of_nonneg_right hBound (exp_pos (-(c*n))).le
  rw [exp_neg] at hFinal
  have hCancel : exp (c*n)/(n:ℝ)^2*(exp (c*n))⁻¹=1/(n:ℝ)^2 := by field_simp
  rw [hCancel] at hFinal
  have hArg : -ε^2*(n:ℝ)/2=-(c*n) := by dsimp only [c];ring
  rw [hArg]
  simpa only [exp_neg] using hFinal

end OverfullWork.UniformSamplingBudget

namespace OverfullWork.UniformSubsetSampling
open Finset Real
open scoped Classical
universe u v
set_option maxHeartbeats 18000000

theorem exists_uniform_profile_threshold (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      (A : I → Finset V) (k : ℕ),N ≤ Fintype.card V → k ≤ Fintype.card V →
      (Fintype.card I:ℝ) ≤ C*(Fintype.card V:ℝ) →
      probability k (fun X => ∃ i,ε*(Fintype.card V:ℝ) ≤
        |((X ∩ A i).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*((A i).card:ℝ)|) ≤
        1/(Fintype.card V:ℝ)^2 := by
  obtain ⟨N,hN⟩ := UniformSamplingBudget.eventual_bound C ε hC hε
  refine ⟨max N 2,?_⟩
  intro V _ I _ A k hn hk hI
  have hTail := profiles_tail A k hk ε hε
  have hScale := mul_le_mul_of_nonneg_right hI
    (show (0:ℝ) ≤ 2*((Fintype.card V:ℝ)+1)*exp (-ε^2*(Fintype.card V:ℝ)/2) by positivity)
  have hBound := hN (Fintype.card V) (by omega)
  nlinarith only [hTail,hScale,hBound]

end OverfullWork.UniformSubsetSampling
