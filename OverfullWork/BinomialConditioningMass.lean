module

public import OverfullWork.BiasedExponentialSigning
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section


/-! The binomial mass at an integral mean is at least 1/(n+1).
This pays for conditioning independent vertex choices to an exact size.
The proof uses the adjacent-mass identity and a finite sum, with no
assumed binomial mode or concentration theorem. -/
namespace OverfullWork.BinomialConditioningMass
open Finset Real
set_option maxHeartbeats 14000000

def term (n : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (n.choose j:ℝ)*p^j*(1-p)^(n-j)

theorem term_nonneg (n j : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ term n p j := by unfold term;positivity

theorem adjacent_identity (n j : ℕ) (p : ℝ) (hj : j < n) :
    ((j:ℝ)+1)*(1-p)*term n p (j+1)=((n-j:ℕ):ℝ)*p*term n p j := by
  have hChoose : (n.choose (j+1):ℝ)*((j:ℝ)+1)=(n.choose j:ℝ)*((n-j:ℕ):ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  have hDiff : n-j=(n-(j+1))+1 := by omega
  unfold term
  calc
    _ = ((n.choose (j+1):ℝ)*((j:ℝ)+1))*p^(j+1)*(1-p)^(n-j) := by
      rw [hDiff,pow_succ (1-p)]
      ring
    _ = ((n.choose j:ℝ)*((n-j:ℕ):ℝ))*p^(j+1)*(1-p)^(n-j) := by rw [hChoose]
    _ = _ := by rw [pow_succ p];ring

theorem maximal_at_integral_mean (n k : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hMean : (n:ℝ)*p=(k:ℝ)) (hk : k ≤ n) :
    ∀ j : ℕ,j ≤ n → term n p j ≤ term n p k := by
  have hUp : ∀ j : ℕ,j < k → term n p j ≤ term n p (j+1) := by
    intro j hj
    have hjn : j < n := hj.trans_le hk
    have hSub : ((n-j:ℕ):ℝ)=(n:ℝ)-(j:ℝ) := Nat.cast_sub hjn.le
    have hjR : (j:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast hj
    have hCoeff : ((j:ℝ)+1)*(1-p) ≤ ((n-j:ℕ):ℝ)*p := by
      rw [hSub]
      nlinarith only [hMean,hjR,hp.le]
    have hPay := mul_le_mul_of_nonneg_right hCoeff (term_nonneg n j p hp.le hp1.le)
    have hA : 0 < ((j:ℝ)+1)*(1-p) := mul_pos (by positivity) (sub_pos.mpr hp1)
    apply (mul_le_mul_iff_right₀ hA).mp
    exact hPay.trans_eq (adjacent_identity n j p hjn).symm
  have hDown : ∀ j : ℕ,k ≤ j → j < n → term n p (j+1) ≤ term n p j := by
    intro j hj hjn
    have hSub : ((n-j:ℕ):ℝ)=(n:ℝ)-(j:ℝ) := Nat.cast_sub hjn.le
    have hjR : (k:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
    have hCoeff : ((n-j:ℕ):ℝ)*p ≤ ((j:ℝ)+1)*(1-p) := by
      rw [hSub]
      nlinarith only [hMean,hjR,hp1.le]
    have hPay := mul_le_mul_of_nonneg_right hCoeff (term_nonneg n j p hp.le hp1.le)
    have hA : 0 < ((j:ℝ)+1)*(1-p) := mul_pos (by positivity) (sub_pos.mpr hp1)
    apply (mul_le_mul_iff_right₀ hA).mp
    exact (adjacent_identity n j p hjn).le.trans hPay
  have hLow : ∀ j : ℕ,j ≤ k → term n p j ≤ term n p k := by
    intro j hj
    exact Nat.decreasingInduction (motive:=fun i _ => term n p i ≤ term n p k)
      (fun i hi ih => (hUp i hi).trans ih) le_rfl hj
  have hHigh : ∀ j : ℕ,k ≤ j → j ≤ n → term n p j ≤ term n p k := by
    intro j hj
    induction j,hj using Nat.le_induction with
    | base => intro _;exact le_rfl
    | succ j hj ih =>
      intro hjn
      exact (hDown j hj (by omega)).trans (ih (by omega))
  intro j hjn
  rcases le_total j k with h|h
  · exact hLow j h
  · exact hHigh j h hjn

theorem sum_terms (n : ℕ) (p : ℝ) : (∑ j ∈ range (n+1),term n p j)=1 := by
  have hh := add_pow p (1-p) n
  rw [show p+(1-p)=1 by ring,one_pow] at hh
  rw [hh]
  apply sum_congr rfl
  intro j _
  unfold term
  ring

theorem mass_at_mean_lower_bound (n k : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hMean : (n:ℝ)*p=(k:ℝ)) (hk : k ≤ n) :
    1/((n:ℝ)+1) ≤ term n p k := by
  have hh := sum_le_sum (s:=range (n+1)) fun j hj =>
    maximal_at_integral_mean n k p hp hp1 hMean hk j (by have hh := mem_range.mp hj;omega)
  rw [sum_terms] at hh
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at hh
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)).mpr
  nlinarith only [hh]

end OverfullWork.BinomialConditioningMass
