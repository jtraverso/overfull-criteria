module

public import OverfullWork.SigningMoments
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

@[expose] public section


/-! Finite exponential signing bounds, including exponentially many rows.
The squared coefficient sum is retained for each row, so sparse degree
rows need not pay the variance of all ambient edges. No probability or
signing-existence oracle is assumed.
-/
namespace OverfullWork.ExponentialSigning
open Finset Real SigningMoments
set_option maxHeartbeats 12000000

theorem exponential_sum_bound (m : ℕ) (a : Fin m → ℝ) (t : ℝ) :
    (∑ s : Fin m → Bool, exp (t*signedSum a s)) ≤
      (2:ℝ)^m*exp (t^2*(∑ i,a i^2)/2) := by
  induction m with
  | zero => simp [signedSum]
  | succ m ih =>
    have hFactor : (∑ s : Fin (m+1) → Bool, exp (t*signedSum a s))=
        (exp (t*a 0)+exp (-(t*a 0)))*
          (∑ s : Fin m → Bool,exp (t*signedSum (fun i => a i.succ) s)) := by
      rw [sum_signs_succ]
      simp only [signedSum_cons,Bool.false_eq_true,ite_true,ite_false,mul_add,mul_neg,exp_add]
      rw [sum_add_distrib,←mul_sum,←mul_sum,←add_mul]
    have hCosh : exp (t*a 0)+exp (-(t*a 0)) ≤ 2*exp ((t*a 0)^2/2) := by
      have hh := Real.cosh_le_exp_half_sq (t*a 0)
      rw [Real.cosh_eq] at hh
      linarith only [hh]
    rw [hFactor]
    calc
      _ ≤ (2*exp ((t*a 0)^2/2))*
          ((2:ℝ)^m*exp (t^2*(∑ i : Fin m,a i.succ^2)/2)) := by
        apply mul_le_mul hCosh (ih (fun i => a i.succ))
        · exact sum_nonneg fun _ _ => (exp_pos _).le
        · positivity
      _ = _ := by
        rw [Fin.sum_univ_succ,pow_succ]
        rw [show t^2*(a 0^2+∑ i : Fin m,a i.succ^2)/2=
          (t*a 0)^2/2+t^2*(∑ i : Fin m,a i.succ^2)/2 by ring,exp_add]
        ring

theorem shifted_exponential_sum_bound (m : ℕ) (a : Fin m → ℝ) (t b : ℝ) :
    (∑ s : Fin m → Bool,exp (t*(signedSum a s-b))) ≤
      (2:ℝ)^m*exp (t^2*(∑ i,a i^2)/2-t*b) := by
  have hh := mul_le_mul_of_nonneg_left (exponential_sum_bound m a t) (exp_pos (-t*b)).le
  calc
    _ = exp (-t*b)*(∑ s : Fin m → Bool,exp (t*signedSum a s)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro s _
      rw [←exp_add]
      congr 1
      ring
    _ ≤ _ := hh
    _ = _ := by
      rw [show exp (-t*b)*((2:ℝ)^m*exp (t^2*(∑ i,a i^2)/2))=
        (2:ℝ)^m*(exp (-t*b)*exp (t^2*(∑ i,a i^2)/2)) by ring,←exp_add]
      congr 2
      ring

theorem exists_signing_of_exponential_budget {R : Type*} [Fintype R] (m : ℕ)
    (a : R → Fin m → ℝ) (t b : R → ℝ) (ht : ∀ r,0 < t r)
    (hBudget : (∑ r,2*exp ((t r)^2*(∑ i,a r i^2)/2-t r*b r)) < 1) :
    ∃ s : Fin m → Bool, ∀ r,|signedSum (a r) s| < b r := by
  classical
  let potential := fun s : Fin m → Bool => ∑ r,
    (exp (t r*(signedSum (a r) s-b r))+exp ((-t r)*(signedSum (a r) s+b r)))
  have hSum : (∑ s : Fin m → Bool,potential s) ≤
      ∑ _s : Fin m → Bool,(∑ r,2*exp ((t r)^2*(∑ i,a r i^2)/2-t r*b r)) := by
    dsimp only [potential]
    rw [sum_comm]
    calc
      _ ≤ ∑ r,((2:ℝ)^m*exp ((t r)^2*(∑ i,a r i^2)/2-t r*b r)+
          (2:ℝ)^m*exp ((t r)^2*(∑ i,a r i^2)/2-t r*b r)) := by
        apply sum_le_sum
        intro r _
        rw [sum_add_distrib]
        have hPos := shifted_exponential_sum_bound m (a r) (t r) (b r)
        have hNeg := shifted_exponential_sum_bound m (a r) (-t r) (-b r)
        have hNeg' : (∑ x,exp ((-t r)*(signedSum (a r) x+b r))) ≤
            (2:ℝ)^m*exp ((t r)^2*(∑ i,a r i^2)/2-t r*b r) := by
          simpa only [sub_neg_eq_add,neg_sq,neg_mul,mul_neg,neg_neg] using hNeg
        exact add_le_add hPos hNeg'
      _ = _ := by
        rw [sum_constant_signs,sum_mul]
        apply sum_congr rfl
        intro r _
        ring
  obtain ⟨s,_,hs⟩ := exists_le_of_sum_le (s:=univ) univ_nonempty hSum
  have hSmall : potential s < 1 := hs.trans_lt hBudget
  refine ⟨s,?_⟩
  intro r
  have hTerm := single_le_sum (s:=univ)
    (f:=fun r => exp (t r*(signedSum (a r) s-b r))+exp ((-t r)*(signedSum (a r) s+b r)))
    (fun _ _ => by positivity) (mem_univ r)
  change _ ≤ potential s at hTerm
  have hPos : exp (t r*(signedSum (a r) s-b r)) < 1 := by
    have hh := exp_pos ((-t r)*(signedSum (a r) s+b r))
    linarith only [hTerm,hSmall,hh]
  have hNeg : exp ((-t r)*(signedSum (a r) s+b r)) < 1 := by
    have hh := exp_pos (t r*(signedSum (a r) s-b r))
    linarith only [hTerm,hSmall,hh]
  have hP : t r*(signedSum (a r) s-b r) < 0 := exp_lt_one_iff.mp hPos
  have hN : (-t r)*(signedSum (a r) s+b r) < 0 := exp_lt_one_iff.mp hNeg
  rw [abs_lt]
  constructor <;> nlinarith only [hP,hN,ht r]

theorem exists_finite_signing_of_exponential_budget {E R : Type*} [Fintype E] [Fintype R]
    (a : R → E → ℝ) (t b : R → ℝ) (ht : ∀ r,0 < t r)
    (hBudget : (∑ r,2*exp ((t r)^2*(∑ e,a r e^2)/2-t r*b r)) < 1) :
    ∃ s : E → Bool, ∀ r, |∑ e,if s e then a r e else -a r e| < b r := by
  classical
  let f := Fintype.equivFin E
  have hVar : ∀ r,(∑ i : Fin (Fintype.card E),a r (f.symm i)^2)=∑ e,a r e^2 := by
    intro r
    exact f.symm.sum_comp (fun e => a r e^2)
  obtain ⟨s,hs⟩ := exists_signing_of_exponential_budget (Fintype.card E)
    (fun r i => a r (f.symm i)) t b ht (by simp_rw [hVar];exact hBudget)
  refine ⟨fun e => s (f e),?_⟩
  intro r
  have hSum := f.symm.sum_comp (fun e => if s (f e) then a r e else -a r e)
  simp only [Equiv.apply_symm_apply] at hSum
  rw [←hSum]
  exact hs r

end OverfullWork.ExponentialSigning
