module

public import OverfullWork.ExponentialSigning
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section


/-! Finite weighted exponential averaging for biased Boolean selections.
All masses and witnesses are constructed explicitly. No probability law,
concentration estimate or favourable partition is postulated. -/
namespace OverfullWork.BiasedExponentialSigning
open Finset Real SigningMoments
open scoped Classical
set_option maxHeartbeats 18000000

theorem centered_bernoulli_exp_le (p x : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-p)*exp (-p*x)+p*exp ((1-p)*x) ≤ exp (x^2/2) := by
  have hq : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hJ := convexOn_exp.2 (Set.mem_univ (p*x))
    (Set.mem_univ (-(1-p)*x)) hq hp (by ring : (1-p)+p=1)
  have hMean : (1-p)*(p*x)+p*(-(1-p)*x)=0 := by ring
  simp only [smul_eq_mul,hMean,exp_zero] at hJ
  let A := (1-p)*exp (-p*x)+p*exp ((1-p)*x)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hMultiply := mul_le_mul_of_nonneg_left hJ hA
  have hProduct : A*((1-p)*exp (p*x)+p*exp (-(1-p)*x))=
      1+p*(1-p)*(exp x+exp (-x)-2) := by
    calc
      _ = (1-p)^2*(exp (-p*x)*exp (p*x))+
          p*(1-p)*(exp (-p*x)*exp (-(1-p)*x))+
          p*(1-p)*(exp ((1-p)*x)*exp (p*x))+
          p^2*(exp ((1-p)*x)*exp (-(1-p)*x)) := by dsimp only [A];ring
      _ = _ := by
        simp_rw [←exp_add]
        have h₁ : -p*x+p*x=0 := by ring
        have h₂ : -p*x+-(1-p)*x = -x := by ring
        have h₃ : (1-p)*x+p*x=x := by ring
        have h₄ : (1-p)*x+-(1-p)*x=0 := by ring
        simp only [h₁,h₂,h₃,h₄,exp_zero]
        ring
  have hCosh := Real.cosh_le_exp_half_sq x
  have hLo₁ := Real.add_one_le_exp x
  have hLo₂ := Real.add_one_le_exp (-x)
  rw [Real.cosh_eq] at hCosh
  have hFactor : 0 ≤ 1-2*p*(1-p) := by nlinarith only [sq_nonneg (p-1/2)]
  have hGap := mul_nonneg hFactor (show 0 ≤ exp x+exp (-x)-2 by linarith only [hLo₁,hLo₂])
  rw [hProduct] at hMultiply
  dsimp only [A] at hMultiply
  nlinarith only [hMultiply,hCosh,hGap]

def mass (m : ℕ) (p : ℝ) (s : Fin m → Bool) : ℝ :=
  ∏ i,if s i then p else 1-p

def centeredSum (m : ℕ) (p : ℝ) (a : Fin m → ℝ) (s : Fin m → Bool) : ℝ :=
  ∑ i,if s i then (1-p)*a i else -p*a i

theorem mass_nonneg (m : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Fin m → Bool) : 0 ≤ mass m p s := by
  apply prod_nonneg
  intro i _
  split_ifs <;> linarith only [hp,hp1]

theorem mass_cons (m : ℕ) (p : ℝ) (b : Bool) (s : Fin m → Bool) :
    mass (m+1) p (Fin.cons b s)=(if b then p else 1-p)*mass m p s := by
  simp only [mass,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem centeredSum_cons (m : ℕ) (p : ℝ) (a : Fin (m+1) → ℝ)
    (b : Bool) (s : Fin m → Bool) :
    centeredSum (m+1) p a (Fin.cons b s)=
      (if b then (1-p)*a 0 else -p*a 0)+centeredSum m p (fun i => a i.succ) s := by
  simp only [centeredSum,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem sum_mass (m : ℕ) (p : ℝ) : (∑ s : Fin m → Bool,mass m p s)=1 := by
  induction m with
  | zero => simp [mass]
  | succ m ih =>
    rw [sum_signs_succ]
    simp only [mass_cons,ite_true,ite_false,Bool.false_eq_true]
    rw [sum_add_distrib,←mul_sum,←mul_sum,ih]
    ring

theorem weighted_exponential_bound (m : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : Fin m → ℝ) (t : ℝ) :
    (∑ s : Fin m → Bool,mass m p s*exp (t*centeredSum m p a s)) ≤
      exp (t^2*(∑ i,a i^2)/2) := by
  induction m with
  | zero => simp [mass,centeredSum]
  | succ m ih =>
    have hFactor : (∑ s : Fin (m+1) → Bool,mass (m+1) p s*exp (t*centeredSum (m+1) p a s))=
        ((1-p)*exp (-p*(t*a 0))+p*exp ((1-p)*(t*a 0)))*
          (∑ s : Fin m → Bool,mass m p s*exp (t*centeredSum m p (fun i => a i.succ) s)) := by
      rw [sum_signs_succ]
      simp only [mass_cons,centeredSum_cons,Bool.false_eq_true,ite_true,ite_false,mul_add,exp_add]
      rw [mul_sum]
      apply sum_congr rfl
      intro s _
      have h₁ : t*(-p*a 0)= -p*(t*a 0) := by ring
      have h₂ : t*((1-p)*a 0)=(1-p)*(t*a 0) := by ring
      rw [h₁,h₂]
      ring
    rw [hFactor]
    calc
      _ ≤ exp ((t*a 0)^2/2)*exp (t^2*(∑ i : Fin m,a i.succ^2)/2) := by
        apply mul_le_mul (centered_bernoulli_exp_le p (t*a 0) hp hp1) (ih (fun i => a i.succ))
        · exact sum_nonneg fun s _ => mul_nonneg (mass_nonneg m p hp hp1 s) (exp_pos _).le
        · exact (exp_pos _).le
      _ = _ := by
        rw [←exp_add,Fin.sum_univ_succ]
        congr 1
        ring

theorem weighted_shifted_bound (m : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : Fin m → ℝ) (t b : ℝ) :
    (∑ s : Fin m → Bool,mass m p s*exp (t*(centeredSum m p a s-b))) ≤
      exp (t^2*(∑ i,a i^2)/2-t*b) := by
  have hh := mul_le_mul_of_nonneg_right (weighted_exponential_bound m p hp hp1 a t) (exp_pos (-t*b)).le
  calc
    _ = (∑ s : Fin m → Bool,mass m p s*exp (t*centeredSum m p a s))*exp (-t*b) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro s _
      rw [mul_assoc,←exp_add]
      congr 2
      ring
    _ ≤ _ := hh
    _ = _ := by rw [←exp_add];congr 1;ring

theorem exists_signing_of_budget {R : Type*} [Fintype R] (m : ℕ)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : R → Fin m → ℝ) (t b : R → ℝ) (ht : ∀ r,0 < t r)
    (hBudget : (∑ r,2*exp ((t r)^2*(∑ i,a r i^2)/2-t r*b r)) < 1) :
    ∃ s : Fin m → Bool,∀ r,|centeredSum m p (a r) s| < b r := by
  let potential := fun s : Fin m → Bool => ∑ r,
    (exp (t r*(centeredSum m p (a r) s-b r))+
      exp ((-t r)*(centeredSum m p (a r) s+b r)))
  have hSum : (∑ s : Fin m → Bool,mass m p s*potential s) ≤
      ∑ r,2*exp ((t r)^2*(∑ i,a r i^2)/2-t r*b r) := by
    conv_lhs => simp only [potential,mul_sum,mul_add]
    rw [sum_comm]
    apply sum_le_sum
    intro r _
    rw [sum_add_distrib]
    have hP := weighted_shifted_bound m p hp hp1 (a r) (t r) (b r)
    have hN := weighted_shifted_bound m p hp hp1 (a r) (-t r) (-b r)
    simp only [sub_neg_eq_add,neg_sq,neg_mul,mul_neg,neg_neg] at hN
    simp only [mul_add,neg_add] at hN
    simp only [neg_mul] at hN ⊢
    linarith only [hP,hN]
  have hSmall : ∃ s : Fin m → Bool,potential s < 1 := by
    by_contra hn
    have hAll : ∀ s : Fin m → Bool,1 ≤ potential s := by simpa only [not_exists,not_lt] using hn
    have hh := sum_le_sum (s:=univ) fun s _ =>
      mul_le_mul_of_nonneg_left (hAll s) (mass_nonneg m p hp hp1 s)
    simp only [mul_one,sum_mass] at hh
    linarith only [hh,hSum,hBudget]
  obtain ⟨s,hs⟩ := hSmall
  refine ⟨s,?_⟩
  intro r
  have hTerm := single_le_sum (s:=univ)
    (f:=fun r => exp (t r*(centeredSum m p (a r) s-b r))+
      exp ((-t r)*(centeredSum m p (a r) s+b r)))
    (fun _ _ => by positivity) (mem_univ r)
  change _ ≤ potential s at hTerm
  have hP : exp (t r*(centeredSum m p (a r) s-b r)) < 1 := by
    have hh := exp_pos ((-t r)*(centeredSum m p (a r) s+b r))
    linarith only [hTerm,hs,hh]
  have hN : exp ((-t r)*(centeredSum m p (a r) s+b r)) < 1 := by
    have hh := exp_pos (t r*(centeredSum m p (a r) s-b r))
    linarith only [hTerm,hs,hh]
  have hP' := exp_lt_one_iff.mp hP
  have hN' := exp_lt_one_iff.mp hN
  rw [abs_lt]
  constructor <;> nlinarith only [hP',hN',ht r]

theorem exists_finite_selection_of_budget {E R : Type*} [Fintype E] [Fintype R]
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : R → E → ℝ) (t b : R → ℝ) (ht : ∀ r,0 < t r)
    (hBudget : (∑ r,2*exp ((t r)^2*(∑ e,a r e^2)/2-t r*b r)) < 1) :
    ∃ s : E → Bool,∀ r,|∑ e,if s e then (1-p)*a r e else -p*a r e| < b r := by
  let f := Fintype.equivFin E
  have hVar : ∀ r,(∑ i : Fin (Fintype.card E),a r (f.symm i)^2)=∑ e,a r e^2 := by
    intro r
    exact f.symm.sum_comp (fun e => a r e^2)
  obtain ⟨s,hs⟩ := exists_signing_of_budget (Fintype.card E) p hp hp1
    (fun r i => a r (f.symm i)) t b ht (by simp_rw [hVar];exact hBudget)
  refine ⟨fun e => s (f e),?_⟩
  intro r
  have hSum := f.symm.sum_comp (fun e => if s (f e) then (1-p)*a r e else -p*a r e)
  simp only [Equiv.apply_symm_apply] at hSum
  rw [←hSum]
  exact hs r

end OverfullWork.BiasedExponentialSigning
