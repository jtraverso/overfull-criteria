module

public import OverfullWork.BiasedDegreeCutSelection
public import OverfullWork.BiasedExponentialSigning
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section


/-! Finite biased Boolean sampling. Products of two coordinates in
different blocks are controlled using the same exponential estimate as
single coordinates. -/
namespace OverfullWork.BernoulliPairBlocks

open Finset Real
open scoped Classical
universe u v

def coordinateMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

def assignmentMass {E : Type u} [Fintype E] (p : ℝ) (s : E → Bool) : ℝ :=
  ∏ i, coordinateMass p (s i)

theorem assignmentMass_nonneg {E : Type u} [Fintype E] (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (s : E → Bool) : 0 ≤ assignmentMass p s :=
  prod_nonneg fun i _ => by cases s i <;> simp [coordinateMass,hp,hp1]

theorem assignmentMass_sum {E : Type u} [Fintype E] (p : ℝ) :
    (∑ s : E → Bool, assignmentMass p s) = 1 := by
  classical
  unfold assignmentMass
  rw [←Fintype.prod_sum]
  have h : (∑ b : Bool, coordinateMass p b) = 1 := by
    rw [Fintype.sum_bool]
    simp only [coordinateMass,Bool.false_eq_true,if_false,if_true]
    ring
  simp only [h,prod_const_one]

private theorem joint_true_mass {E : Type u} [Fintype E] (p : ℝ) {y z : E} (hyz : y ≠ z) :
    (∑ s : E → Bool, assignmentMass p s * (if s y && s z then (1:ℝ) else 0)) = p^2 := by
  classical
  let f (i : E) (b : Bool) : ℝ :=
    coordinateMass p b * if i = y ∨ i = z then (if b then 1 else 0) else 1
  have hInner (i : E) : (∑ b : Bool, f i b) = (if i = y ∨ i = z then p else 1) := by
    rw [Fintype.sum_bool]
    by_cases hi : i = y ∨ i = z
    · simp [f,coordinateMass,hi]
    · simp [f,coordinateMass,hi]
  calc
    _ = ∑ s : E → Bool, ∏ i, f i (s i) := by
      apply sum_congr rfl
      intro s _
      simp only [f,assignmentMass,prod_mul_distrib]
      congr 1
      rw [←prod_filter]
      have h : (univ : Finset E).filter (fun i => i = y ∨ i = z) = {y,z} := by
        ext i
        simp
      rw [h,prod_insert (by simp [hyz]),prod_singleton]
      cases s y <;> cases s z <;> norm_num
    _ = ∏ i, ∑ b : Bool, f i b := (Fintype.prod_sum f).symm
    _ = p^2 := by
      simp only [hInner]
      rw [←prod_filter]
      have h : (univ : Finset E).filter (fun i => i = y ∨ i = z) = {y,z} := by
        ext i
        simp
      rw [h,prod_insert (by simp [hyz]),prod_singleton,pow_two]

private theorem joint_true_exp {E : Type u} [Fintype E] (p t : ℝ) {y z : E} (hyz : y ≠ z) :
    (∑ s : E → Bool, assignmentMass p s *
      exp (if s y && s z then (1-p^2)*t else -p^2*t)) =
      (1-p^2)*exp (-p^2*t)+p^2*exp ((1-p^2)*t) := by
  let a := exp (-p^2*t)
  let b := exp ((1-p^2)*t)
  have hRewrite (s : E → Bool) :
      exp (if s y && s z then (1-p^2)*t else -p^2*t) =
        a + (b-a)*(if s y && s z then (1:ℝ) else 0) := by
    cases s y <;> cases s z <;> simp [a,b]
  simp only [hRewrite,mul_add]
  rw [sum_add_distrib,←sum_mul,assignmentMass_sum,one_mul]
  simp_rw [show ∀ s : E → Bool, assignmentMass p s *
      ((b-a)*(if s y && s z then (1:ℝ) else 0)) =
        (b-a)*(assignmentMass p s * (if s y && s z then (1:ℝ) else 0)) from fun _ => by ring]
  rw [←mul_sum,joint_true_mass p hyz]
  dsimp only [a,b]
  ring

def pairCentered {I : Type u} {J : Type v} [Fintype I] (p : ℝ)
    (a : I → ℝ) (y z : J) (s : I × J → Bool) : ℝ :=
  ∑ i, if s (i,y) && s (i,z) then (1-p^2)*a i else -p^2*a i

/-- Sum the moment generating bound over the independent blocks
indexed by the common-neighbour side of a bipartite pair. -/
theorem weighted_pair_exp {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (a : I → ℝ) {y z : J} (hyz : y ≠ z) (t : ℝ) :
    (∑ s : I × J → Bool, assignmentMass p s * exp (t * pairCentered p a y z s)) ≤
      exp (t^2*(∑ i,a i^2)/2) := by
  classical
  let e := Equiv.curry I J Bool
  let f (i : I) (s : J → Bool) : ℝ :=
    assignmentMass p s * exp (if s y && s z then (1-p^2)*(t*a i) else -p^2*(t*a i))
  have hEq : (∑ s : I × J → Bool, assignmentMass p s * exp (t * pairCentered p a y z s)) =
      ∏ i, ∑ s : J → Bool, f i s := by
    rw [Fintype.prod_sum]
    apply Fintype.sum_equiv e
    intro s
    rw [assignmentMass,Fintype.prod_prod_type,pairCentered,mul_sum,exp_sum,←prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    change _ = _ * exp (if s (i,y) && s (i,z) then (1-p^2)*(t*a i) else -p^2*(t*a i))
    congr 2
    split <;> ring
  rw [hEq]
  calc
    _ ≤ ∏ i, exp ((t*a i)^2/2) := by
      apply prod_le_prod₀
      · intro i _
        exact sum_nonneg (fun s _ => mul_nonneg (assignmentMass_nonneg p hp hp1 s) (exp_pos _).le)
      · intro i _
        dsimp only [f]
        rw [joint_true_exp p (t*a i) hyz]
        exact BiasedExponentialSigning.centered_bernoulli_exp_le (p^2) (t*a i) (sq_nonneg p)
          (by nlinarith [mul_nonneg hp (sub_nonneg.mpr hp1)])
    _ = _ := by
      rw [←exp_sum]
      congr 1
      calc
        _ = ∑ i, (t^2/2)*a i^2 := sum_congr rfl (fun i _ => by ring)
        _ = _ := by rw [←mul_sum];ring

/-- The linear version on an arbitrary finite coordinate type. -/
theorem weighted_linear_exp {E : Type u} [Fintype E]
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (a : E → ℝ) (t : ℝ) :
    (∑ s : E → Bool, assignmentMass p s * exp (t*BiasedDegreeCutSelection.value p a s)) ≤
      exp (t^2*(∑ i,a i^2)/2) := by
  let e := Fintype.equivFin E
  let f : (E → Bool) ≃ (Fin (Fintype.card E) → Bool) := Equiv.arrowCongr e (Equiv.refl _)
  have hEq : (∑ s : E → Bool, assignmentMass p s * exp (t*BiasedDegreeCutSelection.value p a s)) =
      ∑ s : Fin (Fintype.card E) → Bool, BiasedExponentialSigning.mass _ p s *
        exp (t*BiasedExponentialSigning.centeredSum _ p (fun i => a (e.symm i)) s) := by
    apply Fintype.sum_equiv f
    intro s
    have hm := e.symm.prod_comp (fun i => coordinateMass p (s i))
    have hs := e.symm.sum_comp (fun i => if s i then (1-p)*a i else -p*a i)
    simp only [assignmentMass,BiasedDegreeCutSelection.value]
    rw [←hm,←hs] <;> rfl
  rw [hEq,←e.symm.sum_comp (fun i => a i^2)]
  exact BiasedExponentialSigning.weighted_exponential_bound _ p hp hp1 _ _

end OverfullWork.BernoulliPairBlocks
