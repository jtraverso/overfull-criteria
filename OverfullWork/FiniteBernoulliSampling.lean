module

public import OverfullWork.BiasedExponentialSigning
public import Mathlib.Data.Fintype.Powerset

@[expose] public section


/-! Actual finite Bernoulli vertex choices and their exponential tails.
These estimates concern events, not just existence of a good choice. -/
namespace OverfullWork.FiniteBernoulliSampling
open Finset Real
open scoped Classical
variable {E : Type*} [Fintype E]
set_option maxHeartbeats 18000000

def mass (p : ℝ) (s : E → Bool) : ℝ := ∏ e,if s e then p else 1-p

def centeredValue (p : ℝ) (a : E → ℝ) (s : E → Bool) : ℝ :=
  ∑ e,if s e then (1-p)*a e else -p*a e

theorem mass_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : E → Bool) :
    0 ≤ mass p s := prod_nonneg fun _ _ => by split_ifs <;> linarith only [hp,hp1]

theorem sum_mass (p : ℝ) : (∑ s : E → Bool,mass p s)=1 := by
  let f := Fintype.equivFin E
  let g : (Fin (Fintype.card E) → Bool) ≃ (E → Bool) := Equiv.arrowCongr f.symm (Equiv.refl Bool)
  have hMass : ∀ s,mass p (g s)=BiasedExponentialSigning.mass (Fintype.card E) p s := by
    intro s
    unfold mass BiasedExponentialSigning.mass
    have hh := f.symm.prod_comp (fun e => if (g s) e then p else 1-p)
    simpa [g] using hh.symm
  rw [←g.sum_comp]
  simp_rw [hMass]
  exact BiasedExponentialSigning.sum_mass _ p

theorem exponential_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (a : E → ℝ) (t : ℝ) :
    (∑ s : E → Bool,mass p s*exp (t*centeredValue p a s)) ≤
      exp (t^2*(∑ e,a e^2)/2) := by
  let f := Fintype.equivFin E
  let g : (Fin (Fintype.card E) → Bool) ≃ (E → Bool) := Equiv.arrowCongr f.symm (Equiv.refl Bool)
  have hMass : ∀ s,mass p (g s)=BiasedExponentialSigning.mass (Fintype.card E) p s := by
    intro s
    unfold mass BiasedExponentialSigning.mass
    have hh := f.symm.prod_comp (fun e => if (g s) e then p else 1-p)
    simpa [g] using hh.symm
  have hValue : ∀ s,centeredValue p a (g s)=
      BiasedExponentialSigning.centeredSum (Fintype.card E) p (fun i => a (f.symm i)) s := by
    intro s
    unfold centeredValue BiasedExponentialSigning.centeredSum
    have hh := f.symm.sum_comp (fun e => if (g s) e then (1-p)*a e else -p*a e)
    simpa [g] using hh.symm
  rw [←g.sum_comp]
  simp_rw [hMass,hValue]
  have hh := BiasedExponentialSigning.weighted_exponential_bound (Fintype.card E) p hp hp1
    (fun i => a (f.symm i)) t
  have hVar : (∑ i : Fin (Fintype.card E),a (f.symm i)^2)=∑ e,a e^2 :=
    f.symm.sum_comp (fun e => a e^2)
  rw [hVar] at hh
  exact hh

theorem shifted_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (a : E → ℝ) (t b : ℝ) :
    (∑ s : E → Bool,mass p s*exp (t*(centeredValue p a s-b))) ≤
      exp (t^2*(∑ e,a e^2)/2-t*b) := by
  have hh := mul_le_mul_of_nonneg_right (exponential_bound p hp hp1 a t) (exp_pos (-t*b)).le
  calc
    _ = (∑ s : E → Bool,mass p s*exp (t*centeredValue p a s))*exp (-t*b) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro s _
      rw [mul_assoc,←exp_add]
      congr 2
      ring
    _ ≤ _ := hh
    _ = _ := by rw [←exp_add];congr 1;ring

theorem abs_tail_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (a : E → ℝ)
    (t b : ℝ) (ht : 0 < t) :
    (∑ s ∈ (univ : Finset (E → Bool)).filter (fun s => b ≤ |centeredValue p a s|),mass p s) ≤
      2*exp (t^2*(∑ e,a e^2)/2-t*b) := by
  let P : (E → Bool) → ℝ := fun s =>
    exp (t*(centeredValue p a s-b))+exp ((-t)*(centeredValue p a s+b))
  have hPoint : ∀ s : E → Bool,b ≤ |centeredValue p a s| → 1 ≤ P s := by
    intro s hs
    rcases le_abs.mp hs with h|h
    · have hh : 1 ≤ exp (t*(centeredValue p a s-b)) := one_le_exp_iff.mpr (by nlinarith only [h,ht])
      have hh' := exp_pos ((-t)*(centeredValue p a s+b))
      dsimp only [P]
      linarith only [hh,hh']
    · have hh : 1 ≤ exp ((-t)*(centeredValue p a s+b)) := one_le_exp_iff.mpr (by nlinarith only [h,ht])
      have hh' := exp_pos (t*(centeredValue p a s-b))
      dsimp only [P]
      linarith only [hh,hh']
  have hSum : (∑ s ∈ (univ : Finset (E → Bool)).filter (fun s => b ≤ |centeredValue p a s|),mass p s) ≤
      ∑ s : E → Bool,mass p s*P s := by
    calc
      _ ≤ ∑ s ∈ (univ : Finset (E → Bool)).filter (fun s => b ≤ |centeredValue p a s|),mass p s*P s := by
        apply sum_le_sum
        intro s hs
        have hh := mul_le_mul_of_nonneg_left (hPoint s (mem_filter.mp hs).2) (mass_nonneg p hp hp1 s)
        simpa only [mul_one] using hh
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun s _ _ =>
        mul_nonneg (mass_nonneg p hp hp1 s) (by dsimp only [P];positivity))
  have hP := shifted_bound p hp hp1 a t b
  have hN := shifted_bound p hp hp1 a (-t) (-b)
  simp only [sub_neg_eq_add,neg_sq,neg_mul,mul_neg,neg_neg] at hN
  have hTotal : (∑ s : E → Bool,mass p s*P s) ≤ 2*exp (t^2*(∑ e,a e^2)/2-t*b) := by
    dsimp only [P]
    rw [show (∑ s : E → Bool,mass p s*(exp (t*(centeredValue p a s-b))+
        exp ((-t)*(centeredValue p a s+b))))=
      (∑ s : E → Bool,mass p s*exp (t*(centeredValue p a s-b)))+
      (∑ s : E → Bool,mass p s*exp ((-t)*(centeredValue p a s+b))) by
      simp only [mul_add,sum_add_distrib]]
    simp only [neg_mul]
    linarith only [hP,hN]
  exact hSum.trans hTotal

end OverfullWork.FiniteBernoulliSampling
