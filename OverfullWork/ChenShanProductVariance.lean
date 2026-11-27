module

public import OverfullWork.ChenShanSwapVarianceStep
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset

variable {A B : Type*} [Fintype A] [Fintype B]

private theorem uniformMean_mono (f g : A → ℝ) (h : ∀ a, f a ≤ g a) :
    uniformBlockMean f ≤ uniformBlockMean g := by
  simp only [uniformBlockMean_eq_div]
  exact div_le_div_of_nonneg_right (sum_le_sum fun a _ => h a) (by positivity)

private theorem uniformMean_sub (f g : A → ℝ) :
    uniformBlockMean (fun a => f a - g a) = uniformBlockMean f - uniformBlockMean g := by
  simp only [uniformBlockMean_eq_div, sum_sub_distrib, sub_div]

private theorem uniformMean_const [Nonempty A] (c : ℝ) :
    uniformBlockMean (fun _ : A => c) = c := by
  rw [uniformBlockMean_eq_div, sum_const, card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Fintype.card_ne_zero)

private theorem uniformMean_equiv (e : A ≃ B) (f : B → ℝ) :
    uniformBlockMean (fun a => f (e a)) = uniformBlockMean f := by
  simp only [uniformBlockMean_eq_div, Fintype.card_congr e, e.sum_comp]

private theorem uniformMean_prod (f : A → B → ℝ) :
    uniformBlockMean (fun t : A × B => f t.1 t.2) =
      uniformBlockMean (fun a => uniformBlockMean (f a)) := by
  simp only [uniformBlockMean_eq_div, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← sum_div, div_div, mul_comm (Fintype.card B : ℝ)]

private theorem uniformMean_comm (f : A → B → ℝ) :
    uniformBlockMean (fun a => uniformBlockMean (f a)) =
      uniformBlockMean (fun b => uniformBlockMean (fun a => f a b)) := by
  simp only [← uniformMean_prod]
  exact uniformMean_equiv (Equiv.prodComm A B) (fun t => f t.2 t.1)

private theorem uniformVariance_jensen [Nonempty A] (f : A → ℝ) :
    (uniformBlockMean f)^2 ≤ uniformBlockMean (fun a => (f a)^2) := by
  have h := blockMean_coupling_squared_gap
    (fun _ : A => (Fintype.card A : ℝ)⁻¹) f (fun _ => 0)
    (fun _ => by positivity) (by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero))
  change (uniformBlockMean f - uniformBlockMean (fun _ : A => 0))^2 ≤
    uniformBlockMean (fun a => (f a-0)^2) at h
  simpa only [uniformMean_const, sub_zero] using h

private theorem uniformVariance_centered [Nonempty A] (f : A → ℝ) :
    uniformBlockVariance f = uniformBlockMean (fun a => (f a - uniformBlockMean f)^2) := by
  let m := uniformBlockMean f
  have h (a : A) : (f a-m)^2 = (f a)^2 - (2*m)*f a+m^2 := by ring
  have hM : (∑ a, f a) = (Fintype.card A : ℝ)*m := by
    dsimp only [m]
    rw [mul_comm, uniformBlockMean_eq_div, div_mul_cancel₀ _ (by exact_mod_cast Fintype.card_ne_zero)]
  change uniformBlockMean (fun a => (f a)^2) - m^2 = uniformBlockMean (fun a => (f a-m)^2)
  rw [uniformBlockMean_eq_div, uniformBlockMean_eq_div]
  simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, hM]
  field_simp [show (Fintype.card A : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero]
  ring

/-- Averaging functions of one variable over an independent parameter
can only decrease variance relative to the average of their variances. -/
theorem uniform_variance_of_mean_le [Nonempty A] [Nonempty B] (f : A → B → ℝ) :
    uniformBlockVariance (fun a => uniformBlockMean (f a)) ≤
      uniformBlockMean (fun b => uniformBlockVariance (fun a => f a b)) := by
  rw [uniformVariance_centered (fun a => uniformBlockMean (f a))]
  simp_rw [uniformVariance_centered (fun a => f a _)]
  rw [← uniformMean_comm (fun a b => (f a b - uniformBlockMean (fun z => f z b))^2)]
  refine uniformMean_mono _ _ (fun a => ?_)
  rw [uniformMean_comm f, ← uniformMean_sub]
  exact uniformVariance_jensen _

private theorem uniformVariance_equiv (e : A ≃ B) (f : B → ℝ) :
    uniformBlockVariance (fun a => f (e a)) = uniformBlockVariance f := by
  unfold uniformBlockVariance
  rw [uniformMean_equiv e (fun b => (f b)^2), uniformMean_equiv e f]

/-- Law of total variance for a uniform binary product. -/
theorem uniform_variance_prod (f : A → B → ℝ) :
    uniformBlockVariance (fun t : A × B => f t.1 t.2) =
      uniformBlockMean (fun a => uniformBlockVariance (f a)) +
        uniformBlockVariance (fun a => uniformBlockMean (f a)) := by
  unfold uniformBlockVariance
  rw [uniformMean_prod (fun a b => (f a b)^2), uniformMean_prod f, uniformMean_sub]
  ring

/-- The two conditional variances bound the full variance on a binary
product. -/
theorem uniform_variance_prod_le [Nonempty A] [Nonempty B] (f : A → B → ℝ) :
    uniformBlockVariance (fun t : A × B => f t.1 t.2) ≤
      uniformBlockMean (fun a => uniformBlockVariance (f a)) +
        uniformBlockMean (fun b => uniformBlockVariance (fun a => f a b)) := by
  rw [uniform_variance_prod]
  exact add_le_add_right (uniform_variance_of_mean_le f) _


open scoped Classical

/-- Conditional variance bounds for each coordinate of a finite uniform
product add to an upper bound for the variance on the full product. -/
theorem uniform_pi_variance_le {I : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [∀ i, Nonempty (T i)]
    (f : (∀ i, T i) → ℝ) (b : I → ℝ)
    (h : ∀ (i : I) (t : ∀ i, T i),
      uniformBlockVariance (fun x : T i => f (Function.update t i x)) ≤ b i) :
    uniformBlockVariance f ≤ ∑ i, b i := by
  classical
  by_cases hI : Nonempty I
  · let i := Classical.choice hI
    let J := {j : I // j ≠ i}
    let e := Equiv.piSplitAt i T
    let g (x : T i) (t : ∀ j : J, T j.val) := f (e.symm (x,t))
    have hF : uniformBlockVariance f =
        uniformBlockVariance (fun p : T i × (∀ j : J, T j.val) => g p.1 p.2) :=
      (uniformVariance_equiv e.symm f).symm
    have hLeft (x : T i) : uniformBlockVariance (g x) ≤ ∑ j : J, b j.val := by
      apply uniform_pi_variance_le (g x) (fun j : J => b j.val)
      intro j t
      have hComm (y : T j.val) :
          e.symm (x, Function.update t j y) =
            Function.update (e.symm (x,t)) j.val y := by
        ext k
        by_cases hk : k = i
        · subst k
          simp [e, Equiv.piSplitAt, j.property.symm]
        · by_cases hj : k = j.val
          · subst k
            simp [e, Equiv.piSplitAt, j.property]
            exact Function.update_self j y t
          · have hne : (⟨k,hk⟩ : J) ≠ j := fun he => hj (congrArg Subtype.val he)
            simp [e, Equiv.piSplitAt, hk, hj, hne]
      simpa only [g, hComm] using h j.val (e.symm (x,t))
    have hRight (t : ∀ j : J, T j.val) :
        uniformBlockVariance (fun x : T i => g x t) ≤ b i := by
      let x₀ : T i := Classical.choice inferInstance
      have hComm (x : T i) :
          e.symm (x,t) = Function.update (e.symm (x₀,t)) i x := by
        ext k
        by_cases hk : k = i
        · subst k
          simp [e, Equiv.piSplitAt]
        · simp [e, Equiv.piSplitAt, hk]
      have he : (fun x : T i => g x t) =
          (fun x => f (Function.update (e.symm (x₀,t)) i x)) :=
        funext (fun x => congrArg f (hComm x))
      rw [he]
      exact h i (e.symm (x₀,t))
    have hSum : (∑ j : J, b j.val) + b i = ∑ k, b k := by
      rw [← Finset.sum_subtype (univ.erase i) (fun j => by simp only [mem_erase, mem_univ, and_true]) b,
        sum_erase_add _ _ (mem_univ i)]
    rw [hF, ← hSum]
    refine (uniform_variance_prod_le g).trans (add_le_add ?_ ?_)
    · exact (uniformMean_mono _ _ hLeft).trans_eq (uniformMean_const _)
    · exact (uniformMean_mono _ _ hRight).trans_eq (uniformMean_const _)
  · let _ : IsEmpty I := not_nonempty_iff.mp hI
    let t : ∀ i, T i := fun i => isEmptyElim i
    have hf (x : ∀ i, T i) : f x = f t := congrArg f (Subsingleton.elim x t)
    have hfe : f = fun _ => f t := funext hf
    unfold uniformBlockVariance
    rw [hfe]
    simp only [uniformMean_const, sub_self, sum_of_isEmpty, le_refl]
termination_by Fintype.card I
decreasing_by exact Fintype.card_subtype_lt (x := i) (not_not_intro rfl)

end OverfullWork.ChenShan
