module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real
open scoped Classical

variable {I C : Type*} [Fintype I] [Fintype C] [Nonempty C]

/-- One step of conditional expectation for the matching choices of
Barber–Kühn–Lo–Osthus–Taylor. Tests with no possible hit at the current
step retain their weights. Each active test is charged its exponential
moment before the candidate is selected. -/
theorem exists_matching_choice_nonincreasing_cost
    (w : I → ℝ) (active : I → Prop) (hit : I → C → Prop) (α p : ℝ)
    (hα : 0 ≤ α) (hw : ∀ i, 0 ≤ w i)
    (hHit : ∀ i, active i → ((univ.filter (hit i)).card : ℝ) ≤ p*Fintype.card C) :
    ∃ c : C, (∑ i, w i * (if active i then
      exp ((if hit i c then α else 0)-p*(exp α-1)) else 1)) ≤ ∑ i, w i := by
  let cost (i : I) (c : C) : ℝ := if active i then
    exp ((if hit i c then α else 0)-p*(exp α-1)) else 1
  let β := p*(exp α-1)
  let N := (Fintype.card C : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp' : 0 ≤ exp α-1 := sub_nonneg.mpr (one_le_exp_iff.mpr hα)
  have hTest (i : I) : (∑ c, cost i c) ≤ N := by
    by_cases hi : active i
    · have hCount : (∑ c, exp (if hit i c then α else 0)) =
          N+((univ.filter (hit i)).card : ℝ)*(exp α-1) := by
        calc
          _ = ∑ c, (1 + if hit i c then exp α-1 else 0) := by
            apply sum_congr rfl
            intro c _
            by_cases hc : hit i c <;> simp [hc]
          _ = _ := by
            rw [sum_add_distrib,← sum_filter]
            simp [N,nsmul_eq_mul]
            ring
      have hBound : (∑ c, exp (if hit i c then α else 0)) ≤ N*exp β := by
        rw [hCount]
        calc
          _ ≤ N+(p*N)*(exp α-1) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right (hHit i hi) hp')
          _ = N*(β+1) := by dsimp only [β]; ring
          _ ≤ N*exp β := mul_le_mul_of_nonneg_left (add_one_le_exp β) hN
      calc
        _ = (∑ c, exp (if hit i c then α else 0)) * exp (-β) := by
          simp only [cost,hi,ite_true,sum_mul,← exp_add,sub_eq_add_neg,β]
        _ ≤ (N*exp β)*exp (-β) := mul_le_mul_of_nonneg_right hBound (exp_pos _).le
        _ = N := by rw [mul_assoc,← exp_add,add_neg_cancel,exp_zero,mul_one]
    · simp [cost,hi,N]
  have hTotal : (∑ c : C, ∑ i, w i*cost i c) ≤ N*(∑ i, w i) := by
    rw [sum_comm,mul_sum]
    apply sum_le_sum
    intro i _
    rw [← mul_sum,mul_comm N]
    exact mul_le_mul_of_nonneg_left (hTest i) (hw i)
  by_contra! hn
  have hStrict : (∑ _c : C, ∑ i, w i) < ∑ c : C, ∑ i, w i*cost i c :=
    sum_lt_sum_of_nonempty univ_nonempty (fun c _ => hn c)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hStrict
  exact (not_lt_of_ge hTotal) hStrict

end OverfullWork.ChenShan
