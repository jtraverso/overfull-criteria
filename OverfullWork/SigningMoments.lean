module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr

@[expose] public section


/-!
# Finite sixth-moment signing bound

Uniform averaging over a finite Boolean cube, without measure theory.
The coefficients are bounded by one; the second, fourth and sixth moments
are bounded simultaneously. No partition-existence hypothesis is used.
-/

namespace OverfullWork.SigningMoments

open Finset

def signedSum {m : ℕ} (a : Fin m → ℝ) (s : Fin m → Bool) : ℝ :=
  ∑ i, if s i then a i else -a i

def moment {m : ℕ} (a : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ s : Fin m → Bool, (signedSum a s) ^ k

theorem sum_signs_succ {m : ℕ} (f : (Fin (m+1) → Bool) → ℝ) :
    (∑ s, f s) = ∑ s : Fin m → Bool, (f (Fin.cons true s) + f (Fin.cons false s)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).sum_comp f,
    Fintype.sum_prod_type, Fintype.sum_bool, sum_add_distrib]
  rfl

theorem signedSum_cons {m : ℕ} (a : Fin (m+1) → ℝ) (b : Bool) (s : Fin m → Bool) :
    signedSum a (Fin.cons b s) =
      (if b then a 0 else -a 0) + signedSum (fun i => a i.succ) s := by
  simp [signedSum, Fin.sum_univ_succ]

theorem sum_constant_signs (m : ℕ) (c : ℝ) :
    (∑ _s : Fin m → Bool, c) = c * (2:ℝ)^m := by
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem moment_two_succ {m : ℕ} (a : Fin (m+1) → ℝ) :
    moment a 2 = 2 * moment (fun i => a i.succ) 2 + 2 * (a 0)^2 * (2:ℝ)^m := by
  rw [moment, sum_signs_succ]
  simp only [signedSum_cons a true, signedSum_cons a false, Bool.false_eq_true, ite_true, ite_false]
  have h (x y : ℝ) : (x+y)^2 + (-x+y)^2 = 2*y^2 + 2*x^2 := by ring
  simp_rw [h]
  simp only [sum_add_distrib, ← mul_sum, sum_constant_signs, moment]
  ring

theorem moment_four_succ {m : ℕ} (a : Fin (m+1) → ℝ) :
    moment a 4 = 2 * moment (fun i => a i.succ) 4 +
      12 * (a 0)^2 * moment (fun i => a i.succ) 2 + 2 * (a 0)^4 * (2:ℝ)^m := by
  rw [moment, sum_signs_succ]
  simp only [signedSum_cons a true, signedSum_cons a false, Bool.false_eq_true, ite_true, ite_false]
  have h (x y : ℝ) : (x+y)^4 + (-x+y)^4 = 2*y^4 + 12*x^2*y^2 + 2*x^4 := by ring
  simp_rw [h]
  simp only [sum_add_distrib, ← mul_sum, sum_constant_signs, moment]
  ring

theorem moment_six_succ {m : ℕ} (a : Fin (m+1) → ℝ) :
    moment a 6 = 2 * moment (fun i => a i.succ) 6 +
      30 * (a 0)^2 * moment (fun i => a i.succ) 4 +
      30 * (a 0)^4 * moment (fun i => a i.succ) 2 + 2 * (a 0)^6 * (2:ℝ)^m := by
  rw [moment, sum_signs_succ]
  simp only [signedSum_cons a true, signedSum_cons a false, Bool.false_eq_true, ite_true, ite_false]
  have h (x y : ℝ) : (x+y)^6 + (-x+y)^6 =
      2*y^6 + 30*x^2*y^4 + 30*x^4*y^2 + 2*x^6 := by ring
  simp_rw [h]
  simp only [sum_add_distrib, ← mul_sum, sum_constant_signs, moment]
  ring

theorem moment_even_nonneg {m : ℕ} (a : Fin m → ℝ) (k : ℕ) :
    0 ≤ moment a (2*k) := by
  apply sum_nonneg
  intro s _
  exact (even_two_mul k).pow_nonneg _

theorem bounded_moments (m : ℕ) (a : Fin m → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    moment a 2 ≤ (m:ℝ) * 2^m ∧
    moment a 4 ≤ 3 * (m:ℝ)^2 * 2^m ∧
    moment a 6 ≤ 15 * (m:ℝ)^3 * 2^m := by
  induction m with
  | zero => simp [moment, signedSum]
  | succ m ih =>
    obtain ⟨h2,h4,h6⟩ := ih (fun i => a i.succ) (fun i => ha i.succ)
    have hsq : (a 0)^2 ≤ 1 := by nlinarith [abs_le.mp (ha 0)]
    have hfour : (a 0)^4 ≤ 1 := by nlinarith [sq_nonneg ((a 0)^2 - 1)]
    have hsix : (a 0)^6 ≤ 1 := by
      calc
        _ = (a 0)^2 * (a 0)^4 := by ring
        _ ≤ 1 * 1 := mul_le_mul hsq hfour (by positivity) (by norm_num)
        _ = 1 := by ring
    have n2 := moment_even_nonneg (fun i => a i.succ) 1
    have n4 := moment_even_nonneg (fun i => a i.succ) 2
    have n6 := moment_even_nonneg (fun i => a i.succ) 3
    have hp : 0 ≤ (2:ℝ)^m := by positivity
    have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
    constructor
    · rw [moment_two_succ]
      calc
        _ ≤ 2 * ((m:ℝ)*2^m) + 2 * 1 * 2^m := by gcongr
        _ = _ := by push_cast; rw [pow_succ (2:ℝ) m]; ring
    constructor
    · rw [moment_four_succ]
      calc
        _ ≤ 2 * (3*(m:ℝ)^2*2^m) + 12 * 1 * ((m:ℝ)*2^m) + 2 * 1 * 2^m := by gcongr
        _ ≤ _ := by push_cast; rw [pow_succ (2:ℝ) m]; nlinarith
    · rw [moment_six_succ]
      calc
        _ ≤ 2 * (15*(m:ℝ)^3*2^m) + 30 * 1 * (3*(m:ℝ)^2*2^m) +
            30 * 1 * ((m:ℝ)*2^m) + 2 * 1 * 2^m := by gcongr
        _ ≤ _ := by push_cast; rw [pow_succ (2:ℝ) m]; nlinarith [mul_nonneg hm hp]

/-- A single signing simultaneously controls every row of a finite matrix.
The proof averages the sum of the nonnegative sixth powers. -/
theorem exists_signing_sixth_bound {R : Type*} [Fintype R] (m : ℕ)
    (a : R → Fin m → ℝ) (ha : ∀ r i, |a r i| ≤ 1) :
    ∃ s : Fin m → Bool, ∀ r,
      (signedSum (a r) s)^6 ≤ 15 * (Fintype.card R:ℝ) * (m:ℝ)^3 := by
  classical
  have hsum : (∑ s : Fin m → Bool, ∑ r, (signedSum (a r) s)^6) ≤
      ∑ _s : Fin m → Bool, 15 * (Fintype.card R:ℝ) * (m:ℝ)^3 := by
    rw [sum_comm]
    calc
      _ ≤ ∑ _r : R, 15 * (m:ℝ)^3 * 2^m := by
        exact sum_le_sum (fun r _ => (bounded_moments m (a r) (ha r)).2.2)
      _ = _ := by rw [sum_constant_signs]; simp only [sum_const, card_univ, nsmul_eq_mul]; ring
  obtain ⟨s, _, hs⟩ := exists_le_of_sum_le (s := univ) univ_nonempty hsum
  refine ⟨s, fun r => le_trans ?_ hs⟩
  exact single_le_sum (f := fun r => (signedSum (a r) s)^6)
    (fun _ _ => by positivity) (mem_univ r)

/-- Explicit finite discrepancy criterion. It is a numerical size condition,
not an assumption that a good signing or partition already exists. -/
theorem exists_signing_discrepancy {R : Type*} [Fintype R] (m : ℕ)
    (a : R → Fin m → ℝ) (ha : ∀ r i, |a r i| ≤ 1) (b : ℝ) (hb : 0 ≤ b)
    (hsize : 15 * (Fintype.card R:ℝ) * (m:ℝ)^3 < b^6) :
    ∃ s : Fin m → Bool, ∀ r, |signedSum (a r) s| < b := by
  obtain ⟨s, hs⟩ := exists_signing_sixth_bound m a ha
  refine ⟨s, fun r => ?_⟩
  by_contra h
  have hp := pow_le_pow_left₀ hb (le_of_not_gt h) 6
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (signedSum (a r) s)^6)] at hp
  exact (not_lt_of_ge (le_trans hp (hs r))) hsize

end OverfullWork.SigningMoments
