module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

@[expose] public section

namespace OverfullWork.IndependentBernoulliSampling

open Finset Real
open scoped Classical

variable {I : Type*} [Fintype I]

noncomputable def mass (p : I → ℝ) (s : I → Bool) : ℝ :=
  ∏ i, if s i then p i else 1 - p i

noncomputable def mean (p : I → ℝ) (S : Finset I) : ℝ :=
  ∑ i ∈ S, p i

noncomputable def count (S : Finset I) (s : I → Bool) : ℝ :=
  (S.filter fun i => s i).card

theorem mass_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, p i ≤ 1)
    (s : I → Bool) : 0 ≤ mass p s :=
  prod_nonneg fun i _ => by split_ifs <;> linarith only [hp i, hp' i]

theorem sum_mass (p : I → ℝ) : (∑ s : I → Bool, mass p s) = 1 := by
  unfold mass
  rw [← Fintype.prod_sum (κ := fun _ : I => Bool)
    (fun i b => if b then p i else 1 - p i)]
  simp

private theorem exponential_bound (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp' : ∀ i, p i ≤ 1) (S : Finset I) {t : ℝ} (ht : |t| ≤ 1) :
    (∑ s : I → Bool, mass p s * exp (t * count S s)) ≤
      exp (mean p S * (t + t ^ 2)) := by
  let q : I → ℝ := fun i => if i ∈ S then p i else 0
  have hq (i : I) : 0 ≤ q i ∧ q i ≤ 1 := by
    dsimp only [q]
    split_ifs
    · exact ⟨hp i, hp' i⟩
    · norm_num
  let f : I → Bool → ℝ := fun i b =>
    (if b then p i else 1 - p i) * exp (if i ∈ S ∧ b then t else 0)
  have hCount (s : I → Bool) :
      t * count S s = ∑ i, if i ∈ S ∧ s i then t else 0 := by
    rw [← Finset.sum_filter]
    have hFilter : (univ.filter (fun i => i ∈ S ∧ s i)) = S.filter (fun i => s i) := by
      ext i
      simp
    rw [hFilter]
    simp [count, mul_comm]
  have hProd (s : I → Bool) :
      mass p s * exp (t * count S s) = ∏ i, f i (s i) := by
    rw [mass,hCount,exp_sum,← prod_mul_distrib]
  have hFactor (i : I) : (∑ b : Bool, f i b) = 1 + q i * (exp t - 1) := by
    simp only [Fintype.sum_bool,f,q,Bool.false_eq_true,and_false,ite_false,exp_zero,
      mul_one,and_true]
    by_cases hi : i ∈ S
    · simp [hi]
      ring
    · simp [hi]
  simp_rw [hProd]
  rw [← Fintype.prod_sum (κ := fun _ : I => Bool) f]
  simp_rw [hFactor]
  calc
    _ ≤ ∏ i, exp (q i * (exp t - 1)) := by
      apply prod_le_prod₀
      · intro i _
        rw [show 1 + q i * (exp t - 1) = (1-q i) + q i * exp t by ring]
        exact add_nonneg (sub_nonneg.mpr (hq i).2)
          (mul_nonneg (hq i).1 (exp_pos _).le)
      · intro i _
        simpa only [add_comm] using add_one_le_exp (q i * (exp t - 1))
    _ = exp (mean p S * (exp t - 1)) := by
      rw [← exp_sum,← sum_mul]
      congr 2
      simp [q,mean]
    _ ≤ _ := by
      apply exp_le_exp.mpr
      refine mul_le_mul_of_nonneg_left ?_ (sum_nonneg fun i _ => hp i)
      have hTaylor := le_trans (le_abs_self (exp t - 1 - t))
        (abs_exp_sub_one_sub_id_le ht)
      linarith only [hTaylor]

private theorem shifted_bound (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp' : ∀ i, p i ≤ 1) (S : Finset I) {t : ℝ} (ht : |t| ≤ 1) (b : ℝ) :
    (∑ s : I → Bool, mass p s * exp (t * (count S s - mean p S) - b)) ≤
      exp (mean p S * t ^ 2 - b) := by
  calc
    _ = (∑ s : I → Bool, mass p s * exp (t * count S s)) *
        exp (- (t * mean p S) - b) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro s _
      rw [mul_assoc,← exp_add]
      congr 2
      ring
    _ ≤ exp (mean p S * (t + t ^ 2)) * exp (- (t * mean p S) - b) :=
      mul_le_mul_of_nonneg_right (exponential_bound p hp hp' S ht) (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

private theorem abs_tail_bound_at
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, p i ≤ 1)
    (S : Finset I) (D : ℝ) {t : ℝ} (ht : 0 ≤ t) (ht' : |t| ≤ 1) :
    (∑ s ∈ univ.filter (fun s => D ≤ |count S s - mean p S|), mass p s) ≤
      2 * exp (mean p S * t^2-t*D) := by
  let b := t*D
  let P : (I → Bool) → ℝ := fun s =>
    exp (t * (count S s - mean p S) - b) +
      exp ((-t) * (count S s - mean p S) - b)
  have hPoint (s : I → Bool) (hs : D ≤ |count S s - mean p S|) :
      1 ≤ P s := by
    rcases le_abs.mp hs with h | h
    · have hx : 1 ≤ exp (t * (count S s - mean p S) - b) :=
        one_le_exp_iff.mpr (sub_nonneg.mpr (mul_le_mul_of_nonneg_left h ht))
      exact hx.trans (le_add_of_nonneg_right (exp_pos _).le)
    · have hx : 1 ≤ exp ((-t) * (count S s - mean p S) - b) := by
        apply one_le_exp_iff.mpr
        rw [neg_mul, ← mul_neg]
        exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left h ht)
      exact hx.trans (le_add_of_nonneg_left (exp_pos _).le)
  calc
    _ ≤ ∑ s ∈ univ.filter (fun s => D ≤ |count S s - mean p S|),
          mass p s * P s := by
      apply sum_le_sum
      intro s hs
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hPoint s (mem_filter.mp hs).2) (mass_nonneg p hp hp' s)
    _ ≤ ∑ s, mass p s * P s :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun s _ _ =>
        mul_nonneg (mass_nonneg p hp hp' s) (add_nonneg (exp_pos _).le (exp_pos _).le)
    _ ≤ _ := by
      dsimp only [P]
      simp only [mul_add,sum_add_distrib]
      have hPlus := shifted_bound p hp hp' S ht' b
      have hMinus := shifted_bound p hp hp' S (by simpa only [abs_neg] using ht' : |-t| ≤ 1) b
      rw [neg_sq] at hMinus
      linarith only [hPlus,hMinus]

/-- A two-sided Chernoff bound for independent Bernoulli variables with
possibly different probabilities. -/
theorem abs_tail_bound (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, p i ≤ 1)
    (S : Finset I) {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 2) :
    (∑ s ∈ univ.filter (fun s => ε * mean p S ≤ |count S s - mean p S|), mass p s) ≤
      2 * exp (-(ε ^ 2 * mean p S / 4)) := by
  have h := abs_tail_bound_at p hp hp' S (ε*mean p S) (t := ε/2) (by positivity)
    (by rw [abs_of_nonneg (by positivity)]; linarith only [hε'])
  rwa [show mean p S*(ε/2)^2-(ε/2)*(ε*mean p S) = -(ε^2*mean p S/4) by ring] at h

/-- An absolute-threshold bound uniform for counts whose means have a
common upper bound. -/
theorem abs_tail_bound_of_mean_le (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, p i ≤ 1)
    (S : Finset I) {M D : ℝ} (hM : 0 < M) (hMean : mean p S ≤ M)
    (hD : 0 ≤ D) (hD' : D ≤ 2*M) :
    (∑ s ∈ univ.filter (fun s => D ≤ |count S s - mean p S|), mass p s) ≤
      2*exp (-(D^2/(4*M))) := by
  let t := D/(2*M)
  have ht : 0 ≤ t := by positivity
  have ht' : |t| ≤ 1 := by
    rw [abs_of_nonneg ht]
    exact (div_le_iff₀ (by positivity : 0 < 2*M)).mpr (by simpa only [one_mul] using hD')
  refine (abs_tail_bound_at p hp hp' S D ht ht').trans ?_
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) (by norm_num)
  calc
    _ ≤ M*t^2-t*D := sub_le_sub_right (mul_le_mul_of_nonneg_right hMean (sq_nonneg t)) _
    _ = _ := by dsimp only [t]; field_simp; ring

private theorem exists_simultaneous_count_from_tails {J : Type*} [Fintype J] (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, p i ≤ 1) (S : J → Finset I) (D C : ℝ)
    (hTail : ∀ j, (∑ s ∈ univ.filter (fun s => D ≤ |count (S j) s - mean p (S j)|),
      mass p s) ≤ C)
    (hUnion : (Fintype.card J : ℝ)*C < 1) :
    ∃ s : I → Bool, ∀ j, |count (S j) s - mean p (S j)| ≤ D := by
  by_contra! h
  let B : J → Finset (I → Bool) := fun j =>
    univ.filter (fun s => D ≤ |count (S j) s - mean p (S j)|)
  have hBad (s : I → Bool) : mass p s ≤ ∑ j, if s ∈ B j then mass p s else 0 := by
    obtain ⟨j,hj⟩ := h s
    have hs : s ∈ B j := mem_filter.mpr ⟨mem_univ _,hj.le⟩
    have hh := single_le_sum
      (f := fun j => if s ∈ B j then mass p s else 0)
      (fun i _ => by split_ifs <;> first | exact mass_nonneg p hp hp' s | rfl)
      (mem_univ j)
    simpa only [hs,ite_true] using hh
  have hTotal : (∑ s, mass p s) ≤ ∑ j, ∑ s ∈ B j, mass p s := by
    calc
      _ ≤ ∑ s : I → Bool, ∑ j, if s ∈ B j then mass p s else 0 :=
        sum_le_sum fun s _ => hBad s
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro j _
        rw [← sum_filter]
        simp
  have hBounds : (∑ j, ∑ s ∈ B j, mass p s) ≤
      (Fintype.card J : ℝ) * C := by
    calc
      _ ≤ ∑ _j : J, C := by
        apply sum_le_sum
        intro j _
        exact hTail j
      _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]
  rw [sum_mass] at hTotal
  exact (not_le_of_gt hUnion) (hTotal.trans hBounds)

/-- One sample simultaneously controls any finite family of counts with a
common mean, provided the union bound is strictly below one. -/
theorem exists_simultaneous_count {J : Type*} [Fintype J] (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, p i ≤ 1) (S : J → Finset I)
    (μ : ℝ) (hμ : ∀ j, mean p (S j) = μ) {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 2)
    (hUnion : (Fintype.card J : ℝ) * (2 * exp (-(ε ^ 2 * μ / 4))) < 1) :
    ∃ s : I → Bool, ∀ j, |count (S j) s - μ| ≤ ε * μ := by
  simpa only [hμ] using
    exists_simultaneous_count_from_tails p hp hp' S (ε*μ) (2*exp (-(ε^2*μ/4)))
      (fun j => by simpa only [hμ j] using abs_tail_bound p hp hp' (S j) hε hε') hUnion

/-- One sample controls all counts when their means have a common upper
bound and the absolute-threshold union bound is strictly below one. -/
theorem exists_simultaneous_count_of_mean_le {J : Type*} [Fintype J]
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, p i ≤ 1) (S : J → Finset I)
    {M D : ℝ} (hM : 0 < M) (hMean : ∀ j, mean p (S j) ≤ M)
    (hD : 0 ≤ D) (hD' : D ≤ 2*M)
    (hUnion : (Fintype.card J : ℝ)*(2*exp (-(D^2/(4*M)))) < 1) :
    ∃ s : I → Bool, ∀ j, |count (S j) s-mean p (S j)| ≤ D :=
  exists_simultaneous_count_from_tails p hp hp' S D _
    (fun j => abs_tail_bound_of_mean_le p hp hp' (S j) hM (hMean j) hD hD') hUnion

end OverfullWork.IndependentBernoulliSampling
