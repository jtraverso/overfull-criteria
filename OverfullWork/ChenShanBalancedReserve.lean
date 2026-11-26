module

public import OverfullWork.ChenShanRectangularSignedWeights
public import OverfullWork.ChenShanReserveTarget

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {J : Type*} [Fintype J] {V : J → Type*} [∀ i, Fintype (V i)]

noncomputable def reserveOutDegree {A B : Type*} [Fintype B] (E : A → B → Prop)
    (a : A) : ℝ :=
  (univ.filter (E a)).card

noncomputable def reserveInDegree {A B : Type*} [Fintype A] (E : A → B → Prop)
    (b : B) : ℝ :=
  (univ.filter (fun a => E a b)).card

noncomputable def reservePairSize {A B : Type*} [Fintype A] [Fintype B] (E : A → B → Prop) : ℝ :=
  ∑ a, reserveOutDegree E a

theorem sum_reserveInDegree {A B : Type*} [Fintype A] [Fintype B] (E : A → B → Prop) :
    (∑ b, reserveInDegree E b) = reservePairSize E := by
  simp only [reserveInDegree,reservePairSize,reserveOutDegree,card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]
  exact sum_comm

private theorem sum_constant_edge_weight {A B : Type*} [Fintype B] (E : A → B → Prop)
    (a : A) (μ : ℝ) : (∑ b, if E a b then μ else 0) = μ * reserveOutDegree E a := by
  rw [← sum_filter]
  simp [reserveOutDegree,nsmul_eq_mul,mul_comm]

/-- Chen–Shan, Lemma 4.12. For a cyclic family of directed pairs, one can
balance the incident probabilities with the explicit constant 8/(2c-1).
Using a permutation in the statement also allows several disjoint cycles. -/
theorem exists_balanced_reserve_probabilities [Nonempty J]
    (next : J ≃ J) (E : (i j : J) → V i → V j → Prop)
    (c θ μ e : ℝ) (hc : 1/2 < c) (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1/4)
    (hθtight : (8/(2*c-1))*θ < 1/2) (hμ : 0 < μ) (hμupper : μ < 1/4) (he : 0 < e)
    (hOut : ∀ i a, c * (Fintype.card (V (next i)) : ℝ) ≤ reserveOutDegree (E i (next i)) a)
    (hIn : ∀ i b, c * (Fintype.card (V i) : ℝ) ≤ reserveInDegree (E i (next i)) b)
    (hSizes : ∀ i, |reservePairSize (E i (next i))-e| ≤ θ*e)
    (hBalance : ∀ i a, let out := reserveOutDegree (E i (next i)) a
      let in' := reserveInDegree (E (next.symm i) i) a
      |out-in'| ≤ θ * min out in') :
    ∃ p : (i : J) → V i → V (next i) → ℝ,
      (∀ i a b, ¬ E i (next i) a b → p i a b = 0) ∧
      (∀ i a b, E i (next i) a b →
        p i a b ∈ Set.Ioo (0 : ℝ) 1 ∧ |p i a b-μ| ≤ μ*((8/(2*c-1))*θ)) ∧
      (∀ i (a : V (next i)), (∑ b, p (next i) a b) = ∑ b, p i b a) ∧
      ∀ i, (∑ a, ∑ b, p i a b) =
        μ * (∑ j, reservePairSize (E j (next j))) / Fintype.card J := by
  let o (i : J) (a : V i) := reserveOutDegree (E i (next i)) a
  let l (i : J) (a : V i) := reserveInDegree (E (next.symm i) i) a
  let n (i : J) := reservePairSize (E i (next i))
  let average := (∑ i, n i) / (Fintype.card J : ℝ)
  have hcard : 0 < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
  have hAverage : |average-e| ≤ θ*e := by
    have heq : average-e = (∑ i, (n i-e)) / Fintype.card J := by
      simp only [average,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul]
      field_simp [hcard.ne']
    rw [heq,abs_div,abs_of_pos hcard]
    apply (div_le_iff₀ hcard).mpr
    calc
      _ ≤ ∑ i, |n i-e| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : J, θ*e := sum_le_sum fun i _ => hSizes i
      _ = _ := by simp [nsmul_eq_mul,mul_comm]
  have hInSum (i : J) : (∑ a, l i a) = n (next.symm i) := by
    simp only [l,n,sum_reserveInDegree]
    exact congrArg (fun j => reservePairSize (E (next.symm i) j))
      (next.apply_symm_apply i).symm
  let target (i : J) (a : V i) := μ*average*(o i a+l i a)/(n (next.symm i)+n i)
  have hDen (i : J) : 0 < n (next.symm i)+n i := by
    have h1 := (abs_le.mp (hSizes (next.symm i))).1
    have h2 := (abs_le.mp (hSizes i)).1
    have ht := mul_le_mul_of_nonneg_right hθsmall he.le
    change -(θ*e) ≤ n (next.symm i)-e at h1
    change -(θ*e) ≤ n i-e at h2
    linarith only [h1,h2,he,ht]
  have hTargetSum (i : J) : (∑ a, target i a) = μ*average := by
    dsimp only [target]
    rw [← sum_div,← mul_sum,sum_add_distrib,hInSum]
    change μ*average*(n i+n (next.symm i))/(n (next.symm i)+n i) = μ*average
    field_simp [(hDen i).ne']
    ring
  have hOutCorrection (i : J) (a : V i) :
      |target i a-μ*o i a| ≤ 4*μ*θ*o i a := by
    have h := (hBalance i a).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hθ)
    rw [abs_sub_comm] at h
    exact reserve_target_deviation e average _ _ μ θ _ _ he hμ.le hθ hθsmall
      (Nat.cast_nonneg _) hAverage (hSizes (next.symm i)) (hSizes i) h
  have hInCorrection (i : J) (a : V i) :
      |target i a-μ*l i a| ≤ 4*μ*θ*l i a := by
    have h := (hBalance i a).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hθ)
    simpa only [target,add_comm (o i a) (l i a)] using
      reserve_target_deviation e average _ _ μ θ _ _ he hμ.le hθ hθsmall
        (show 0 ≤ l i a from Nat.cast_nonneg _) hAverage (hSizes (next.symm i)) (hSizes i) h
  let r (i : J) (a : V i) := target i a-μ*o i a
  let s (i : J) (b : V (next i)) := target (next i) b-μ*reserveInDegree (E i (next i)) b
  have hIncomingCorrection (i : J) (b : V (next i)) :
      |s i b| ≤ (4*μ*θ)*reserveInDegree (E i (next i)) b := by
    have hEq := congrArg (fun j => reserveInDegree (E j (next i)) b) (next.symm_apply_apply i)
    have h := hInCorrection (next i) b
    dsimp only [l] at h
    rw [hEq] at h
    exact h
  have hMargins (i : J) : (∑ a, r i a) = ∑ b, s i b := by
    simp only [r,s,sum_sub_distrib,hTargetSum,← mul_sum,sum_reserveInDegree]
    rfl
  have hWeights (i : J) : ∃ q : V i → V (next i) → ℝ,
      (∀ a, ∑ b, q a b = r i a) ∧ (∀ b, ∑ a, q a b = s i b) ∧
      (∀ a b, |q a b| ≤ μ*((8/(2*c-1))*θ)) ∧
      (∀ a b, ¬ E i (next i) a b → q a b = 0) := by
    have hR (a : V i) : |r i a| ≤ (4*μ*θ)*Fintype.card (V (next i)) :=
      (hOutCorrection i a).trans (mul_le_mul_of_nonneg_left
        (by
          change ((univ.filter (E i (next i) a)).card : ℝ) ≤ _
          exact_mod_cast (card_filter_le _ _).trans_eq card_univ) (by positivity))
    have hS (b : V (next i)) : |s i b| ≤ (4*μ*θ)*Fintype.card (V i) :=
      (hIncomingCorrection i b).trans (mul_le_mul_of_nonneg_left
        (by
          change ((univ.filter (fun a => E i (next i) a b)).card : ℝ) ≤ _
          exact_mod_cast (card_filter_le _ _).trans_eq card_univ) (by positivity))
    obtain ⟨q,hqR,hqS,hqB,hqSupport⟩ := exists_bounded_rectangular_signed_edge_weights
      (E i (next i)) (r i) (s i) c (4*μ*θ) hc (by positivity)
      (hOut i) (hIn i) (hMargins i) hR hS
    refine ⟨q,hqR,hqS,fun a b => (hqB a b).trans_eq ?_,hqSupport⟩
    ring
  choose q hqR hqS hqB hqSupport using hWeights
  let p (i : J) (a : V i) (b : V (next i)) := (if E i (next i) a b then μ else 0)+q i a b
  have hRow (i : J) (a : V i) : (∑ b, p i a b) = target i a := by
    rw [show (∑ b,p i a b) = (∑ b, if E i (next i) a b then μ else 0)+∑ b,q i a b
      from sum_add_distrib]
    rw [sum_constant_edge_weight,hqR]
    dsimp only [r,o]
    ring
  have hCol (i : J) (b : V (next i)) : (∑ a, p i a b) = target (next i) b := by
    rw [show (∑ a,p i a b) = (∑ a, if E i (next i) a b then μ else 0)+∑ a,q i a b
      from sum_add_distrib]
    rw [sum_constant_edge_weight (fun b a => E i (next i) a b),hqS]
    dsimp only [s,reserveInDegree,reserveOutDegree]
    ring
  refine ⟨p,?_,?_,?_,?_⟩
  · intro i a b h
    simp [p,h,hqSupport i a b h]
  · intro i a b h
    have hSmall := mul_lt_mul_of_pos_left hθtight hμ
    have hQ := abs_le.mp (hqB i a b)
    simp only [p,h,ite_true]
    constructor
    · exact ⟨by linarith only [hSmall,hQ.1,hμ],by linarith only [hSmall,hQ.2,hμupper]⟩
    · simpa only [add_sub_cancel_left] using hqB i a b
  · intro i a
    rw [hRow,hCol]
  · intro i
    simp_rw [hRow,hTargetSum]
    dsimp only [average]
    ring

end OverfullWork.ChenShan
