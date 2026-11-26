module

public import OverfullWork.ChenShanSignedEdgeWeights

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]

private theorem card_filter_prod_left {U V : Type*} [Fintype U] [Fintype V] (P : U → Prop) :
    ((univ : Finset (U × V)).filter (fun x => P x.1)).card =
      (univ.filter P).card * Fintype.card V := by
  rw [← Fintype.card_subtype,← Fintype.card_subtype,← Fintype.card_prod]
  exact Fintype.card_congr
    { toFun := fun x => (⟨x.val.1,x.property⟩,x.val.2)
      invFun := fun x => ⟨(x.1.val,x.2),x.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Chen–Shan, Lemma 4.11, with edge bound 2θ/(2c-1).
Blowing up each shore by the opposite shore size gives two shores
of equal size, so Lemma 4.7 applies. Averaging over copies preserves
the original margins and the edge bound. -/
theorem exists_bounded_rectangular_signed_edge_weights
    (E : A → B → Prop) (r : A → ℝ) (s : B → ℝ) (c θ : ℝ)
    (hc : 1/2 < c) (hθ : 0 ≤ θ)
    (hA : ∀ a, c * (Fintype.card B : ℝ) ≤ ((univ.filter (E a)).card : ℝ))
    (hB : ∀ b, c * (Fintype.card A : ℝ) ≤ ((univ.filter (fun a => E a b)).card : ℝ))
    (hBalance : (∑ a, r a) = ∑ b, s b)
    (hr : ∀ a, |r a| ≤ θ * Fintype.card B) (hs : ∀ b, |s b| ≤ θ * Fintype.card A) :
    ∃ q : A → B → ℝ,
      (∀ a, (∑ b, q a b) = r a) ∧ (∀ b, (∑ a, q a b) = s b) ∧
      (∀ a b, |q a b| ≤ 2*θ/(2*c-1)) ∧ (∀ a b, ¬ E a b → q a b = 0) := by
  by_cases hA0 : IsEmpty A
  · let := hA0
    refine ⟨fun _ _ => 0, hA0.elim, ?_, hA0.elim, hA0.elim⟩
    intro b
    have h : |s b| ≤ 0 := by simpa using hs b
    have hh := abs_le.mp h
    simpa using (le_antisymm hh.2 (by simpa using hh.1)).symm
  by_cases hB0 : IsEmpty B
  · let := hB0
    refine ⟨fun _ _ => 0, ?_, fun b => hB0.elim b, fun _ b => hB0.elim b,
      fun _ b => hB0.elim b⟩
    intro a
    have h : |r a| ≤ 0 := by simpa using hr a
    have hh := abs_le.mp h
    simpa using (le_antisymm hh.2 (by simpa using hh.1)).symm
  have hAn : Nonempty A := not_isEmpty_iff.mp hA0
  have hBn : Nonempty B := not_isEmpty_iff.mp hB0
  have hAp : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos_iff.mpr hAn
  have hBp : 0 < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos_iff.mpr hBn
  let n := Fintype.card A * Fintype.card B
  let newE (x : A × B) (y : B × A) := E x.1 y.1
  let newR (x : A × B) := (Fintype.card A : ℝ) * r x.1
  let newS (y : B × A) := (Fintype.card B : ℝ) * s y.1
  have hn : (n : ℝ) = (Fintype.card A : ℝ) * Fintype.card B := by
    simp [n]
  have hnp : 0 < (n : ℝ) := by rw [hn]; positivity
  have hSizeA : Fintype.card (A × B) = n := Fintype.card_prod _ _
  have hSizeB : Fintype.card (B × A) = n := by simpa only [Fintype.card_prod,n] using Nat.mul_comm (Fintype.card B) (Fintype.card A)
  have hLeft (x : A × B) :
      (n : ℝ)/2 + (c-1/2)*n ≤ ((univ.filter (newE x)).card : ℝ) := by
    dsimp only [newE]
    rw [card_filter_prod_left,hn]
    push_cast
    have h := mul_le_mul_of_nonneg_right (hA x.1) hAp.le
    linarith only [h]
  have hRight (y : B × A) :
      (n : ℝ)/2 + (c-1/2)*n ≤ ((univ.filter (fun x => newE x y)).card : ℝ) := by
    dsimp only [newE]
    rw [card_filter_prod_left (fun a : A => E a y.1),hn]
    push_cast
    have h := mul_le_mul_of_nonneg_right (hB y.1) hBp.le
    linarith only [h]
  have hTotals : (∑ x, newR x) = ∑ y, newS y := by
    simp only [Fintype.sum_prod_type,newR,newS,sum_const,card_univ,nsmul_eq_mul]
    simp_rw [← mul_sum]
    rw [hBalance]
    ring
  have hR (x : A × B) : |newR x| ≤ θ * n := by
    simp only [newR,abs_mul,abs_of_nonneg hAp.le,hn]
    have h := mul_le_mul_of_nonneg_left (hr x.1) hAp.le
    linarith only [h]
  have hS (y : B × A) : |newS y| ≤ θ * n := by
    simp only [newS,abs_mul,abs_of_nonneg hBp.le,hn]
    have h := mul_le_mul_of_nonneg_left (hs y.1) hBp.le
    linarith only [h]
  obtain ⟨z,hzR,hzS,hzBound,hzSupport⟩ := exists_bounded_signed_edge_weights
    newE newR newS n ((c-1/2)*n) (θ*n) (mul_pos (sub_pos.mpr hc) hnp) (by positivity)
    hSizeA hSizeB hLeft hRight hTotals hR hS
  have hThreshold : θ * n / ((c-1/2)*n) = 2*θ/(2*c-1) := by
    have hGap : 0 < c-1/2 := sub_pos.mpr hc
    have hGap' : 0 < 2*c-1 := by linarith only [hc]
    field_simp [hnp.ne',hGap.ne',hGap'.ne']
  rw [hThreshold] at hzBound
  let q (a : A) (b : B) := (∑ i : B, ∑ j : A, z (a,i) (b,j)) / (n : ℝ)
  refine ⟨q,?_,?_,?_,?_⟩
  · intro a
    simp only [q,← sum_div]
    rw [sum_comm]
    have hCopy (i : B) : (∑ b : B, ∑ j : A, z (a,i) (b,j)) = newR (a,i) := by
      rw [← Fintype.sum_prod_type]
      exact hzR (a,i)
    simp only [hCopy,newR,sum_const,card_univ,nsmul_eq_mul,hn]
    field_simp [hAp.ne',hBp.ne']
  · intro b
    simp only [q,← sum_div]
    have hOuter (i : B) : (∑ a : A, ∑ j : A, z (a,i) (b,j)) =
        ∑ j : A, ∑ a : A, z (a,i) (b,j) := sum_comm
    rw [sum_comm]
    simp_rw [hOuter]
    rw [sum_comm]
    have hCopy (j : A) : (∑ i : B, ∑ a : A, z (a,i) (b,j)) = newS (b,j) := by
      rw [sum_comm]
      simpa only [Fintype.sum_prod_type] using hzS (b,j)
    simp only [hCopy,newS,sum_const,card_univ,nsmul_eq_mul,hn]
    field_simp [hAp.ne',hBp.ne']
  · intro a b
    dsimp only [q]
    rw [abs_div,abs_of_pos hnp]
    apply (div_le_iff₀ hnp).mpr
    calc
      _ ≤ ∑ i : B, |∑ j : A, z (a,i) (b,j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : B, ∑ _j : A, 2*θ/(2*c-1) := by
        apply sum_le_sum
        intro i _
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _ => hzBound (a,i) (b,j)))
      _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,hn]; ring
  · intro a b hab
    simp [q,fun i j => hzSupport (a,i) (b,j) hab]

end OverfullWork.ChenShan
