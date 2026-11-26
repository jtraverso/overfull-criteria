module

public import Mathlib.Tactic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Sum

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical BigOperators

variable {A B V : Type*}

noncomputable def bipartiteCutEdges [Fintype A] [Fintype B]
    (E : A → B → Prop) (S : Finset A) (T : Finset B) : Finset (A × B) :=
  univ.filter fun e => E e.1 e.2 ∧ ((e.1 ∈ S ∧ e.2 ∉ T) ∨ (e.1 ∉ S ∧ e.2 ∈ T))

private theorem sum_bipartite_row_degrees [Fintype A] [Fintype B]
    (E : A → B → Prop) (S : Finset A) :
    (∑ a ∈ S, (univ.filter (E a)).card) =
      ∑ a : A, ∑ b : B, if E a b ∧ a ∈ S then 1 else 0 := by
  have hS : univ.filter (fun a : A => a ∈ S) = S := by ext; simp
  calc
    _ = ∑ a ∈ univ.filter (fun a : A => a ∈ S), ∑ b : B, if E a b then 1 else 0 := by
      rw [hS]
      simp only [card_filter]
    _ = _ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases h : a ∈ S <;> simp [h, -Finset.sum_boole]

/-- Degree incidences in the selected vertices count a cut edge once
and an internal edge twice. -/
theorem bipartite_cut_incidence_count [Fintype A] [Fintype B]
    (E : A → B → Prop) (S : Finset A) (T : Finset B) :
    (∑ a ∈ S, (univ.filter (E a)).card) + (∑ b ∈ T, (univ.filter (fun a => E a b)).card) =
      (bipartiteCutEdges E S T).card + 2*((S ×ˢ T).filter fun e => E e.1 e.2).card := by
  have hInternal : (S ×ˢ T).filter (fun e => E e.1 e.2) =
      univ.filter (fun e => E e.1 e.2 ∧ e.1 ∈ S ∧ e.2 ∈ T) := by
    ext e
    simp only [mem_filter,mem_product,mem_univ,true_and]
    tauto
  rw [sum_bipartite_row_degrees E S,sum_bipartite_row_degrees (fun b a => E a b) T]
  rw [sum_comm (s := (univ : Finset B)) (t := (univ : Finset A)),hInternal]
  simp only [bipartiteCutEdges,card_filter,Fintype.sum_prod_type,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases hab : E a b <;> by_cases ha : a ∈ S <;> by_cases hb : b ∈ T <;>
    simp [hab,ha,hb]

/-- A cut selecting at most n vertices has at least gap times its order
in crossing edges, under the minimum degree in Chen–Shan, Lemma 4.7. -/
theorem bipartite_cut_lower_bound_small [Fintype A] [Fintype B]
    (E : A → B → Prop) (S : Finset A) (T : Finset B) (n gap : ℝ)
    (hSize : (S.card : ℝ) + T.card ≤ n)
    (hA : ∀ a, n/2+gap ≤ ((univ.filter (E a)).card : ℝ))
    (hB : ∀ b, n/2+gap ≤ ((univ.filter (fun a => E a b)).card : ℝ)) :
    gap*((S.card : ℝ) + T.card) ≤ ((bipartiteCutEdges E S T).card : ℝ) := by
  have hSumA : (n/2+gap)*(S.card : ℝ) ≤ ∑ a ∈ S, ((univ.filter (E a)).card : ℝ) := by
    calc
      _ = ∑ _ ∈ S, (n/2+gap) := by simp [nsmul_eq_mul,mul_comm]; ring
      _ ≤ _ := sum_le_sum (fun a _ => hA a)
  have hSumB : (n/2+gap)*(T.card : ℝ) ≤ ∑ b ∈ T, ((univ.filter (fun a => E a b)).card : ℝ) := by
    calc
      _ = ∑ _ ∈ T, (n/2+gap) := by simp [nsmul_eq_mul,mul_comm]; ring
      _ ≤ _ := sum_le_sum (fun b _ => hB b)
  have hRaw := congrArg (fun m : ℕ => (m : ℝ)) (bipartite_cut_incidence_count E S T)
  push_cast at hRaw
  have hInt : (((S ×ˢ T).filter fun e => E e.1 e.2).card : ℝ) ≤ (S.card : ℝ)*T.card := by
    exact_mod_cast ((card_filter_le (S ×ˢ T) _).trans_eq (card_product S T))
  have hProd := mul_nonneg (sub_nonneg.mpr hSize) (show 0 ≤ (S.card : ℝ) + T.card by positivity)
  nlinarith [sq_nonneg ((S.card : ℝ) - T.card)]

/-- Applying the degree bound to the smaller side gives the capacity
lower bound for every cut. -/
theorem bipartite_cut_lower_bound [Fintype A] [Fintype B]
    (E : A → B → Prop) (S : Finset A) (T : Finset B) (n : ℕ) (gap : ℝ)
    (hGap : 0 ≤ gap) (hSizeA : Fintype.card A = n) (hSizeB : Fintype.card B = n)
    (hA : ∀ a, (n : ℝ)/2+gap ≤ ((univ.filter (E a)).card : ℝ))
    (hB : ∀ b, (n : ℝ)/2+gap ≤ ((univ.filter (fun a => E a b)).card : ℝ)) :
    gap * min ((S.card : ℝ) + T.card) ((Sᶜ.card : ℝ) + Tᶜ.card) ≤
      ((bipartiteCutEdges E S T).card : ℝ) := by
  have hS : (S.card : ℝ) + Sᶜ.card = n := by exact_mod_cast (card_add_card_compl S).trans hSizeA
  have hT : (T.card : ℝ) + Tᶜ.card = n := by exact_mod_cast (card_add_card_compl T).trans hSizeB
  by_cases h : (S.card : ℝ) + T.card ≤ n
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hGap).trans
      (bipartite_cut_lower_bound_small E S T n gap h hA hB)
  · have h' : (Sᶜ.card : ℝ) + Tᶜ.card ≤ n := by linarith
    have hEq : bipartiteCutEdges E Sᶜ Tᶜ = bipartiteCutEdges E S T := by
      ext
      simp only [bipartiteCutEdges,mem_filter,mem_univ,true_and,mem_compl]
      tauto
    rw [← hEq]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hGap).trans
      (bipartite_cut_lower_bound_small E Sᶜ Tᶜ n gap h' hA hB)

/-- The second cut inequality of Lemma 4.7, from zero total demand. -/
theorem abs_sum_demands_le_min_shore [Fintype V] [DecidableEq V] (f : V → ℝ) (d : ℝ) (S : Finset V)
    (hZero : ∑ v : V, f v = 0) (hBound : ∀ v, |f v| ≤ d) :
    |∑ v ∈ S, f v| ≤ d * min (S.card : ℝ) (Sᶜ.card : ℝ) := by
  have hD (T : Finset V) : |∑ v ∈ T, f v| ≤ d*(T.card : ℝ) := by
    calc
      _ ≤ ∑ v ∈ T, |f v| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ T, d := sum_le_sum (fun v _ => hBound v)
      _ = _ := by simp [nsmul_eq_mul,mul_comm]
  have hSum : (∑ v ∈ Sᶜ, f v) + ∑ v ∈ S, f v = 0 := by
    rw [sum_compl_add_sum,hZero]
  have hAbs : |∑ v ∈ Sᶜ, f v| = |∑ v ∈ S, f v| := by
    have hEq : (∑ v ∈ Sᶜ, f v) = -(∑ v ∈ S, f v) := by linarith
    rw [hEq,abs_neg]
  rcases le_total S.card Sᶜ.card with h | h
  · rw [min_eq_left (by exact_mod_cast h)]
    exact hD S
  · rw [min_eq_right (by exact_mod_cast h),← hAbs]
    exact hD Sᶜ

/-- The capacity d/gap per edge dominates the net demand of every cut. -/
theorem bipartite_demands_cut_capacity [Fintype A] [Fintype B]
    (E : A → B → Prop) (r : A → ℝ) (s : B → ℝ) (n : ℕ) (gap d : ℝ)
    (hGap : 0 < gap) (hd : 0 ≤ d) (hSizeA : Fintype.card A = n) (hSizeB : Fintype.card B = n)
    (hA : ∀ a, (n : ℝ)/2+gap ≤ ((univ.filter (E a)).card : ℝ))
    (hB : ∀ b, (n : ℝ)/2+gap ≤ ((univ.filter (fun a => E a b)).card : ℝ))
    (hBalance : (∑ a, r a) = ∑ b, s b)
    (hr : ∀ a, |r a| ≤ d) (hs : ∀ b, |s b| ≤ d) (S : Finset A) (T : Finset B) :
    |(∑ a ∈ S, r a) - ∑ b ∈ T, s b| ≤ (d/gap) * (bipartiteCutEdges E S T).card := by
  let b : A ⊕ B → ℝ := Sum.elim r (fun b => -s b)
  have hZero : (∑ v, b v) = 0 := by
    rw [Fintype.sum_sum_type]
    change (∑ a, r a) + ∑ b, -s b = 0
    rw [sum_neg_distrib,hBalance,add_neg_cancel]
  have hBd : ∀ v, |b v| ≤ d := by
    rintro (a | b')
    · exact hr a
    · simpa [b] using hs b'
  have hComplement : (S.disjSum T)ᶜ = Sᶜ.disjSum Tᶜ := by
    ext v
    rcases v with a | b' <;> simp
  have hDem := abs_sum_demands_le_min_shore b d (S.disjSum T) hZero hBd
  rw [sum_disjSum, hComplement,card_disjSum,card_disjSum] at hDem
  change |(∑ a ∈ S, r a) + ∑ b ∈ T, -s b| ≤
    d * min (↑(S.card + T.card) : ℝ) ↑(Sᶜ.card + Tᶜ.card) at hDem
  rw [sum_neg_distrib,← sub_eq_add_neg] at hDem
  push_cast at hDem
  let size := min ((S.card : ℝ) + T.card) ((Sᶜ.card : ℝ) + Tᶜ.card)
  calc
    _ ≤ d*size := hDem
    _ = (d/gap)*(gap*size) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (bipartite_cut_lower_bound E S T n gap hGap.le
      hSizeA hSizeB hA hB) (div_nonneg hd hGap.le)

end OverfullWork.ChenShan
