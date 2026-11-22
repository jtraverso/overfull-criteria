module

public import OverfullWork.RealDirectedRobustExpansion
public import OverfullWork.DirectedArcSelection

@[expose] public section


/-! Count ordered two-edge paths for the small-set estimate in
Kühn–Osthus Lemma 4.11. Diagonal pairs of targets are paid separately. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

def reverseArcs (D : Digraph V) : Digraph V := ⟨fun x y => D.Adj y x⟩

noncomputable def commonInNeighbours (D : Digraph V) (x y : V) : ℕ :=
  (univ.filter (fun u => D.Adj u x ∧ D.Adj u y)).card

noncomputable def outTo (D : Digraph V) (T : Finset V) (x : V) : ℕ :=
  (T.filter (D.Adj x)).card

theorem reverseArcs_outTo (D : Digraph V) (S : Finset V) (v : V) :
    outTo (reverseArcs D) S v = inNeighbours D S v := rfl

theorem incidences_eq_sum_outTo (D : Digraph V) (S T : Finset V) :
    (incidences D S T:ℝ) = ∑ u ∈ S, (outTo D T u:ℝ) := by
  rw [incidences_eq_sum,sum_comm]
  simp only [outTo,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem incidences_reverseArcs (D : Digraph V) (S T : Finset V) :
    incidences (reverseArcs D) T S = incidences D S T := by
  apply Nat.cast_inj (R := ℝ).mp
  rw [incidences_eq_sum_outTo]
  simp only [reverseArcs_outTo,incidences,Nat.cast_sum]

private noncomputable def bit (D : Digraph V) (x y : V) : ℝ :=
  if D.Adj x y then 1 else 0

private theorem sum_bit_out (D : Digraph V) (T : Finset V) (x : V) :
    (∑ v ∈ T, bit D x v) = (outTo D T x:ℝ) := by
  simp only [outTo,bit,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

private theorem bit_products_le_codegree (D : Digraph V) (S : Finset V) (x y : V) :
    (∑ u ∈ S, bit D u x * bit D u y) ≤ (commonInNeighbours D x y:ℝ) := by
  have hPt (u : V) : bit D u x * bit D u y =
      if D.Adj u x ∧ D.Adj u y then 1 else 0 := by
    by_cases hx : D.Adj u x <;> by_cases hy : D.Adj u y <;> simp [bit,hx,hy]
  have he : (∑ u ∈ S, bit D u x * bit D u y) =
      ((S.filter (fun u => D.Adj u x ∧ D.Adj u y)).card:ℝ) := by
    simp only [hPt,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [he]
  unfold commonInNeighbours
  exact_mod_cast card_le_card (filter_subset_filter (fun u => D.Adj u x ∧ D.Adj u y) (subset_univ S))

/-- Bound the second moment of the degrees into a target set by
counting common inneighbours of ordered pairs of targets. -/
theorem squared_outTo_le_codegree (D : Digraph V) (S T : Finset V) (c : ℝ)
    (hc : 0 ≤ c)
    (hCodegree : ∀ x y, x ≠ y → (commonInNeighbours D x y:ℝ) ≤ c) :
    (∑ u ∈ S, (outTo D T u:ℝ)^2) ≤ (T.card:ℝ)*Fintype.card V + (T.card:ℝ)^2*c := by
  have hEq : (∑ u ∈ S, (outTo D T u:ℝ)^2) =
      ∑ x ∈ T, ∑ y ∈ T, ∑ u ∈ S, bit D u x * bit D u y := by
    simp only [←sum_bit_out,pow_two,sum_mul,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    rw [sum_comm]
    apply sum_congr rfl
    intro y _
    exact sum_congr rfl (fun u _ => mul_comm (bit D u y) (bit D u x))
  rw [hEq]
  calc
    _ ≤ ∑ x ∈ T, ∑ y ∈ T, ((if x = y then (Fintype.card V:ℝ) else 0) + c) := by
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      apply (bit_products_le_codegree D S x y).trans
      by_cases he : x = y
      · have h : commonInNeighbours D x y ≤ Fintype.card V := by
          exact (card_le_card (filter_subset _ _)).trans_eq card_univ
        rw [if_pos he]
        exact (by exact_mod_cast h : (commonInNeighbours D x y:ℝ) ≤ Fintype.card V).trans
          (le_add_of_nonneg_right hc)
      · simpa only [if_neg he,zero_add] using hCodegree x y he
    _ = _ := by
      rw [pow_two]
      simp only [sum_add_distrib,sum_ite_eq,mem_univ,sum_const,nsmul_eq_mul]
      have he : ∀ x ∈ T, (if x ∈ T then (Fintype.card V:ℝ) else 0) = (Fintype.card V:ℝ) :=
        fun x hx => if_pos hx
      rw [sum_congr rfl he,sum_const,nsmul_eq_mul]
      ring

/-- The small-set estimate with explicit budgets for the diagonal and
for incidences outside the robust neighbourhood. A factor four in
the expansion term suffices for the application to Lemma 4.11. -/
theorem small_robust_neighbourhood_of_codegrees (D : Digraph V) (S : Finset V)
    (ν L c cap : ℝ) (hν : 0 ≤ ν) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hOut : ∀ x ∈ S, L ≤ (outDegree D x:ℝ))
    (hCodegree : ∀ x y, x ≠ y → (commonInNeighbours D x y:ℝ) ≤ c)
    (hDiscard : 4*ν*(Fintype.card V:ℝ)^3 ≤ (S.card:ℝ)*L^2)
    (hScale : 8*((Fintype.card V:ℝ) + cap*c) ≤ L^2)
    (hPositive : 0 < (Fintype.card V:ℝ) + cap*c) :
    min cap (4*(S.card:ℝ)) ≤ ((realNeighbourhood D ν S).card:ℝ) := by
  classical
  let B := realNeighbourhood D ν S
  let n : ℝ := Fintype.card V
  by_cases hB : cap ≤ (B.card:ℝ)
  · exact (min_le_left _ _).trans hB
  apply (min_le_right _ _).trans
  have hBad : (incidences D S Bᶜ:ℝ) ≤ ν*n^2 := by
    simp only [incidences,Nat.cast_sum]
    calc
      _ ≤ ∑ y ∈ Bᶜ, ν*n := by
        apply sum_le_sum
        intro y hy
        have hb : y ∉ B := mem_compl.mp hy
        exact (lt_of_not_ge (fun hg => hb (mem_filter.mpr ⟨mem_univ _,hg⟩))).le
      _ = (Bᶜ.card:ℝ)*(ν*n) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        have hCard : (Bᶜ.card:ℝ) ≤ n := by
          dsimp only [n]
          exact_mod_cast card_le_univ Bᶜ
        have h := mul_le_mul_of_nonneg_right hCard (mul_nonneg hν (show 0 ≤ n by positivity))
        nlinarith only [h]
  have hSplit (x : V) : (outDegree D x:ℝ) = (outTo D B x:ℝ) + outTo D Bᶜ x := by
    change (outTo D univ x:ℝ) = _
    simp only [outTo,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [sum_add_sum_compl]
  have hLoss (x : V) : (outDegree D x:ℝ)^2 ≤
      (outTo D B x:ℝ)^2 + 2*n*(outTo D Bᶜ x:ℝ) := by
    have hD : (outDegree D x:ℝ) ≤ n := by
      dsimp only [n]
      exact_mod_cast DirectedArcSelection.outDegree_le D x
    have hB' : (outTo D B x:ℝ) ≤ outDegree D x := by
      rw [hSplit]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    have hL' := mul_le_mul_of_nonneg_right (show (outDegree D x:ℝ) + outTo D B x ≤ 2*n by linarith)
      (Nat.cast_nonneg (outTo D Bᶜ x))
    nlinarith only [hSplit x,hL']
  have hLower : (S.card:ℝ)*L^2 ≤ ∑ x ∈ S, (outDegree D x:ℝ)^2 := by
    rw [← nsmul_eq_mul,←sum_const]
    exact sum_le_sum (fun x hx => by
      have h := hOut x hx
      nlinarith [mul_nonneg (sub_nonneg.mpr h) hL, sq_nonneg ((outDegree D x:ℝ)-L)])
  have hUpper : (∑ x ∈ S, (outDegree D x:ℝ)^2) ≤
      (B.card:ℝ)*(n+cap*c) + 2*ν*n^3 := by
    have hM := squared_outTo_le_codegree D S B c hc hCodegree
    have hSquare : (B.card:ℝ)^2*c ≤ (B.card:ℝ)*cap*c := by
      have h := mul_le_mul_of_nonneg_right (le_of_not_ge hB) (Nat.cast_nonneg B.card : (0:ℝ) ≤ B.card)
      nlinarith only [mul_le_mul_of_nonneg_right h hc]
    have hSum := sum_le_sum (s := S) (fun x _ => hLoss x)
    rw [sum_add_distrib,←mul_sum,←incidences_eq_sum_outTo] at hSum
    have hPay := mul_le_mul_of_nonneg_left hBad (show 0 ≤ 2*n by positivity)
    linarith only [hSum,hM,hSquare,hPay]
  have hScale' := mul_le_mul_of_nonneg_left hScale (Nat.cast_nonneg S.card : (0:ℝ) ≤ S.card)
  have hFinal : (4*(S.card:ℝ))*(n+cap*c) ≤ (B.card:ℝ)*(n+cap*c) := by
    linarith only [hLower.trans hUpper,hDiscard,hScale']
  change 4*(S.card:ℝ) ≤ (B.card:ℝ)
  by_contra! h
  exact (not_lt_of_ge hFinal) (mul_lt_mul_of_pos_right h hPositive)

end OverfullWork.DirectedRobustExpansion
