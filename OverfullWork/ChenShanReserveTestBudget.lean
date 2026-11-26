module

public import OverfullWork.ChenShanReserveCommonFamilies
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- The ambient list of single-neighborhood tests. There is one test
per outer vertex and part for (R2) and (R5), and two per outer–inner
pair for (R4). Irrelevant same-part indices can be omitted. -/
abbrev CrossingNeighborhoodTests (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) :=
  let X := S.vertices i \ S.vertices (i+1)
  let U := S.vertices (i+1)
  (↥X × Fin 3) ⊕ ((Bool × (↥X × ↥U)) ⊕ (↥X × Fin 3))

theorem crossing_neighborhood_test_budget
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i+1 ≤ l)
    (hm : 0 < m) (hk : (k:ℝ) ≤ (3/2)*(m:ℝ))
    (hρ : ρ ≤ 1)
    (hInit : 1 ≤ nestedCoreSize ρ m (i+1)) :
    (Fintype.card (CrossingNeighborhoodTests S i) : ℝ) ≤ 56*(nestedCoreSize ρ m i : ℝ)^2 := by
  unfold CrossingNeighborhoodTests
  let X := S.vertices i \ S.vertices (i+1)
  let U := S.vertices (i+1)
  let n : ℝ := nestedCoreSize ρ m i
  have hStep := nestedCoreSize_monotone_down ρ hρ m i
  have hn : 1 ≤ nestedCoreSize ρ m i := hInit.trans hStep
  have hnR : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast hn
  have hn₀ : 0 ≤ n := by linarith only [hnR]
  have hX : (X.card : ℝ) ≤ 4*n := by
    dsimp only [n,X]
    exact_mod_cast (card_le_card (sdiff_subset : X ⊆ S.vertices i)).trans
      (S.vertices_card_le hm hk i (by omega) hn)
  have hU : (U.card : ℝ) ≤ 4*n := by
    dsimp only [n,U]
    exact_mod_cast (S.vertices_card_le hm hk (i+1) hi hInit).trans (Nat.mul_le_mul_left 4 hStep)
  have hProd : (X.card : ℝ)*(U.card : ℝ) ≤ (4*n)*(4*n) :=
    mul_le_mul hX hU (Nat.cast_nonneg _) (by positivity)
  have hnSq := mul_le_mul_of_nonneg_right hnR hn₀
  change (Fintype.card ((↥X × Fin 3) ⊕ ((Bool × (↥X × ↥U)) ⊕ (↥X × Fin 3))) : ℝ) ≤ 56*n^2
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [hProd,hX,hnSq]


/-- A quadratic envelope for all five groups. The last term bounds the
distinct outer pairs, which form a subtype of the full product. -/
theorem crossing_total_test_budget
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i+1 ≤ l)
    (hm : 0 < m) (hk : (k:ℝ)/m ≤ 3/2) (hρ : ρ ≤ 1)
    (hInit : 1 ≤ nestedCoreSize ρ m (i+1))
    (hn : 2 ≤ (nestedCoreSize ρ m i : ℝ)) :
    let n : ℝ := nestedCoreSize ρ m i
    let X := S.vertices i \ S.vertices (i+1)
    2*(Fintype.card (Σ j, CrossingPart S i (crossingNext j)) : ℝ) +
      (Fintype.card (CrossingNeighborhoodTests S i) : ℝ) +
      (Fintype.card {q : ↥X × ↥X // q.1 ≠ q.2} : ℝ) ≤ 96*n^2 := by
  dsimp only
  let n : ℝ := nestedCoreSize ρ m i
  let X := S.vertices i \ S.vertices (i+1)
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hk' := (div_le_iff₀ hmR).mp hk
  have hOuter := crossing_outer_pair_test_budget S i (by omega) hm hk'
    (hInit.trans (nestedCoreSize_monotone_down ρ hρ m i))
  have hJ : (Fintype.card {q : ↥X × ↥X // q.1 ≠ q.2} : ℝ) ≤ 16*n^2 := by
    have h := Fintype.card_le_of_injective (Subtype.val : {q : ↥X × ↥X // q.1 ≠ q.2} → _) Subtype.val_injective
    exact (show (Fintype.card {q : ↥X × ↥X // q.1 ≠ q.2} : ℝ) ≤ Fintype.card (↥X × ↥X)
      by exact_mod_cast h).trans hOuter
  have hH := crossing_neighborhood_test_budget S i hi hm hk' hρ hInit
  have hV : (Fintype.card (Σ j, CrossingPart S i (crossingNext j)) : ℝ) ≤ 12*n := by
    rw [Fintype.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _ : Fin 6, 2*n := sum_le_sum fun j _ =>
        crossingPart_card_le S i hi hρ hn hk (crossingNext j)
      _ = _ := by simp [nsmul_eq_mul]; ring
  have hn₀ : 0 ≤ n := by linarith only [hn]
  have hnSq := mul_le_mul_of_nonneg_right (show 1 ≤ n by linarith only [hn]) hn₀
  nlinarith only [hJ,hH,hV,hnSq]

end OverfullWork.ChenShan
