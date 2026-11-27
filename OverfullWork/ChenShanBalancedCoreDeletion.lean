module

public import OverfullWork.KLOSRobustComponents
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset KLOS PrunedCore RobustExpansion
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Removing vertices from the reference set costs at most their number
in each internal degree. -/
theorem neighboursIn_after_vertex_deletion (S D : Finset V) (v : V) :
    neighboursIn G S v ≤ neighboursIn G (S \ D) v + D.card := by
  simp only [neighboursIn_eq_filter_card]
  have hSub : S.filter (G.Adj v) ⊆ ((S \ D).filter (G.Adj v)) ∪ D := by
    intro x hx
    obtain ⟨hS,ha⟩ := mem_filter.mp hx
    by_cases hD : x ∈ D
    · exact mem_union_right _ hD
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hS,hD⟩,ha⟩)
  exact (card_le_card hSub).trans (card_union_le _ _)

private theorem robustAcross_filter (A B X : Finset V) (ν : ℝ) :
    robustNeighbourhoodIn G ν (A ∪ B) X ∩ B =
      B.filter (fun v => ν * ((A ∪ B).card : ℝ) ≤ neighboursIn G X v) := by
  ext v
  simp only [robustNeighbourhoodIn,mem_filter,mem_inter,mem_union]
  tauto

set_option maxHeartbeats 1000000 in
/-- Chen–Shan Lemma 3.12(2), in the repository normalization where
the robust threshold is measured on the union of the two shores. -/
theorem expandsAcross_after_balanced_vertex_deletion
    (A B D E : Finset V) (hAB : Disjoint A B) (hSize : A.card = B.card)
    (hD : D ⊆ A) (hE : E ⊆ B) (hDE : D.card = E.card)
    {ν τ : ℝ} (hν : 0 ≤ ν) (hντ : ν ≤ τ) (hτ : τ < 1/4)
    (hSmall : (D.card : ℝ) ≤ ν * A.card)
    (hExp : ExpandsAcross G ν τ A B) :
    ExpandsAcross G (ν/2) (2*τ) (A \ D) (B \ E) := by
  let A' := A \ D
  let B' := B \ E
  have hA' : A'.card + D.card = A.card := by
    exact card_sdiff_add_card_eq_card hD
  have hB' : B'.card + E.card = B.card := by
    exact card_sdiff_add_card_eq_card hE
  have hSize' : A'.card = B'.card := by omega
  have hAB' : Disjoint A' B' := hAB.mono sdiff_subset sdiff_subset
  have hUnion : ((A ∪ B).card : ℝ) = 2 * A.card := by
    rw [card_union_of_disjoint hAB,← hSize,Nat.cast_add]
    ring
  have hUnion' : ((A' ∪ B').card : ℝ) = 2 * A'.card := by
    rw [card_union_of_disjoint hAB',← hSize',Nat.cast_add]
    ring
  have hA'le : (A'.card : ℝ) ≤ A.card := by exact_mod_cast card_le_card (sdiff_subset : A' ⊆ A)
  have hHalf : (A.card : ℝ) ≤ 2*A'.card := by
    have hEq : (A'.card : ℝ) + D.card = A.card := by exact_mod_cast hA'
    have hBound := mul_le_mul_of_nonneg_right (show ν ≤ 1/2 by linarith only [hντ,hτ])
      (Nat.cast_nonneg (α := ℝ) A.card)
    linarith only [hEq,hSmall,hBound]
  intro X hX hLower hUpper
  change X ⊆ A' at hX
  change (2*τ) * (A'.card:ℝ) ≤ (X.card:ℝ) at hLower
  change (X.card:ℝ) ≤ (1-2*τ) * (A'.card:ℝ) at hUpper
  have hNonnegτ : 0 ≤ τ := hν.trans hντ
  have hLo : τ * (A.card:ℝ) ≤ X.card := by
    have h := mul_le_mul_of_nonneg_left hHalf hNonnegτ
    linarith only [h,hLower]
  have hHi : (X.card:ℝ) ≤ (1-τ)*A.card := by
    have hStep := mul_le_mul_of_nonneg_right (show 1 - 2*τ ≤ 1-τ by linarith only [hNonnegτ])
      (Nat.cast_nonneg (α := ℝ) A'.card)
    have hRight := mul_le_mul_of_nonneg_left hA'le (show 0 ≤ 1-τ by linarith only [hτ])
    exact hUpper.trans (hStep.trans hRight)
  let R := B.filter (fun v => ν * ((A ∪ B).card : ℝ) ≤ neighboursIn G X v)
  let R' := B'.filter (fun v => (ν/2) * ((A' ∪ B').card : ℝ) ≤ neighboursIn G X v)
  have hOld := hExp X (hX.trans sdiff_subset) hLo hHi
  rw [robustAcross_filter] at hOld ⊢
  change (X.card:ℝ)+ν*((A ∪ B).card:ℝ) ≤ R.card at hOld
  change (X.card:ℝ)+(ν/2)*((A' ∪ B').card:ℝ) ≤ R'.card
  have hScale : (ν/2)*((A' ∪ B').card:ℝ) ≤ ν*((A ∪ B).card:ℝ) := by
    rw [hUnion',hUnion]
    have h := mul_le_mul_of_nonneg_left hA'le hν
    have hPos : 0 ≤ ν*(A.card:ℝ) := by positivity
    nlinarith only [h,hPos]
  have hSub : R ⊆ R' ∪ E := by
    intro v hv
    obtain ⟨hvB,hvN⟩ := mem_filter.mp hv
    by_cases hEv : v ∈ E
    · exact mem_union_right _ hEv
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hvB,hEv⟩,hScale.trans hvN⟩)
  have hCount : (R.card:ℝ) ≤ (R'.card:ℝ) + E.card := by
    exact_mod_cast (card_le_card hSub).trans (card_union_le R' E)
  rw [hUnion] at hOld
  rw [hUnion']
  have hLoss : (E.card:ℝ) ≤ ν * A.card := by rw [← hDE]; exact hSmall
  have hMargin := mul_le_mul_of_nonneg_left hA'le hν
  nlinarith only [hLoss,hCount,hOld,hMargin]

omit [Fintype V] in
/-- Making the shore size divisible by `b` moves fewer than `b`
vertices from each side. The retained sizes are equal. -/
theorem exists_balanced_divisible_core_deletion
    (A B : Finset V) (hSize : A.card = B.card) (b : ℕ) (hb : 0 < b) :
    ∃ D E : Finset V, D ⊆ A ∧ E ⊆ B ∧ D.card = E.card ∧ D.card < b ∧
      (A \ D).card = (B \ E).card ∧ b ∣ (A \ D).card := by
  let t := A.card % b
  obtain ⟨D,hD,hDt⟩ := exists_subset_card_eq (s := A) (Nat.mod_le A.card b)
  obtain ⟨E,hE,hEt⟩ := exists_subset_card_eq (s := B) (show t ≤ B.card by rw [← hSize]; exact Nat.mod_le _ _)
  have hA := card_sdiff_add_card_eq_card hD
  have hB := card_sdiff_add_card_eq_card hE
  have ht : t < b := Nat.mod_lt _ hb
  have hRound := Nat.mod_add_div A.card b
  refine ⟨D,E,hD,hE,hDt.trans hEt.symm,hDt ▸ ht,by omega,?_⟩
  exact ⟨A.card / b,by dsimp [t] at *; omega⟩


/-- The recut used before the regularity labels in §5.1.1. It preserves
the bipartite robust expansion and gives the pointwise degree loss on
both shores, with the new exceptional vertices specified explicitly. -/
theorem exists_divisible_robust_core_trimming
    (A B : Finset V) (hAB : Disjoint A B) (hSize : A.card = B.card)
    (b : ℕ) (hb : 0 < b)
    {ν τ : ℝ} (hν : 0 ≤ ν) (hντ : ν ≤ τ) (hτ : τ < 1/4)
    (hRoom : ((b-1 : ℕ):ℝ) ≤ ν*A.card)
    (hExp : ExpandsAcross G ν τ A B) :
    ∃ D E : Finset V, D ⊆ A ∧ E ⊆ B ∧ (D ∪ E).card < 2*b ∧
      (A \ D).card = (B \ E).card ∧ b ∣ (A \ D).card ∧
      ExpandsAcross G (ν/2) (2*τ) (A \ D) (B \ E) ∧
      (∀ v, neighboursIn G A v ≤ neighboursIn G (A \ D) v + D.card) ∧
      (∀ v, neighboursIn G B v ≤ neighboursIn G (B \ E) v + D.card) := by
  obtain ⟨D,E,hD,hE,hDE,hCount,hEq,hDiv⟩ := exists_balanced_divisible_core_deletion A B hSize b hb
  have hSizeY : (D ∪ E).card < 2*b := by
    have h := card_union_le D E
    omega
  have hSmall : (D.card:ℝ) ≤ ν*A.card :=
    (show (D.card:ℝ) ≤ ((b-1 : ℕ):ℝ) by exact_mod_cast (show D.card ≤ b-1 by omega)).trans hRoom
  refine ⟨D,E,hD,hE,hSizeY,hEq,hDiv,
    expandsAcross_after_balanced_vertex_deletion G A B D E hAB hSize hD hE hDE hν hντ hτ hSmall hExp,
    neighboursIn_after_vertex_deletion G A D,?_⟩
  intro v
  rw [hDE]
  exact neighboursIn_after_vertex_deletion G B E v

end OverfullWork.ChenShan
