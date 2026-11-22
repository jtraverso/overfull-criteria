module

public import OverfullWork.KuhnOsthusPhysicalChordBalance
public import OverfullWork.KuhnOsthusExceptionalPairStability
public import OverfullWork.KuhnOsthusExtenderIteration

@[expose] public section


/-! Claim 5 of Kühn–Osthus Lemma 9.5. After each deletion, the
free successor pairs pay both the removed vertices and the
semidegrees used by previous cycles. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u

/-- The free successor pairs support Hamilton completion after any
deletion bounded by the same number of earlier cycles. This applies
to one contracted system even if other systems have the same shortcuts. -/
theorem exists_chord_path_completion_after_deletion
    (d η ν τ γ : ℝ) (hν : 0 < ν) (hWidth : η+ν ≤ τ) (hη : 0 < η)
    (hη1 : η ≤ 1) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 0 < d)
    (hCost : ν ≤ d*τ) (hDegrees : γ ≤ d) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {n : ℕ}
      (B L D : Digraph V) (c : V → Fin (n+1)) (q : ℕ)
      (ε ρ δ : ℝ) (r : Fin (n+1) → ℕ),
      let s := finRotate (n+1)
      let A (j : Fin (n+1)) := (univ : Finset V).filter (fun v => c v = j)
      let S (j : Fin (n+1)) := freeOut D c j
      let T (j : Fin (n+1)) := freeIn D c (s j)
      L ≤ B → (∀ v, inDegree L v ≤ q ∧ outDegree L v ≤ q) →
      0 ≤ ε → 0 ≤ δ → ρ ≤ 1 → d ≤ ρ-2*η → 2*(ε+δ) ≤ η →
      (∀ j, IsSuperregularPair B ε ρ (A j) (A (s j))) →
      IsDirectedPathSystem D →
      (∀ j, (S j).card = (T j).card) →
      (∀ j, ∃ v, v ∈ freeIn D c j ∧ v ∈ S j) →
      (∀ j, N ≤ (S j).card) →
      (∀ j, (q:ℝ) ≤ δ*((S j).card:ℝ)*η) →
      (∀ j, ε*((A j).card:ℝ)+((A j \ S j).card:ℝ)+q ≤ η*((S j).card:ℝ)) →
      (∀ j, ε*((A (s j)).card:ℝ)+((A (s j) \ T j).card:ℝ)+q ≤ η*((T j).card:ℝ)) →
      (∀ j, 0 < r j ∧ η*((S j).card:ℝ) ≤ r j ∧ (r j:ℝ) ≤ d*((S j).card:ℝ)) →
      ∃ F : Equiv.Perm V, HasSpanningCycle (fun x y => F x = y) ∧
        (∀ x y, D.Adj x y → F x = y) ∧
        ∀ x, (D ⊔ (B \ L)).Adj x (F x) := by
  obtain ⟨N,hN⟩ := exists_hamilton_completion_of_physical_successor_pairs.{u}
    d η ν τ γ hν hWidth hη.le hτγ hγ hd hCost hDegrees
  refine ⟨max N 1,?_⟩
  intro V _ n B L D c q ε ρ δ r s A S T hLB hDeg hε hδ hρ hDensity hTol hPairs hPath hBal
    hOverlap hSize hBudget hLeft hRight hr
  have hρ₀ : 0 ≤ ρ := by linarith only [hd,hDensity,hη]
  have hLow : d ≤ ρ-η := by linarith only [hDensity,hη]
  have hSubA (j : Fin (n+1)) : S j ⊆ A j :=
    fun _ hv => mem_filter.mpr ⟨mem_univ _,(mem_freeOut.mp hv).1⟩
  have hSubB (j : Fin (n+1)) : T j ⊆ A (s j) :=
    fun _ hv => mem_filter.mpr ⟨mem_univ _,(mem_freeIn.mp hv).1⟩
  have hNew (j : Fin (n+1)) : IsSuperregularPair (B \ L) η ρ (S j) (T j) := by
    have hPos : 0 < (S j).card := (le_max_right N 1).trans (hSize j)
    have hPos' : 0 < (T j).card := (hBal j) ▸ hPos
    apply IsSuperregularPair.on_pair_remainder B L hLB (A j) (A (s j)) (S j) (T j)
      (hSubA j) (hSubB j) (card_pos.mp hPos) (card_pos.mp hPos') ρ ε η δ q
      hρ₀ hρ hη hη1 hδ
    · have h := hLeft j
      linarith only [h,Nat.cast_nonneg (α := ℝ) (A j \ S j).card,Nat.cast_nonneg (α := ℝ) q]
    · have h := hRight j
      linarith only [h,Nat.cast_nonneg (α := ℝ) (A (s j) \ T j).card,Nat.cast_nonneg (α := ℝ) q]
    · exact hTol
    · simpa only [mul_assoc,mul_left_comm,mul_comm] using hBudget j
    · exact hLeft j
    · exact hRight j
    · exact fun v _ => (hDeg v).2
    · exact fun v _ => (hDeg v).1
    · exact hPairs j
  apply hN D (B \ L) c r hPath hBal hOverlap
    (fun j => (le_max_left N 1).trans (hSize j)) hr
  · intro j X hx Y hy hX hY
    obtain ⟨_,_,hRect⟩ := (hNew j).physical_lower_bounds (B \ L) (S j) (T j) ρ η
    rw [hBal j] at hY
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg X.card))
      (Nat.cast_nonneg Y.card)).trans (hRect X hx Y hy
        (by simpa only [mul_comm] using hX) (by simpa only [mul_comm] using hY))
  · intro j v hv
    have hIn := ((hNew j).physical_lower_bounds (B \ L) (S j) (T j) ρ η).2.1 v hv
    exact (mul_le_mul_of_nonneg_right hLow (Nat.cast_nonneg _)).trans hIn
  · intro j v hv
    have hOut := ((hNew j).physical_lower_bounds (B \ L) (S j) (T j) ρ η).1 v hv
    rw [←hBal j] at hOut
    exact (mul_le_mul_of_nonneg_right hLow (Nat.cast_nonneg _)).trans hOut

/-- Complete all the prepared basic path systems with the same
base-cycle reserve. The budgets are uniform over earlier choices
of Hamilton cycles. -/
theorem exists_iterated_chord_path_completions
    (d η ν τ γ : ℝ) (hν : 0 < ν) (hWidth : η+ν ≤ τ) (hη : 0 < η)
    (hη1 : η ≤ 1) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 0 < d)
    (hCost : ν ≤ d*τ) (hDegrees : γ ≤ d) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {n q : ℕ}
      (B : Digraph V) (Q : Fin q → Digraph V) (c : V → Fin (n+1))
      (ε ρ δ : ℝ) (r : Fin q → Fin (n+1) → ℕ),
      let s := finRotate (n+1)
      let A (j : Fin (n+1)) := (univ : Finset V).filter (fun v => c v = j)
      let S (i : Fin q) (j : Fin (n+1)) := freeOut (Q i) c j
      let T (i : Fin q) (j : Fin (n+1)) := freeIn (Q i) c (s j)
      0 ≤ ε → 0 ≤ δ → ρ ≤ 1 → d ≤ ρ-2*η → 2*(ε+δ) ≤ η →
      (∀ j, IsSuperregularPair B ε ρ (A j) (A (s j))) →
      (∀ i, IsDirectedPathSystem (Q i)) →
      (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) →
      (∀ i, Disjoint (Q i) B) →
      (∀ i j, (S i j).card = (T i j).card) →
      (∀ i j, ∃ v, v ∈ freeIn (Q i) c j ∧ v ∈ S i j) →
      (∀ i j, N ≤ (S i j).card) →
      (∀ i j, (q:ℝ) ≤ δ*((S i j).card:ℝ)*η) →
      (∀ i j, ε*((A j).card:ℝ)+((A j \ S i j).card:ℝ)+q ≤ η*((S i j).card:ℝ)) →
      (∀ i j, ε*((A (s j)).card:ℝ)+((A (s j) \ T i j).card:ℝ)+q ≤ η*((T i j).card:ℝ)) →
      (∀ i j, 0 < r i j ∧ η*((S i j).card:ℝ) ≤ r i j ∧ (r i j:ℝ) ≤ d*((S i j).card:ℝ)) →
      ∃ F : Fin q → Equiv.Perm V,
        (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
        (∀ i x y, (Q i).Adj x y → F i x = y) ∧
        (∀ i x, (Q i ⊔ B).Adj x (F i x)) ∧
        (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
        (⨆ i, Q i) ≤ matchingUnion F := by
  obtain ⟨N,hN⟩ := exists_chord_path_completion_after_deletion.{u}
    d η ν τ γ hν hWidth hη hη1 hτγ hγ hd hCost hDegrees
  refine ⟨N,?_⟩
  intro V _ n q B Q c ε ρ δ r s A S T hε hδ hρ hDensity hTol hPairs hPath hDis hReserve hBal
    hOverlap hSize hBudget hLeft hRight hr
  apply exists_iterated_path_extensions B Q hDis hReserve
  intro i L hLB hDeg
  exact hN B L (Q i) c q ε ρ δ (r i) hLB
    (fun v => ⟨(hDeg v).1.trans i.isLt.le,(hDeg v).2.trans i.isLt.le⟩)
    hε hδ hρ hDensity hTol hPairs (hPath i) (hBal i) (hOverlap i) (hSize i)
    (hBudget i) (hLeft i) (hRight i) (hr i)

end OverfullWork.DirectedRobustExpansion
