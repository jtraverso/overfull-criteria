module

public import OverfullWork.KLOSRobustComponents

@[expose] public section

/-! Stability of bipartite robust expansion under vertex edits
(Kühn–Lo–Osthus–Staden, Lemma 4.9, and Staden, Lemma 3.4.9). -/
namespace OverfullWork.KLOS

open SimpleGraph Finset PrunedCore RobustExpansion
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem expandsAcross_self_iff (U : Finset V) (ν τ : ℝ) :
    ExpandsAcross G ν τ U U ↔ ExpandsInside G ν τ U := by
  unfold ExpandsAcross ExpandsInside
  simp only [union_self]
  simp_rw [inter_eq_left.mpr (robustNeighbourhoodIn_subset G ν U _)]

/-- A smaller expansion threshold or a narrower test window preserves
bipartite robust expansion. -/
theorem expandsAcross_mono (A B : Finset V) {ν ν' τ τ' : ℝ}
    (hν : ν' ≤ ν) (hτ : τ ≤ τ') (hExpand : ExpandsAcross G ν τ A B) :
    ExpandsAcross G ν' τ' A B := by
  intro S hS hLow hHigh
  have hA : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hU : (0 : ℝ) ≤ (A ∪ B).card := Nat.cast_nonneg _
  have hSize := mul_le_mul_of_nonneg_right hν hU
  have hN : robustNeighbourhoodIn G ν (A ∪ B) S ⊆ robustNeighbourhoodIn G ν' (A ∪ B) S := by
    intro v hv
    obtain ⟨hvU, hvS⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨hvU, hSize.trans hvS⟩
  have hCard : (((robustNeighbourhoodIn G ν (A ∪ B) S ∩ B).card : ℕ) : ℝ) ≤
      ((robustNeighbourhoodIn G ν' (A ∪ B) S ∩ B).card : ℝ) := by
    exact_mod_cast card_le_card (inter_subset_inter hN (Subset.rfl : B ⊆ B))
  have hOld := hExpand S hS ((mul_le_mul_of_nonneg_right hτ hA).trans hLow)
    (hHigh.trans (mul_le_mul_of_nonneg_right (sub_le_sub_left hτ 1) hA))
  linarith only [hOld, hCard, hSize]

/-- Ordinary robust expansion has the same parameter monotonicity. -/
theorem expandsInside_mono (U : Finset V) {ν ν' τ τ' : ℝ}
    (hν : ν' ≤ ν) (hτ : τ ≤ τ') (hExpand : ExpandsInside G ν τ U) :
    ExpandsInside G ν' τ' U := by
  exact (expandsAcross_self_iff G U ν' τ').mp
    (expandsAcross_mono G U U hν hτ ((expandsAcross_self_iff G U ν τ).mpr hExpand))

/-- One bound on the edits to both sides suffices to preserve the source
window, the robust-neighbour threshold, and the surplus. -/
theorem expandsAcross_of_small_edit (A B A' B' : Finset V)
    (ν τ e : ℝ) (hν : 0 ≤ ν) (hνOne : ν ≤ 1) (hτ : 0 ≤ τ) (hτHalf : τ ≤ 1 / 2)
    (hExpand : ExpandsAcross G ν τ A B)
    (hEdit : ((A \ A').card : ℝ) + ((A' \ A).card : ℝ) +
      ((B \ B').card : ℝ) + ((B' \ B).card : ℝ) ≤ e)
    (hWindow : 2 * e ≤ τ * (A.card : ℝ))
    (hSurplus : 4 * e ≤ ν * ((A ∪ B).card : ℝ)) :
    ExpandsAcross G (ν / 2) (2 * τ) A' B' := by
  intro S hS hLower hUpper
  let U := A ∪ B
  let U' := A' ∪ B'
  let T := S ∩ A
  change 4 * e ≤ ν * (U.card : ℝ) at hSurplus
  have hT : T ⊆ A := inter_subset_right
  have he : 0 ≤ e := by
    have h₁ := Nat.cast_nonneg (α := ℝ) (A \ A').card
    have h₂ := Nat.cast_nonneg (α := ℝ) (A' \ A).card
    have h₃ := Nat.cast_nonneg (α := ℝ) (B \ B').card
    have h₄ := Nat.cast_nonneg (α := ℝ) (B' \ B).card
    linarith only [hEdit, h₁, h₂, h₃, h₄]
  have hA : (A.card : ℝ) ≤ (A'.card : ℝ) + ((A \ A').card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := A) (t := A')).trans_eq (Nat.add_comm _ _)
  have hA' : (A'.card : ℝ) ≤ (A.card : ℝ) + ((A' \ A).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := A') (t := A)).trans_eq (Nat.add_comm _ _)
  have hSdiff := card_le_card (sdiff_subset_sdiff_left A hS)
  have hTcard : (S.card : ℝ) ≤ (T.card : ℝ) + ((A' \ A).card : ℝ) := by
    have h := card_sdiff_add_card_inter S A
    exact_mod_cast (show S.card ≤ T.card + (A' \ A).card by dsimp [T]; omega)
  have hTUpper : (T.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast card_le_card (inter_subset_left : T ⊆ S)
  have hLostA : ((A \ A').card : ℝ) + ((A' \ A).card : ℝ) ≤ e := by
    have h₁ := Nat.cast_nonneg (α := ℝ) (B \ B').card
    have h₂ := Nat.cast_nonneg (α := ℝ) (B' \ B).card
    linarith only [hEdit, h₁, h₂]
  have hAddA : ((A' \ A).card : ℝ) ≤ e := by
    have h := Nat.cast_nonneg (α := ℝ) (A \ A').card
    linarith only [hLostA, h]
  have hTL : τ * (A.card : ℝ) ≤ (T.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2 * τ by positivity)
    have h' := mul_le_mul_of_nonneg_right (show 2 * τ ≤ 1 by linarith only [hτHalf])
      (Nat.cast_nonneg (α := ℝ) (A \ A').card)
    linarith only [h, h', hLower, hTcard, hLostA, hWindow]
  have hTU : (T.card : ℝ) ≤ (1 - τ) * (A.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hA' (show 0 ≤ 1 - 2 * τ by linarith only [hτHalf])
    have h' := mul_le_mul_of_nonneg_right (show 1 - 2 * τ ≤ 1 by linarith only [hτ])
      (Nat.cast_nonneg (α := ℝ) (A' \ A).card)
    linarith only [h, h', hUpper, hTUpper, hAddA, hWindow, he]
  have hUnion : (U'.card : ℝ) ≤ (U.card : ℝ) + e := by
    have hsub : U' \ U ⊆ (A' \ A) ∪ (B' \ B) := by
      intro v hv
      simp only [U, U', mem_union, mem_sdiff] at hv ⊢
      tauto
    have hNat := (card_le_card hsub).trans (card_union_le (A' \ A) (B' \ B))
    have hReal : ((U' \ U).card : ℝ) ≤ ((A' \ A).card : ℝ) + ((B' \ B).card : ℝ) := by
      exact_mod_cast hNat
    have hBase : (U'.card : ℝ) ≤ ((U' \ U).card : ℝ) + (U.card : ℝ) := by
      exact_mod_cast (card_le_card_sdiff_add_card (s := U') (t := U))
    have h₁ := Nat.cast_nonneg (α := ℝ) (A \ A').card
    have h₂ := Nat.cast_nonneg (α := ℝ) (B \ B').card
    linarith only [hReal, hBase, hEdit, h₁, h₂]
  have hHalfThreshold : (ν / 2) * (U'.card : ℝ) ≤ ν * (U.card : ℝ) - e := by
    have h := mul_le_mul_of_nonneg_left hUnion (show 0 ≤ ν / 2 by positivity)
    rw [mul_add] at h
    have h' := mul_le_mul_of_nonneg_right hνOne he
    have hCost : (ν / 2) * e ≤ e / 2 := by linarith only [h']
    have hHalf : (ν / 2) * (U.card : ℝ) + (ν / 2) * (U.card : ℝ) =
        ν * (U.card : ℝ) := by ring
    linarith only [h, hCost, hHalf, hSurplus, he]
  have hThreshold : (ν / 2) * (U'.card : ℝ) ≤ ν * (U.card : ℝ) := by
    linarith only [hHalfThreshold, he]
  let N := robustNeighbourhoodIn G ν U T ∩ B
  let N' := robustNeighbourhoodIn G (ν / 2) U' S ∩ B'
  have hKeep : N ∩ B' ⊆ N' := by
    intro v hv
    obtain ⟨hvN, hvB'⟩ := mem_inter.mp hv
    have hOld := (mem_filter.mp (mem_inter.mp hvN).1).2
    have hDeg : (neighboursIn G T v : ℝ) ≤ (neighboursIn G S v : ℝ) := by
      exact_mod_cast neighboursIn_mono G (inter_subset_left : T ⊆ S) v
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_union.mpr (Or.inr hvB'),
      hThreshold.trans (hOld.trans hDeg)⟩, hvB'⟩
  have hDrop : (N.card : ℝ) ≤ (N'.card : ℝ) + ((B \ B').card : ℝ) := by
    have hsub : N \ B' ⊆ B \ B' := sdiff_subset_sdiff_left B' inter_subset_right
    have hNat := card_sdiff_add_card_inter N B'
    have h₁ := card_le_card hsub
    have h₂ := card_le_card hKeep
    exact_mod_cast (show N.card ≤ N'.card + (B \ B').card by omega)
  have hOld := hExpand T hT hTL hTU
  have hSpending : ((A' \ A).card : ℝ) + ((B \ B').card : ℝ) ≤ e := by
    have h₁ := Nat.cast_nonneg (α := ℝ) (A \ A').card
    have h₂ := Nat.cast_nonneg (α := ℝ) (B' \ B).card
    linarith only [hEdit, h₁, h₂]
  change (S.card : ℝ) + (ν / 2) * (U'.card : ℝ) ≤ (N'.card : ℝ)
  linarith only [hOld, hDrop, hTcard, hHalfThreshold, hSpending]

/-- Ordinary robust expansion also survives small changes of its ambient
vertex set. This is a version of Lemma 4.8 with explicit edit budgets. -/
theorem expandsInside_of_small_edit (U U' : Finset V)
    (ν τ e : ℝ) (hν : 0 ≤ ν) (hνOne : ν ≤ 1) (hτ : 0 ≤ τ) (hτHalf : τ ≤ 1 / 2)
    (hExpand : ExpandsInside G ν τ U)
    (hEdit : ((U \ U').card : ℝ) + ((U' \ U).card : ℝ) ≤ e)
    (hWindow : 4 * e ≤ τ * (U.card : ℝ)) (hSurplus : 8 * e ≤ ν * (U.card : ℝ)) :
    ExpandsInside G (ν / 2) (2 * τ) U' := by
  apply (expandsAcross_self_iff G U' (ν / 2) (2 * τ)).mp
  apply expandsAcross_of_small_edit G U U U' U' ν τ (2 * e) hν hνOne hτ hτHalf
    ((expandsAcross_self_iff G U ν τ).mpr hExpand)
  · linarith only [hEdit]
  · linarith only [hWindow]
  · rw [union_self]
    linarith only [hSurplus]

/-- Lemma 4.10(i) with explicit inequalities for the scales. -/
theorem bipartite_component_of_small_edit (ρ ν τ γ : ℝ) (A B A' B' : Finset V)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V)
    (hν : 0 ≤ ν) (hνOne : ν ≤ 1) (hτ : 0 ≤ τ) (hτHalf : τ ≤ 1 / 2)
    (hOld : CloseToBipartite G ρ A B) (hExpand : ExpandsAcross G ν τ A B)
    (hNew : Disjoint A' B') (hScale : ρ ≤ γ)
    (hEdit : ((A \ A').card : ℝ) + ((A' \ A).card : ℝ) +
      ((B \ B').card : ℝ) + ((B' \ B).card : ℝ) ≤ γ * (Fintype.card V : ℝ))
    (hSize : (Real.sqrt (3 * γ) + 2 * Real.sqrt ρ + γ) * (Fintype.card V : ℝ) ≤ G.minDegree)
    (hWindow : 2 * (γ * (Fintype.card V : ℝ)) ≤ τ * (A.card : ℝ))
    (hSurplus : 4 * (γ * (Fintype.card V : ℝ)) ≤ ν * ((A ∪ B).card : ℝ)) :
    CloseToBipartite G (3 * γ) A' B' ∧ ExpandsAcross G (ν / 2) (2 * τ) A' B' :=
  ⟨closeToBipartite_of_small_edit G ρ γ (3 * γ) A B A' B' hρ hn hOld hNew hEdit
      (by linarith only [hScale]) hSize,
    expandsAcross_of_small_edit G A B A' B' ν τ _ hν hνOne hτ hτHalf hExpand
      hEdit hWindow hSurplus⟩

/-- Lemma 4.10(ii). Keep retained vertices on their original side and
assign all newly added vertices to the first side. Each changed vertex
is charged exactly once in the edit budget. -/
theorem exists_bipartite_component_of_small_edit (ρ ν τ γ : ℝ) (A B W : Finset V)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V)
    (hν : 0 ≤ ν) (hνOne : ν ≤ 1) (hτ : 0 ≤ τ) (hτHalf : τ ≤ 1 / 2)
    (hOld : CloseToBipartite G ρ A B) (hExpand : ExpandsAcross G ν τ A B)
    (hScale : ρ ≤ γ)
    (hEdit : ((((A ∪ B) \ W) ∪ (W \ (A ∪ B))).card : ℝ) ≤ γ * (Fintype.card V : ℝ))
    (hSize : (Real.sqrt (3 * γ) + 2 * Real.sqrt ρ + γ) * (Fintype.card V : ℝ) ≤ G.minDegree)
    (hWindow : 2 * (γ * (Fintype.card V : ℝ)) ≤ τ * (A.card : ℝ))
    (hSurplus : 4 * (γ * (Fintype.card V : ℝ)) ≤ ν * ((A ∪ B).card : ℝ)) :
    ∃ A' B' : Finset V, A' ∪ B' = W ∧
      CloseToBipartite G (3 * γ) A' B' ∧ ExpandsAcross G (ν / 2) (2 * τ) A' B' := by
  let A' := W \ B
  let B' := W ∩ B
  have hUnion : A' ∪ B' = W := sdiff_union_inter W B
  have hDis : Disjoint A' B' := Finset.disjoint_left.mpr (fun _ ha hb =>
    (mem_sdiff.mp ha).2 (mem_inter.mp hb).2)
  have h₁ : A \ A' = A \ W := by
    ext v
    simp only [A', mem_sdiff]
    have h : v ∈ A → v ∉ B := fun ha hb => Finset.disjoint_left.mp hOld.1 ha hb
    tauto
  have h₂ : A' \ A = W \ (A ∪ B) := by
    ext v
    simp only [A', mem_sdiff, mem_union]
    tauto
  have h₃ : B \ B' = B \ W := by
    ext v
    simp only [B', mem_sdiff, mem_inter]
    tauto
  have h₄ : B' \ B = ∅ := by simp [B']
  have hLossUnion : (A ∪ B) \ W = (A \ W) ∪ (B \ W) := by
    ext v
    simp only [mem_union, mem_sdiff]
    tauto
  have hLossDis : Disjoint (A \ W) (B \ W) :=
    Disjoint.mono (sdiff_subset) (sdiff_subset) hOld.1
  have hEditDis : Disjoint ((A ∪ B) \ W) (W \ (A ∪ B)) :=
    Finset.disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1)
  have hPay : ((A \ A').card : ℝ) + ((A' \ A).card : ℝ) +
      ((B \ B').card : ℝ) + ((B' \ B).card : ℝ) ≤ γ * (Fintype.card V : ℝ) := by
    rw [card_union_of_disjoint hEditDis, hLossUnion, card_union_of_disjoint hLossDis] at hEdit
    rw [h₁, h₂, h₃, h₄, card_empty]
    push_cast at hEdit ⊢
    linarith only [hEdit]
  exact ⟨A', B', hUnion, bipartite_component_of_small_edit G ρ ν τ γ A B A' B'
    hρ hn hν hνOne hτ hτHalf hOld hExpand hDis hScale hPay hSize hWindow hSurplus⟩

end OverfullWork.KLOS
