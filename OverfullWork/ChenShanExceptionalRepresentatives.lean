module

public import OverfullWork.AvailableNeighbours
public import OverfullWork.ChenShanBalancedCoreDeletion
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem repeated_incidence_le_of_subset
    (M : MultiGraph V) (x : V) {S U : Finset V} (hSU : S ⊆ U) :
    M.degreeInto S x - (M.neighboursInto S x).card ≤
      M.degreeInto U x - (M.neighboursInto U x).card := by
  have hEq (T : Finset V) : M.degreeInto T x - (M.neighboursInto T x).card =
      ∑ y ∈ T, (M.mult s(x,y) - if 0 < M.mult s(x,y) then 1 else 0) := by
    have h : M.degreeInto T x = (M.neighboursInto T x).card +
        ∑ y ∈ T, (M.mult s(x,y) - if 0 < M.mult s(x,y) then 1 else 0) := by
      rw [MultiGraph.degreeInto,MultiGraph.neighboursInto,card_eq_sum_ones,sum_filter,← sum_add_distrib]
      apply sum_congr rfl
      intro y _
      split_ifs <;> omega
    omega
  rw [hEq S,hEq U]
  exact sum_le_sum_of_subset_of_nonneg hSU (fun _ _ _ => Nat.zero_le _)

/-- The preferred side and the representative edges of §5.1.1.
Each representative is an indexed copy, with distinct core endpoints. -/
theorem exists_preferred_side_representatives
    (M : MultiGraph V) (A B : Finset V) (hAB : Disjoint A B) (x : V)
    (k a : ℕ) (β : ℝ) (hβ : 0 < β) (hβ₁ : β ≤ 1)
    (hDegree : M.degree x ≤ k) :
    let c := M.degreeInto (A ∪ B) x
    β*(k:ℝ) ≤ (c:ℝ) → (a:ℝ) ≤ β*k/10 →
    (c - (M.neighboursInto (A ∪ B) x).card ≤ a ∨
      β*(k:ℝ) ≤ min ((M.neighboursInto A x).card : ℝ) ((M.neighboursInto B x).card : ℝ)) →
    ∃ S : Finset V, (S = A ∨ S = B) ∧ c ≤ 2*M.degreeInto S x ∧
      β*(c:ℝ)/4 ≤ ((M.neighboursInto S x).card : ℝ) ∧
      ∃ f : ↥(M.neighboursInto S x) ↪ (Σ y : V, Fin (M.mult s(x,y))),
        ∀ y, (f y).1 = y.val := by
  intro c hDensity hSlack hOrd
  have hErr : (a:ℝ) ≤ (c:ℝ)/10 := by linarith only [hDensity,hSlack]
  have hSum : M.degreeInto A x + M.degreeInto B x = c := by
    unfold MultiGraph.degreeInto
    rw [← sum_union hAB]
    rfl
  obtain ⟨S,hSide,hLarge⟩ : ∃ S : Finset V, (S = A ∨ S = B) ∧ c ≤ 2*M.degreeInto S x := by
    by_cases h : M.degreeInto B x ≤ M.degreeInto A x
    · exact ⟨A,Or.inl rfl,by omega⟩
    · exact ⟨B,Or.inr rfl,by omega⟩
  have hSub : S ⊆ A ∪ B := by
    rcases hSide with rfl | rfl
    · exact subset_union_left
    · exact subset_union_right
  have hCK : c ≤ k := by
    have h := M.degreeInto_add_compl (A ∪ B) x
    change c + _ = _ at h
    omega
  have hRep : β*(c:ℝ)/4 ≤ ((M.neighboursInto S x).card : ℝ) := by
    rcases hOrd with hRepeat | hBoth
    · have hNat := (repeated_incidence_le_of_subset M x hSub).trans hRepeat
      have hDeg : (M.degreeInto S x : ℝ) ≤ ((M.neighboursInto S x).card : ℝ) + a := by
        exact_mod_cast (show M.degreeInto S x ≤ (M.neighboursInto S x).card + a by omega)
      have hHalf : (c:ℝ) ≤ 2*(M.degreeInto S x : ℝ) := by exact_mod_cast hLarge
      have hβc := mul_le_mul_of_nonneg_right hβ₁ (Nat.cast_nonneg (α := ℝ) c)
      linarith only [hDeg,hHalf,hErr,hβc,Nat.cast_nonneg (α := ℝ) c]
    · have hSideN : β*(k:ℝ) ≤ ((M.neighboursInto S x).card : ℝ) := by
        rcases hSide with rfl | rfl
        · exact hBoth.trans (min_le_left _ _)
        · exact hBoth.trans (min_le_right _ _)
      have hBound := mul_le_mul_of_nonneg_left
        (show (c:ℝ) ≤ k by exact_mod_cast hCK) hβ.le
      linarith only [hSideN,hBound,mul_nonneg hβ.le (Nat.cast_nonneg (α := ℝ) c)]
  refine ⟨S,hSide,hLarge,hRep,⟨fun y => ⟨y.val,⟨0,?_⟩⟩,?_⟩,fun _ => rfl⟩
  · exact (mem_filter.mp y.property).2
  · intro y z h
    exact Subtype.ext (congrArg Sigma.fst h)


omit [Fintype V] in
private theorem degreeInto_after_deletion
    (M : MultiGraph V) (x : V) (U Y : Finset V) (a : ℕ)
    (hMultiplicity : ∀ y ∈ U ∩ Y, M.mult s(x,y) ≤ a) :
    M.degreeInto U x ≤ M.degreeInto (U \ Y) x + a*Y.card := by
  have hSep : Disjoint (U \ Y) (U ∩ Y) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact (mem_sdiff.mp hv).2 (mem_inter.mp hv').2
  have hPartition : (U \ Y) ∪ (U ∩ Y) = U := by
    ext v
    simp only [mem_union,mem_sdiff,mem_inter]
    tauto
  have hCount : (∑ y ∈ U ∩ Y, M.mult s(x,y)) ≤ a*Y.card := by
    calc
      _ ≤ ∑ _y ∈ U ∩ Y, a := sum_le_sum hMultiplicity
      _ ≤ _ := by
        have hCard : (U ∩ Y).card ≤ Y.card := card_le_card inter_subset_right
        rw [Finset.sum_const_nat (m := a) (fun _ _ => rfl),Nat.mul_comm a]
        exact Nat.mul_le_mul_right a hCard
  unfold MultiGraph.degreeInto
  nth_rw 1 [← hPartition]
  rw [sum_union hSep]
  exact Nat.add_le_add_left hCount _

omit [Fintype V] in
private theorem neighboursInto_after_deletion
    (M : MultiGraph V) (x : V) (S Y : Finset V) :
    (M.neighboursInto S x).card ≤ (M.neighboursInto (S \ Y) x).card + Y.card := by
  apply (card_le_card ?_).trans (card_union_le (M.neighboursInto (S \ Y) x) Y)
  intro v hv
  obtain ⟨hvS,hvAdj⟩ := mem_filter.mp hv
  by_cases hvY : v ∈ Y
  · exact mem_union_right _ hvY
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hvS,hvY⟩,hvAdj⟩)

omit [Fintype V] in
/-- An old exceptional vertex keeps the neighborhood alternatives in
(5.1) after the balanced trimming. The multiplicity bound controls
lost incidences, while the size of the deleted set controls lost
distinct neighbors. -/
theorem exceptional_neighborhood_after_core_deletion
    (M : MultiGraph V) (A B Y : Finset V) (x : V)
    (k a : ℕ) (β : ℝ)
    (hMultiplicity : ∀ y ∈ (A ∪ B) ∩ Y, M.mult s(x,y) ≤ a)
    (hLostIncidence : (a:ℝ)*Y.card ≤ β*k/2)
    (hLostNeighbors : (Y.card:ℝ) ≤ β*k/2)
    (hDensity : β*(k:ℝ) ≤ M.degreeInto (A ∪ B) x)
    (hOld : M.degreeInto (A ∪ B) x - (M.neighboursInto (A ∪ B) x).card ≤ a ∨
      β*(k:ℝ) ≤ min ((M.neighboursInto A x).card : ℝ) ((M.neighboursInto B x).card : ℝ)) :
    (β/2)*(k:ℝ) ≤ M.degreeInto ((A \ Y) ∪ (B \ Y)) x ∧
    (M.degreeInto ((A \ Y) ∪ (B \ Y)) x -
        (M.neighboursInto ((A \ Y) ∪ (B \ Y)) x).card ≤ a ∨
      (β/2)*(k:ℝ) ≤
        min ((M.neighboursInto (A \ Y) x).card : ℝ) ((M.neighboursInto (B \ Y) x).card : ℝ)) := by
  have hUnion : (A \ Y) ∪ (B \ Y) = (A ∪ B) \ Y := by
    ext v
    simp only [mem_union,mem_sdiff]
    tauto
  rw [hUnion]
  constructor
  · have hd := degreeInto_after_deletion M x (A ∪ B) Y a hMultiplicity
    have hR : (M.degreeInto (A ∪ B) x:ℝ) ≤
        (M.degreeInto ((A ∪ B) \ Y) x:ℝ) + (a:ℝ)*Y.card := by exact_mod_cast hd
    linarith only [hDensity,hR,hLostIncidence]
  · rcases hOld with hRep | hBoth
    · exact Or.inl ((repeated_incidence_le_of_subset M x sdiff_subset).trans hRep)
    · right
      apply le_min
      · have hOldA := hBoth.trans (min_le_left _ _)
        have hR : ((M.neighboursInto A x).card:ℝ) ≤
            ((M.neighboursInto (A \ Y) x).card:ℝ) + Y.card := by
          exact_mod_cast neighboursInto_after_deletion M x A Y
        linarith only [hOldA,hLostNeighbors,hR]
      · have hOldB := hBoth.trans (min_le_right _ _)
        have hR : ((M.neighboursInto B x).card:ℝ) ≤
            ((M.neighboursInto (B \ Y) x).card:ℝ) + Y.card := by
          exact_mod_cast neighboursInto_after_deletion M x B Y
        linarith only [hOldB,hLostNeighbors,hR]


/-- A vertex moved out of a simple core has many distinct neighbors
in the retained core. Every repeated incidence can be charged to the
original exterior multigraph. -/
theorem moved_vertex_has_low_repetition
    (M : MultiGraph V) (H : SimpleGraph V) [DecidableRel H.Adj] (U Y : Finset V)
    (x : V) (k a : ℕ) (β : ℝ)
    (hH : k-a ≤ PrunedCore.neighboursIn H U x) (hM : M.degree x ≤ a)
    (hBudget : β*(k:ℝ)/2 ≤ (k:ℝ) - a - Y.card) :
    let R := M.addCopies (MultiGraph.ofSimpleGraph H)
    β*(k:ℝ)/2 ≤ (R.degreeInto (U \ Y) x : ℝ) ∧
      R.degreeInto (U \ Y) x - (R.neighboursInto (U \ Y) x).card ≤ a := by
  intro R
  let S := U \ Y
  have hDistinct : PrunedCore.neighboursIn H S x ≤ (R.neighboursInto S x).card := by
    rw [RobustExpansion.neighboursIn_eq_filter_card]
    apply card_le_card
    intro y hy
    obtain ⟨hyS,hyAdj⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨hyS,?_⟩
    have hOne : (MultiGraph.ofSimpleGraph H).mult s(x,y) = 1 := by
      simp [MultiGraph.ofSimpleGraph,SimpleGraph.mem_edgeSet,hyAdj]
    change 0 < M.mult s(x,y) + (MultiGraph.ofSimpleGraph H).mult s(x,y)
    omega
  have hSimple : (MultiGraph.ofSimpleGraph H).degreeInto S x = PrunedCore.neighboursIn H S x := by
    simp only [MultiGraph.degreeInto,MultiGraph.ofSimpleGraph,SimpleGraph.mem_edgeSet,
      RobustExpansion.neighboursIn_eq_filter_card,card_eq_sum_ones,sum_filter]
  have hAdd : R.degreeInto S x = M.degreeInto S x + PrunedCore.neighboursIn H S x := by
    rw [← hSimple]
    simp only [R,MultiGraph.degreeInto,MultiGraph.addCopies,sum_add_distrib]
  have hExterior : M.degreeInto S x ≤ a := by
    have hh := M.degreeInto_add_compl S x
    omega
  have hLoss : PrunedCore.neighboursIn H U x ≤ PrunedCore.neighboursIn H S x + Y.card :=
    neighboursIn_after_vertex_deletion H U Y x
  have hDegN : k ≤ R.degreeInto S x + a + Y.card := by omega
  have hDeg : (k:ℝ) ≤ (R.degreeInto S x:ℝ) + a + Y.card := by exact_mod_cast hDegN
  constructor
  · linarith only [hDeg,hBudget]
  · change R.degreeInto S x - (R.neighboursInto S x).card ≤ a
    omega

end OverfullWork.ChenShan
