module

public import OverfullWork.AvailableNeighbours
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem repeated_incidence_le_of_subset
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

end OverfullWork.ChenShan
