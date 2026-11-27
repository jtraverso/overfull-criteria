module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import OverfullWork.EquitableRecolouring
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset

/-- The finite choice of one or two components in Lemma 3.9. Each
component contributes the signed counts of its endpoints on the two
core sides. A positive total on both sides gives a balanced transfer. -/
theorem exists_balanced_component_transfer {I : Type*} (S : Finset I)
    (x y : I → ℤ)
    (hLocal : ∀ i ∈ S,
      (x i = 0 ∧ y i = 0) ∨ (x i = 2 ∧ y i = 0) ∨ (x i = -2 ∧ y i = 0) ∨
      (x i = 0 ∧ y i = 2) ∨ (x i = 0 ∧ y i = -2) ∨
      (x i = 1 ∧ y i = 1) ∨ (x i = -1 ∧ y i = -1) ∨
      (x i = 1 ∧ y i = -1) ∨ (x i = -1 ∧ y i = 1))
    (hx : 0 < ∑ i ∈ S, x i) (hy : 0 < ∑ i ∈ S, y i) :
    (∃ i ∈ S, x i = 1 ∧ y i = 1) ∨
      ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
        x i + x j = y i + y j ∧ 1 ≤ x i + x j ∧ x i + x j ≤ 2 := by
  classical
  by_cases h11 : ∃ i ∈ S, x i = 1 ∧ y i = 1
  · exact Or.inl h11
  right
  have hForbidden i (hi : i ∈ S) : ¬ (x i = 1 ∧ y i = 1) :=
    fun h => h11 ⟨i,hi,h⟩
  by_cases h20 : ∃ i ∈ S, x i = 2 ∧ y i = 0
  · obtain ⟨i,hi,hxi,hyi⟩ := h20
    obtain ⟨j,hj,hyj⟩ : ∃ j ∈ S, 0 < y j := by
      by_contra! h
      exact hy.not_ge (sum_nonpos h)
    have hne : i ≠ j := by
      rintro rfl
      omega
    refine ⟨i,hi,j,hj,hne,?_⟩
    rcases hLocal j hj with h|h|h|h|h|h|h|h|h <;>
      rcases h with ⟨hxj,hyj'⟩ <;> first
      | exact (hForbidden j hj ⟨hxj,hyj'⟩).elim
      | omega
  · by_cases h02 : ∃ j ∈ S, x j = 0 ∧ y j = 2
    · obtain ⟨j,hj,hxj,hyj⟩ := h02
      obtain ⟨i,hi,hxi⟩ : ∃ i ∈ S, 0 < x i := by
        by_contra! h
        exact hx.not_ge (sum_nonpos h)
      have hne : i ≠ j := by
        rintro rfl
        omega
      refine ⟨i,hi,j,hj,hne,?_⟩
      rcases hLocal i hi with h|h|h|h|h|h|h|h|h <;>
        rcases h with ⟨hxi',hyi⟩ <;> first
        | exact (hForbidden i hi ⟨hxi',hyi⟩).elim
        | omega
    · have hNonpos : ∑ i ∈ S, (x i + y i) ≤ 0 := by
        apply sum_nonpos
        intro i hi
        rcases hLocal i hi with h|h|h|h|h|h|h|h|h <;> first
          | exact (h20 ⟨i,hi,h⟩).elim
          | exact (h02 ⟨i,hi,h⟩).elim
          | exact (hForbidden i hi h).elim
          | obtain ⟨hxi,hyi⟩ := h; omega
      rw [sum_add_distrib] at hNonpos
      omega


open SimpleGraph
open scoped Classical

/-- In a component of two colors, at most two vertices have different
incidences in the two colors. The signed sum is even because each color
contributes two incidences per internal edge copy. -/
theorem component_incidence_disagreement
    {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
    (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    let S := C.componentSet a b z
    let diff (v : V) := ((C.colourGraph a).degree v : ℤ) - (C.colourGraph b).degree v
    (∑ v ∈ S, |diff v|) ≤ 2 ∧ Even (∑ v ∈ S, diff v) := by
  intro S diff
  have hCut (i : Fin k) (hi : i = a ∨ i = b) : (C.colourGraph i).cutSize S = 0 := by
    apply sum_eq_zero
    intro u hu
    apply sum_eq_zero
    intro v hv
    change C.col s(u,v) i = 0
    by_contra hn
    have hPos : 0 < C.col s(u,v) a + C.col s(u,v) b := by
      rcases hi with rfl | rfl <;> omega
    exact (mem_compl.mp hv) ((C.component_closed a b z u v hPos).mp hu)
  have hMass (i : Fin k) (hi : i = a ∨ i = b) :
      ∑ v ∈ S, ((C.colourGraph i).degree v : ℤ) =
        2 * ((C.colourGraph i).edgesWithin S : ℤ) := by
    exact_mod_cast (show ∑ v ∈ S, (C.colourGraph i).degree v =
        2 * (C.colourGraph i).edgesWithin S by
      rw [(C.colourGraph i).sum_degree_eq_internal_add_cut,
        MultiGraph.twiceInternal_eq, hCut i hi, add_zero])
  have ha := hMass a (Or.inl rfl)
  have hb := hMass b (Or.inr rfl)
  have hSize : (S.card : ℤ) ≤ (C.colourGraph a).edgesWithin S +
      (C.colourGraph b).edgesWithin S + 1 := by
    exact_mod_cast C.component_size_bound a b z
  constructor
  · calc
      ∑ v ∈ S, |diff v| ≤ ∑ v ∈ S,
          (2 - ((C.colourGraph a).degree v : ℤ) - (C.colourGraph b).degree v) := by
        apply sum_le_sum
        intro v _
        have hda : ((C.colourGraph a).degree v : ℤ) ≤ 1 := by
          exact_mod_cast C.colourGraph_degree_le_one a v
        have hdb : ((C.colourGraph b).degree v : ℤ) ≤ 1 := by
          exact_mod_cast C.colourGraph_degree_le_one b v
        exact abs_le.mpr ⟨by dsimp [diff]; omega,by dsimp [diff]; omega⟩
      _ ≤ 2 := by
        simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,ha,hb]
        omega
  · dsimp [diff]
    rw [sum_sub_distrib,ha,hb]
    exact ⟨((C.colourGraph a).edgesWithin S : ℤ) - (C.colourGraph b).edgesWithin S,by omega⟩


/-- The possible contributions of one component to the side counts in
Lemma 3.9. Vertices outside the sides already have both colors. -/
theorem component_side_contributions
    {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
    (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) (A B : Finset V)
    (hAB : Disjoint A B)
    (hSat : ∀ v, v ∉ A → v ∉ B → (C.colourGraph a).degree v = (C.colourGraph b).degree v) :
    let S := C.componentSet a b z
    let diff (v : V) := ((C.colourGraph a).degree v : ℤ) - (C.colourGraph b).degree v
    let x := ∑ v ∈ A ∩ S, diff v
    let y := ∑ v ∈ B ∩ S, diff v
    (x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = 0) ∨ (x = -2 ∧ y = 0) ∨
    (x = 0 ∧ y = 2) ∨ (x = 0 ∧ y = -2) ∨
    (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) ∨
    (x = 1 ∧ y = -1) ∨ (x = -1 ∧ y = 1) := by
  intro S diff x y
  have hDisj : Disjoint (A ∩ S) (B ∩ S) :=
    hAB.mono inter_subset_left inter_subset_left
  have hSub : (A ∩ S) ∪ (B ∩ S) ⊆ S := union_subset inter_subset_right inter_subset_right
  obtain ⟨hAbs,hEven⟩ := component_incidence_disagreement C a b z
  have hAdd : x+y = ∑ v ∈ S, diff v := by
    dsimp only [x,y]
    rw [← sum_union hDisj]
    apply sum_subset hSub
    intro v hv hn
    have hA : v ∉ A := fun ha => hn (mem_union_left _ (mem_inter.mpr ⟨ha,hv⟩))
    have hB : v ∉ B := fun hb => hn (mem_union_right _ (mem_inter.mpr ⟨hb,hv⟩))
    simp [diff,hSat v hA hB]
  have hSize : |x| + |y| ≤ 2 := by
    calc
      _ ≤ (∑ v ∈ A ∩ S, |diff v|) + ∑ v ∈ B ∩ S, |diff v| :=
        add_le_add (abs_sum_le_sum_abs ..) (abs_sum_le_sum_abs ..)
      _ = ∑ v ∈ (A ∩ S) ∪ (B ∩ S), |diff v| := (sum_union hDisj).symm
      _ ≤ ∑ v ∈ S, |diff v| := sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => abs_nonneg _)
      _ ≤ 2 := hAbs
  rw [← hAdd] at hEven
  obtain ⟨n,hn⟩ := hEven
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx] at hSize
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy] at hSize
      omega
    · rw [abs_of_neg (lt_of_not_ge hy)] at hSize
      omega
  · rw [abs_of_neg (lt_of_not_ge hx)] at hSize
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy] at hSize
      omega
    · rw [abs_of_neg (lt_of_not_ge hy)] at hSize
      omega


variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

/-- Sum a vertex statistic over its bicolored components, restricted to
one side of the core. -/
theorem sum_component_side (C : M.EdgeColoring k) (a b : Fin k) (A : Finset V)
    (f : V → ℤ) :
    (∑ z : (C.twoColourGraph a b).ConnectedComponent,
      ∑ v ∈ A ∩ C.componentSet a b z, f v) = ∑ v ∈ A, f v := by
  have hEq (z) : A ∩ C.componentSet a b z =
      A.filter (fun v => (C.twoColourGraph a b).connectedComponentMk v = z) := by
    ext
    simp [MultiGraph.EdgeColoring.componentSet,ConnectedComponent.mem_supp_iff]
  simp_rw [hEq,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [sum_eq_single ((C.twoColourGraph a b).connectedComponentMk v)]
  · simp
  · intro z _ hne
    simp [hne.symm]
  · simp

/-- If a color has more left-right imbalance than a second color, a
single component contributes a transfer of two to their imbalance. -/
theorem exists_component_imbalance_transfer
    (C : M.EdgeColoring k) (a b : Fin k) (A B : Finset V) (hAB : Disjoint A B)
    (hSat : ∀ v, v ∉ A → v ∉ B → (C.colourGraph a).degree v = (C.colourGraph b).degree v)
    (hDiff : (∑ v ∈ B, (((C.colourGraph a).degree v : ℤ) - (C.colourGraph b).degree v)) <
      (∑ v ∈ A, (((C.colourGraph a).degree v : ℤ) - (C.colourGraph b).degree v))) :
    let diff (v : V) := ((C.colourGraph a).degree v : ℤ) - (C.colourGraph b).degree v
    ∃ z : (C.twoColourGraph a b).ConnectedComponent,
      (∑ v ∈ A ∩ C.componentSet a b z, diff v) -
      (∑ v ∈ B ∩ C.componentSet a b z, diff v) = 2 := by
  intro diff
  by_contra! h
  have hNonpos : (∑ z : (C.twoColourGraph a b).ConnectedComponent,
      ((∑ v ∈ A ∩ C.componentSet a b z, diff v) -
      (∑ v ∈ B ∩ C.componentSet a b z, diff v))) ≤ 0 := by
    apply sum_nonpos
    intro z _
    have hCases := component_side_contributions C a b z A B hAB hSat
    dsimp only at hCases
    have hn := h z
    rcases hCases with h₀|h₀|h₀|h₀|h₀|h₀|h₀|h₀|h₀ <;>
      obtain ⟨hx,hy⟩ := h₀ <;> change
        (∑ v ∈ A ∩ C.componentSet a b z, diff v) = _ at hx <;> change
        (∑ v ∈ B ∩ C.componentSet a b z, diff v) = _ at hy <;> omega
  rw [sum_sub_distrib,sum_component_side,sum_component_side] at hNonpos
  change (∑ v ∈ B, diff v) < (∑ v ∈ A, diff v) at hDiff
  linarith only [hDiff,hNonpos]

/-- Effect of swapping the colors on any closed union of components.
The equality holds vertex by vertex, including parallel edge copies. -/
theorem swap_closed_colour_degree
    (C : M.EdgeColoring k) (a b i : Fin k) (S : Finset V)
    (hclosed : ∀ u v, 0 < C.col s(u,v) a + C.col s(u,v) b → (u ∈ S ↔ v ∈ S))
    (v : V) :
    ((C.swapClosed a b S hclosed).colourGraph i).degree v =
      if v ∈ S then (C.colourGraph (Equiv.swap a b i)).degree v
      else (C.colourGraph i).degree v := by
  simp only [MultiGraph.degree,MultiGraph.EdgeColoring.colourGraph]
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv]
    apply sum_congr rfl
    intro e he
    simpa only [ite_eq_left hv,MultiGraph.EdgeColoring.swapClosed] using C.swappedCol_incident a b S hclosed e v (mem_filter.mp he).2 i
  · rw [ite_eq_right hv]
    apply sum_congr rfl
    intro e he
    simpa only [ite_eq_right hv,MultiGraph.EdgeColoring.swapClosed] using C.swappedCol_incident a b S hclosed e v (mem_filter.mp he).2 i


/-- On a core side, the transferred count is the signed contribution
from the intersection with the vertices whose colors are swapped. -/
theorem swap_closed_side_degree
    (C : M.EdgeColoring k) (a b i : Fin k) (S A : Finset V)
    (hclosed : ∀ u v, 0 < C.col s(u,v) a + C.col s(u,v) b → (u ∈ S ↔ v ∈ S)) :
    (∑ v ∈ A, (((C.swapClosed a b S hclosed).colourGraph i).degree v : ℤ)) =
      (∑ v ∈ A, ((C.colourGraph i).degree v : ℤ)) +
      ∑ v ∈ A ∩ S, (((C.colourGraph (Equiv.swap a b i)).degree v : ℤ) -
        (C.colourGraph i).degree v) := by
  have hAS : A ∩ S = A.filter (· ∈ S) := by ext; simp
  rw [hAS,sum_filter,← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  rw [swap_closed_colour_degree]
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv,ite_eq_left hv]
    omega
  · rw [ite_eq_right hv,ite_eq_right hv,add_zero]

end OverfullWork.ChenShan
