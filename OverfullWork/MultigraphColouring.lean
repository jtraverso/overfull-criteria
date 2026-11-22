module

public import OverfullWork.MultigraphExtension

@[expose] public section


/-! Restriction of a multigraph colouring to the contained original simple graph. -/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem EdgeColoring.eq_of_incident_positive {M : MultiGraph V} {k : ℕ}
    (C : M.EdgeColoring k) {v : V} {e f : Sym2 V} {i : Fin k}
    (hve : v ∈ e) (hvf : v ∈ f) (he : 0 < C.col e i) (hf : 0 < C.col f i) : e = f := by
  by_contra hne
  have hsub : {e,f} ⊆ univ.filter (fun a : Sym2 V => v ∈ a) := by
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact mem_filter.mpr ⟨mem_univ _, hve⟩
    · exact mem_filter.mpr ⟨mem_univ _, hvf⟩
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => Nat.zero_le _) (f := fun a => C.col a i)
  have hp := C.proper v i
  simp only [sum_pair hne] at hs
  omega

/-- A colouring of all copies restricts to any contained simple graph. -/
theorem edgeColourable_of_contained (M : MultiGraph V) (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ}
    (hcontains : ∀ e ∈ G.edgeSet, 1 ≤ M.mult e) (C : M.EdgeColoring k) :
    G.lineGraph.Colorable k := by
  classical
  have hpositive (e : G.edgeSet) : ∃ i : Fin k, 0 < C.col e.1 i := by
    by_contra h
    have hz : ∀ i : Fin k, C.col e.1 i = 0 := by
      intro i
      have hi : ¬ 0 < C.col e.1 i := fun hi => h ⟨i, hi⟩
      omega
    have hs := C.sum_col e.1
    simp_rw [hz] at hs
    have hm := hcontains e.1 e.2
    simp only [sum_const_zero] at hs
    omega
  choose colour hcolour using hpositive
  refine ⟨SimpleGraph.Coloring.mk colour ?_⟩
  intro e f hadj heq
  rw [lineGraph_adj_iff_exists] at hadj
  obtain ⟨hne, v, hve, hvf⟩ := hadj
  apply hne
  apply Subtype.ext
  apply C.eq_of_incident_positive hve hvf (hcolour e)
  rw [heq]
  exact hcolour f

end SimpleGraph.MultiGraph

namespace OverfullWork.MultigraphExtension

open SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- This is a reduction, not an existence theorem for the colouring of
the extension. Regularity and multiplicity two alone are not invoked as
a sufficient factorization criterion. -/
theorem edgeColourable_of_extension_colouring (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (C : (pointExtension G).EdgeColoring k) : G.EdgeColorable k := by
  classical
  have hcontains : ∀ e ∈ (OddOrder.pointExtend G ∅).edgeSet,
      1 ≤ (pointExtension G).mult e := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      cases u with
      | none =>
        cases v <;> simp [OddOrder.pointExtend] at he
      | some u =>
        cases v with
        | none => simp [OddOrder.pointExtend] at he
        | some v => exact contains_original G u v he
  have hc := MultiGraph.edgeColourable_of_contained (pointExtension G)
    (OddOrder.pointExtend G ∅) hcontains C
  exact Critical.colourable_of_copy (OddOrder.intoExtension G ∅) hc

#print axioms edgeColourable_of_extension_colouring

end OverfullWork.MultigraphExtension
