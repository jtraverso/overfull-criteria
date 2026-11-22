module

public import OverfullWork.InternalEdges

@[expose] public section


namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem internal_edge_counts_eq_of_regular (M : MultiGraph V) (L : Finset V) (D : ℕ)
    (hreg : M.IsRegularOfDegree D) (hbal : L.card=Lᶜ.card) :
    M.edgesWithin L = M.edgesWithin Lᶜ := by
  have h₁ := M.regular_cut_identity hreg L
  have h₂ := M.regular_cut_identity hreg Lᶜ
  rw [M.cutSize_compl] at h₂
  rw [twiceInternal_eq] at h₁ h₂
  rw [hbal] at h₁
  omega

def EdgeColoring.colourGraph {M : MultiGraph V} {k : ℕ} (C : M.EdgeColoring k)
    (i : Fin k) : MultiGraph V where
  mult e := C.col e i
  loopless _ he := col_eq_zero_of_isDiag M C he i

theorem EdgeColoring.colourGraph_regular {M : MultiGraph V} {k : ℕ}
    (C : M.EdgeColoring k) (hC : C.IsFactorization) (i : Fin k) :
    (C.colourGraph i).IsRegularOfDegree 1 := fun v => hC v i

/-- Every completed colour must have equally many internal copies on
the two sides of an equipartition. This is a per-colour condition, not
just equality of the total numbers of internal edges. -/
theorem EdgeColoring.internal_balance_of_factorization {M : MultiGraph V} {k : ℕ}
    (C : M.EdgeColoring k) (hC : C.IsFactorization) (L : Finset V)
    (hbal : L.card=Lᶜ.card) (i : Fin k) :
    (C.colourGraph i).edgesWithin L = (C.colourGraph i).edgesWithin Lᶜ :=
  (C.colourGraph i).internal_edge_counts_eq_of_regular L 1 (C.colourGraph_regular hC i) hbal

theorem EdgeColoring.edgesWithin_eq_of_same_internal_colours
    {M N : MultiGraph V} {k : ℕ} (C : M.EdgeColoring k) (B : N.EdgeColoring k)
    (L : Finset V) (i : Fin k)
    (h : ∀ e, e.toFinset ⊆ L → C.col e i=B.col e i) :
    (C.colourGraph i).edgesWithin L = (B.colourGraph i).edgesWithin L := by
  unfold edgesWithin edgeCount
  apply sum_congr rfl
  intro e _
  change (if e.toFinset ⊆ L then C.col e i else 0) =
    (if e.toFinset ⊆ L then B.col e i else 0)
  by_cases he : e.toFinset ⊆ L
  · simp only [if_pos he,h e he]
  · simp only [if_neg he]

end SimpleGraph.MultiGraph
