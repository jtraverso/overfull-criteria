module

public import OverfullWork.TwoStageResiduePalette

@[expose] public section


/-! # Attach the actual internal-residue palette to the filled seed colors

Disjoint palettes preserve the seed 1-factors. The resulting actual
partial coloring covers every internal copy; its fresh classes retain
the constructed two-stage color graphs. Completing those classes is
still required before using the bipartite residual factorization.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k l : ℕ}

def attach_internal_residue (P : M.PartialColouring k) (A : Finset V)
    (C : (P.available.internalPart A).EdgeColoring l) : M.PartialColouring (k+l) where
  graph := P.graph.addCopies (P.available.internalPart A)
  colouring := P.colouring.addCopies C
  le e := by
    have hCap := P.le e
    have hInt := P.available.internalPart_le A e
    change P.graph.mult e+(P.available.internalPart A).mult e ≤ M.mult e
    change (P.available.internalPart A).mult e ≤ M.mult e-P.graph.mult e at hInt
    omega

theorem attach_internal_residue_old_colour (P : M.PartialColouring k) (A : Finset V)
    (C : (P.available.internalPart A).EdgeColoring l) (i : Fin k) :
    ((P.attach_internal_residue A C).colouring.colourGraph (Fin.castAdd l i))=P.colouring.colourGraph i :=
  P.colouring.addCopies_colourGraph_left C i

theorem attach_internal_residue_fresh_colour (P : M.PartialColouring k) (A : Finset V)
    (C : (P.available.internalPart A).EdgeColoring l) (i : Fin l) :
    ((P.attach_internal_residue A C).colouring.colourGraph (Fin.natAdd k i))=C.colourGraph i :=
  P.colouring.addCopies_colourGraph_right C i

theorem attach_internal_residue_covers (P : M.PartialColouring k) (A : Finset V)
    (C : (P.available.internalPart A).EdgeColoring l) :
    (P.attach_internal_residue A C).CoversInternal A := by
  intro x y hSame
  change P.graph.mult s(x,y)+(P.available.internalPart A).mult s(x,y)=M.mult s(x,y)
  rw [internalPart_mult,if_pos hSame]
  change P.graph.mult s(x,y)+(M.mult s(x,y)-P.graph.mult s(x,y))=M.mult s(x,y)
  exact Nat.add_sub_of_le (P.le s(x,y))

end SimpleGraph.MultiGraph.PartialColouring
