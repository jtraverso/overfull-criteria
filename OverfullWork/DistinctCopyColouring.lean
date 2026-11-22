module

public import OverfullWork.ResidueCopySelection

@[expose] public section


/-! # Color each selected edge copy with its own color

The palette is the actual edge count. Enumerating the finite copy type
constructs a proper coloring with exactly one copy in each color.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem GeneralCopies.card_copies (M : MultiGraph V) :
    Fintype.card (GeneralCopies.Copies M)=M.edgeCount := by
  simp only [GeneralCopies.Copies,Fintype.card_sigma,Fintype.card_fin,edgeCount]

theorem exists_distinct_copy_colouring (M : MultiGraph V) :
    ∃ C : M.EdgeColoring M.edgeCount, ∀ i, C.colourMass i=1 := by
  let e : GeneralCopies.Copies M ≃ Fin M.edgeCount := Fintype.equivOfCardEq
    (by simpa only [Fintype.card_fin] using GeneralCopies.card_copies M)
  have hProper : ShannonColouring.IsProperEdgeColouring (GeneralCopies.ends M) e := by
    intro x y hxy _ he
    exact hxy (e.injective he)
  let C := GeneralCopies.edgeColoring M e hProper
  refine ⟨C,?_⟩
  intro i
  change (∑ p, GeneralCopies.colouredCopies M e p i)=1
  unfold GeneralCopies.colouredCopies
  rw [sum_card_fiberwise_eq_card_filter]
  simp only [mem_univ,filter_true]
  have hFiber : (univ.filter (fun x : GeneralCopies.Copies M => e x=i))={e.symm i} := by
    ext x
    simp only [mem_filter,mem_univ,true_and,mem_singleton]
    exact e.apply_eq_iff_eq_symm_apply
  rw [hFiber,card_singleton]

end SimpleGraph.MultiGraph
