module

public import OverfullWork.FirstAnchorScale

@[expose] public section


namespace SimpleGraph.MultiGraph.EdgeColoring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {A : Finset V}

theorem occupied_compl_eq_of_internal_balance {k : ℕ} (C : (M.internalPart A).EdgeColoring k)
    (i : Fin k) (hBalance : (C.colourGraph i).edgesWithin A=(C.colourGraph i).edgesWithin Aᶜ) :
    (Aᶜ\C.missingSet Aᶜ i).card=(A\C.missingSet A i).card := by
  have hl := C.internal_missing_count A i
  have hr := C.internal_missing_count_compl A i
  have hcl := card_sdiff_add_card_eq_card (show C.missingSet A i ⊆ A from filter_subset _ _)
  have hcr := card_sdiff_add_card_eq_card (show C.missingSet Aᶜ i ⊆ Aᶜ from filter_subset _ _)
  omega

end SimpleGraph.MultiGraph.EdgeColoring
