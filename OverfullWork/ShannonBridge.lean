module

public import OverfullWork.GeneralCopies
public import ShannonColouring.Shannon

@[expose] public section


namespace SimpleGraph.MultiGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Shannon's theorem transported to the exact multiplicity model. -/
theorem exists_edgeColoring_shannon (M : MultiGraph V) (d : ℕ)
    (hdeg : ∀ v, M.degree v ≤ d) : Nonempty (M.EdgeColoring (3*d/2)) := by
  obtain ⟨c,hc⟩ := ShannonColouring.shannon (GeneralCopies.ends M)
    (GeneralCopies.loopless M) d (fun v => by rw [GeneralCopies.degree_eq]; exact hdeg v)
  exact ⟨GeneralCopies.edgeColoring M c hc⟩

end SimpleGraph.MultiGraph
