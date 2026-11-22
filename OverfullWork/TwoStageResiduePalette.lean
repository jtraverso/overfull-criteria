module

public import OverfullWork.StageTwoResidueColouring

@[expose] public section


/-! # Assemble the two actual residue stages on one fresh palette

Keep the distinct Stage I colors separate from the aligned Stage II
colors, then glue the disjoint sides. All internal residue copies are
colored, and the per-side balance and class-size bounds are preserved.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 32000000

def EdgeColoring.transport_graph {N M : MultiGraph V} {k : ℕ} (C : N.EdgeColoring k) (h : N=M) :
    M.EdgeColoring k where
  col := C.col
  sum_col e := (C.sum_col e).trans (congrArg (fun T : MultiGraph V => T.mult e) h)
  proper := C.proper

theorem EdgeColoring.transport_graph_colourGraph {N M : MultiGraph V} {k : ℕ}
    (C : N.EdgeColoring k) (h : N=M) (i : Fin k) :
    ((C.transport_graph h).colourGraph i)=C.colourGraph i := by
  apply ext_mult
  intro e
  rfl

theorem EdgeColoring.addCopies_colourGraph_left {N M : MultiGraph V} {k l : ℕ}
    (C : N.EdgeColoring k) (D : M.EdgeColoring l) (i : Fin k) :
    (C.addCopies D).colourGraph (Fin.castAdd l i)=C.colourGraph i := by
  apply ext_mult
  intro e
  change Fin.addCases (C.col e) (D.col e) (Fin.castAdd l i)=C.col e i
  exact Fin.addCases_left i

theorem EdgeColoring.addCopies_colourGraph_right {N M : MultiGraph V} {k l : ℕ}
    (C : N.EdgeColoring k) (D : M.EdgeColoring l) (i : Fin l) :
    (C.addCopies D).colourGraph (Fin.natAdd k i)=D.colourGraph i := by
  apply ext_mult
  intro e
  change Fin.addCases (C.col e) (D.col e) (Fin.natAdd k i)=D.col e i
  exact Fin.addCases_right i

theorem StageTwoResidueColouring.exists_combined_palette {M : MultiGraph V} {A E : Finset V}
    {first : StageOneResidueColouring M A E} {h : ℕ}
    (second : StageTwoResidueColouring M A E first h) :
    ∃ C : (M.internalPart A).EdgeColoring (((M.restrict Aᶜ).incidentOn E).edgeCount+3*h),
      (∀ i, (C.colourGraph i).edgesWithin A=(C.colourGraph i).edgesWithin Aᶜ) ∧
      (∀ i, (C.colourGraph (Fin.castAdd (3*h) i)).edgesWithin A=1) ∧
      (∀ i, (3*h)*(C.colourGraph (Fin.natAdd ((M.restrict Aᶜ).incidentOn E).edgeCount i)).edgesWithin A ≤
        ((M.restrict A).subtractCopies first.left).edgeCount+3*h) ∧
      ∀ v ∈ E, v ∈ Aᶜ → ∀ i : Fin (3*h),
        (C.colourGraph (Fin.natAdd ((M.restrict Aᶜ).incidentOn E).edgeCount i)).degree v=0 := by
  let q := ((M.restrict Aᶜ).incidentOn E).edgeCount
  let CL₀ := first.leftColouring.addCopies second.left
  let CR₀ := first.rightColouring.addCopies second.right
  let CL := CL₀.transport_graph (add_subtract_of_le (M.restrict A) first.left first.left_le)
  let CR := CR₀.transport_graph (add_subtract_of_le (M.restrict Aᶜ) ((M.restrict Aᶜ).incidentOn E)
    ((M.restrict Aᶜ).incidentOn_le E))
  have hCL : ∀ i, CL.colourGraph i=CL₀.colourGraph i := CL₀.transport_graph_colourGraph _
  have hCR : ∀ i, CR.colourGraph i=CR₀.colourGraph i := CR₀.transport_graph_colourGraph _
  have hLeftI : ∀ i, CL.colourMass (Fin.castAdd (3*h) i)=1 := by
    intro i
    unfold EdgeColoring.colourMass
    rw [hCL,first.leftColouring.addCopies_colourGraph_left]
    exact first.left_mass i
  have hRightI : ∀ i, CR.colourMass (Fin.castAdd (3*h) i)=1 := by
    intro i
    unfold EdgeColoring.colourMass
    rw [hCR,first.rightColouring.addCopies_colourGraph_left]
    exact first.right_mass i
  have hLeftII : ∀ i, CL.colourGraph (Fin.natAdd q i)=second.left.colourGraph i := by
    intro i
    rw [hCL,first.leftColouring.addCopies_colourGraph_right]
  have hRightII : ∀ i, CR.colourGraph (Fin.natAdd q i)=second.right.colourGraph i := by
    intro i
    rw [hCR,first.rightColouring.addCopies_colourGraph_right]
  have hBalance : ∀ i, CL.colourMass i=CR.colourMass i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [hLeftI,hRightI]
    · intro j
      unfold EdgeColoring.colourMass
      rw [hLeftII,hRightII]
      exact second.balance j
  let C₀ := CL.addSamePalette CR (M.restrict_vertex_disjoint A)
  let C := C₀.transport_graph (restrict_add_restrict_compl M A)
  have hC : ∀ i, C.colourGraph i=C₀.colourGraph i := C₀.transport_graph_colourGraph _
  have hInside : ∀ i, (C.colourGraph i).edgesWithin A=CL.colourMass i := by
    intro i
    rw [hC,EdgeColoring.inside_addSamePalette]
    have hZero : (CR.colourGraph i).edgesWithin A=0 := by
      simpa only [compl_compl] using CR.inside_compl_restrict_zero Aᶜ i
    rw [hZero,←CL.colourMass_eq_inside_restrict A i,Nat.add_zero]
  have hOutside : ∀ i, (C.colourGraph i).edgesWithin Aᶜ=CR.colourMass i := by
    intro i
    rw [hC,EdgeColoring.inside_addSamePalette,CL.inside_compl_restrict_zero A i]
    rw [←CR.colourMass_eq_inside_restrict Aᶜ i,Nat.zero_add]
  refine ⟨C,fun i => by rw [hInside,hOutside];exact hBalance i,
    fun i => by rw [hInside];exact hLeftI i,?_,?_⟩
  · intro i
    rw [hInside]
    unfold EdgeColoring.colourMass
    rw [hLeftII]
    exact second.mass_bound i
  · intro v hv hvA i
    rw [hC]
    have hGraph : C₀.colourGraph (Fin.natAdd q i)=
        (CL.colourGraph (Fin.natAdd q i)).addCopies (CR.colourGraph (Fin.natAdd q i)) := by
      apply ext_mult
      intro e
      rfl
    rw [hGraph,degree_addCopies,hRightII,second.cleared v hv i]
    have hLeftZero : (M.restrict A).degree v=0 := by
      rw [degree_restrict,if_neg (mem_compl.mp hvA)]
    have hLe := CL.incidence_le_degree v (Fin.natAdd q i)
    omega

end SimpleGraph.MultiGraph
