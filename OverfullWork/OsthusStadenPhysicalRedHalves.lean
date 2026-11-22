module

public import OverfullWork.OsthusStadenPrimaryRedSelection

@[expose] public section


/-! The directional half-cells are actual subsets of the initial slices. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

/-- Choose one of the two halves of the labelled p-cell. -/
noncomputable def primaryHalfCell {V I J : Type*} [Fintype V] [Fintype I]
    {profiles : J → Finset V} {f : V → Option I} {s p m : ℕ} [NeZero s] [NeZero p]
    {ε₁ ε₂ ε₃ : ℝ} (R : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p m ε₁ ε₂ ε₃)
    (a : RefinedVertex I s p) (half : Bool) : Finset V :=
  ((R a.1.1).halves ((ZMod.finEquiv s).symm a.1.2) ((ZMod.finEquiv p).symm a.2)).cells
    (if half then 1 else 0)

theorem primaryHalfCell_card {V I J : Type*} [Fintype V] [Fintype I]
    {profiles : J → Finset V} {f : V → Option I} {s p m : ℕ} [NeZero s] [NeZero p]
    {ε₁ ε₂ ε₃ : ℝ} (R : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p m ε₁ ε₂ ε₃)
    (a : RefinedVertex I s p) (half : Bool) : (primaryHalfCell R a half).card = m :=
  ((R a.1.1).halves _ _).size _

theorem primaryHalfCell_subset {V I J : Type*} [Fintype V] [Fintype I]
    {profiles : J → Finset V} {f : V → Option I} {s p m : ℕ} [NeZero s] [NeZero p]
    {ε₁ ε₂ ε₃ : ℝ} (R : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p m ε₁ ε₂ ε₃)
    (a : RefinedVertex I s p) (half : Bool) : primaryHalfCell R a half ⊆ primaryPCells R a :=
  ((R a.1.1).halves _ _).subset _

/-- The physical p-cells selected in one direction in a primary cluster. -/
noncomputable def PrimaryRedSelection.pCells {I : Type*} {r s p : ℕ} [NeZero (2*s)]
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)} (D : PrimaryRedSelection (p := p) C)
    (q : Bool) (j : RefinedFactorIndex r (2*s) p) (i : I) : Finset (RefinedVertex I (2*s) p) :=
  (D.select q j i).map ⟨redPLabel j.1.val i,fun _ _ h =>
    (ZMod.finEquiv (2*s)).injective (congrArg (fun a => a.1.2) h)⟩

theorem PrimaryRedSelection.pCells_card {I : Type*} {r s p : ℕ} [NeZero (2*s)]
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)} (D : PrimaryRedSelection (p := p) C)
    (q : Bool) (j : RefinedFactorIndex r (2*s) p) (i : I) : (D.pCells q j i).card = s-1 :=
  card_map _ |>.trans (D.size q j i)

section Physical

variable {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero (2*s)] [NeZero p]
variable {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
variable {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ η d : ℝ}
variable {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
  (cluster (g t) i) (2*s) p m τ τ τ}
variable {A : UnwoundPrimarySlices G thin E g σ τ η d R}

/-- The vertices eligible for one orientation in a layer. -/
noncomputable def PrimaryRedSelection.vertices (D : PrimaryRedSelection (p := p) A.coordinates)
    (q : Bool) (j : RefinedFactorIndex r (2*s) p) : Finset V :=
  univ.biUnion (fun i => (D.pCells q j i).biUnion
    (fun a => primaryHalfCell (R j.1) a (redPhase p j.1.val).2))

theorem PrimaryRedSelection.mem_half_of_mem_vertices_and_pCell
    (D : PrimaryRedSelection (p := p) A.coordinates) (q : Bool)
    (j : RefinedFactorIndex r (2*s) p) (a : RefinedVertex I (2*s) p) (x : V)
    (hx : x ∈ D.vertices q j) (ha : x ∈ primaryPCells (R j.1) a) :
    D.selectedPCell q j a ∧ x ∈ primaryHalfCell (R j.1) a (redPhase p j.1.val).2 := by
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
  obtain ⟨b,hb,hxb⟩ := mem_biUnion.mp hi
  have hba : b = a := Option.some.inj
    (((A.label_cell j.1 x b).mpr (primaryHalfCell_subset (R j.1) b _ hxb)).symm.trans
      ((A.label_cell j.1 x a).mpr ha))
  subst b
  obtain ⟨z,hz,hzEq⟩ := mem_map.mp hb
  exact ⟨⟨i,z,hz,hzEq.symm⟩,hxb⟩

/-- Red4 on the actual vertices. Both directions use one half of the
given p-cell, so no more than half the cell can be incident to red arcs. -/
theorem PrimaryRedSelection.red4_on_vertices
    (D : PrimaryRedSelection (p := p) A.coordinates)
    (j : RefinedFactorIndex r (2*s) p) (a : RefinedVertex I (2*s) p) :
    (((D.vertices true j ∪ D.vertices false j) ∩ primaryPCells (R j.1) a).card) ≤ m := by
  refine (card_le_card ?_).trans_eq (primaryHalfCell_card (R j.1) a (redPhase p j.1.val).2)
  intro x hx
  obtain ⟨hRed,hP⟩ := mem_inter.mp hx
  rcases mem_union.mp hRed with h | h
  · exact (D.mem_half_of_mem_vertices_and_pCell true j a x h hP).2
  · exact (D.mem_half_of_mem_vertices_and_pCell false j a x h hP).2

/-- Red6 on the actual vertices. A p-cell that receives red arcs
contains no vertex that can send a red arc in the same layer. -/
theorem PrimaryRedSelection.red6_on_vertices
    (D : PrimaryRedSelection (p := p) A.coordinates)
    (j : RefinedFactorIndex r (2*s) p) (a : RefinedVertex I (2*s) p) :
    ¬ ((D.vertices true j ∩ primaryPCells (R j.1) a).Nonempty ∧
      (D.vertices false j ∩ primaryPCells (R j.1) a).Nonempty) := by
  rintro ⟨⟨x,hx⟩,y,hy⟩
  obtain ⟨hx',hxP⟩ := mem_inter.mp hx
  obtain ⟨hy',hyP⟩ := mem_inter.mp hy
  exact D.pCell_unique_direction j a ⟨
    (D.mem_half_of_mem_vertices_and_pCell true j a x hx' hxP).1,
    (D.mem_half_of_mem_vertices_and_pCell false j a y hy' hyP).1⟩

end Physical
end OverfullWork.DirectedRobustExpansion
