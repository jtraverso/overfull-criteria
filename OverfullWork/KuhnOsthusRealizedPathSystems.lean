module

public import OverfullWork.KuhnOsthusPhysicalWalkRealization

@[expose] public section


/-! The physical walk pieces are added to the prescribed systems
in Kühn–Osthus Lemma 9.5. Taken together they use each reserved or
prescribed arc exactly once. -/
namespace OverfullWork.DirectedRobustExpansion

variable {V I : Type*}

/-- Join the physical realization to the prescribed path systems.
Disjoint vertex supports certify the path property, while the
two arc partitions certify exact coverage of the union. -/
theorem join_walk_pieces_to_prescribed_systems (U W : Digraph V) (D C : I → Digraph V)
    (hDis : ∀ x y, U.Adj x y → ¬ W.Adj x y)
    (hDU : ∀ i, D i ≤ U) (hCW : ∀ i, C i ≤ W)
    (hDPart : ∀ x y, U.Adj x y → ∃! i, (D i).Adj x y)
    (hCPart : ∀ x y, W.Adj x y → ∃! i, (C i).Adj x y)
    (hD : ∀ i, IsDirectedPathSystem (D i)) (hC : ∀ i, IsDirectedPathSystem (C i))
    (hAvoid : ∀ i x, IncidentTo (D i) x → ¬ IncidentTo (C i) x) :
    let combined (i : I) := D i ⊔ C i
    (∀ i, IsDirectedPathSystem (combined i) ∧ combined i ≤ U ⊔ W) ∧
      ∀ x y, (U ⊔ W).Adj x y ↔ ∃! i, (combined i).Adj x y := by
  intro combined
  have hLe (i : I) : combined i ≤ U ⊔ W := sup_le_sup (hDU i) (hCW i)
  refine ⟨fun i => ⟨(hD i).sup_of_disjoint_vertices (hC i) (hAvoid i),hLe i⟩,?_⟩
  intro x y
  constructor
  · rintro (hu | hw)
    · obtain ⟨i,hi,hUnique⟩ := hDPart x y hu
      refine ⟨i,Or.inl hi,?_⟩
      rintro j (hj | hj)
      · exact hUnique j hj
      · exact (hDis x y hu (hCW j hj)).elim
    · obtain ⟨i,hi,hUnique⟩ := hCPart x y hw
      refine ⟨i,Or.inr hi,?_⟩
      rintro j (hj | hj)
      · exact (hDis x y (hDU j hj) hw).elim
      · exact hUnique j hj
  · rintro ⟨i,hi,_⟩
    exact hLe i hi

end OverfullWork.DirectedRobustExpansion
