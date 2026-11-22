module

public import OverfullWork.OsthusStadenRedRoutingFromPhysicalArcs
public import OverfullWork.OsthusStadenBalancingHalfCells

@[expose] public section


/-! Relate the actual H2 choices and original exceptional arcs to the
two directional shadow ranges. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

set_option maxHeartbeats 1450000 in
/-- Every balanced red arc that leaves an ordinary cell uses the chosen
half of a shadow source. Every balanced red arc that enters an ordinary
cell uses a shadow target. Exceptional vertices remain independent. -/
theorem balanced_red_arc_directions_on_physical_layer
    {V I : Type*} [Fintype V] [Fintype I] {r s p mBase m : ℕ} [NeZero (2*s)] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {f : V → Option I} {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {εBase τ ε d : ℝ}
    (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster f i) (2*s) p mBase εBase εBase εBase)
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    {A : UnwoundPrimarySlices G thin E g σ τ ε d R}
    (D : PrimaryRedSelection (p := p) A.coordinates) (j : RefinedFactorIndex r (2*s) p)
    (erase : RefinedVertex I (2*s) p → V) (F : Digraph V) (B : Finset (V × V)) :
    let cell := fun u => (primaryPCells (R j.1) u).erase (erase u)
    let ordinary := univ.biUnion cell
    let label := trimPCellLabel (A.label j.1) erase
    let half := fun u => primaryHalfCell (R j.1) u (redPhase p j.1.val).2
    let eligible := fun u => balancingHalfCell base (R j.1) erase u (redPhase p j.1.val).2
    let incoming := D.allPCells true j
    let outgoing := D.allPCells false j
    let send := shadowSend (A.factor j) incoming outgoing
    let receive := shadowReceive (A.factor j) incoming outgoing
    let red := physicalExceptionalArcs F ordinary ∪ B
    (∀ x y, F.Adj x y →
      (x ∈ ordinary ∧ y ∈ ordinary) ∨
      (x ∉ ordinary ∧ y ∈ ordinary ∧ y ∈ D.vertices true j) ∨
      (y ∉ ordinary ∧ x ∈ ordinary ∧ x ∈ D.vertices false j)) →
    (∀ e ∈ B, ∃ u v, e.1 ∈ eligible u ∧ e.2 ∈ eligible v ∧ u ∈ Set.range send ∧ v ∈ Set.range receive) →
    (∀ x y u, (x,y) ∈ red → label x = some u → u ∈ Set.range send ∧ x ∈ half u) ∧
    (∀ x y u, (x,y) ∈ red → label y = some u → u ∈ Set.range receive) ∧
    ∀ e ∈ red, e.1 ∈ ordinary ∨ e.2 ∈ ordinary := by
  intro cell ordinary label half eligible incoming outgoing send receive red hF hB
  have hLabel (x : V) (u : RefinedVertex I (2*s) p) : label x = some u ↔ x ∈ cell u :=
    trimPCellLabel_eq_some (A.label j.1) (primaryPCells (R j.1)) erase (A.label_cell j.1) x u
  have hOrd (u : RefinedVertex I (2*s) p) : cell u ⊆ ordinary :=
    fun x hx => mem_biUnion.mpr ⟨u,mem_univ _,hx⟩
  have hEligible (u : RefinedVertex I (2*s) p) : eligible u ⊆ cell u :=
    (balancingHalfCell_subsets base (R j.1) erase u (redPhase p j.1.val).2).2
  have hDis : Disjoint incoming outgoing := by
    apply disjoint_left.mpr
    intro u hu hv
    exact D.pCell_unique_direction j u ⟨(D.mem_allPCells_iff _ _ _).mp hu,(D.mem_allPCells_iff _ _ _).mp hv⟩
  refine ⟨?_,?_,?_⟩
  · intro x y u h hl
    rcases mem_union.mp h with h | h
    · obtain ⟨hAdj,hExc⟩ := (mem_filter.mp h).2
      have hx := (hLabel x u).mp hl
      have hOx := hOrd u hx
      rcases hF x y hAdj with hh | hh | hh
      · exact (hExc.elim (fun h => h hh.1) (fun h => h hh.2)).elim
      · exact (hh.1 hOx).elim
      · have hp := D.mem_half_of_mem_vertices_and_pCell false j u x hh.2.2 (mem_erase.mp hx).2
        have hu := (D.mem_allPCells_iff false j u).mpr hp.1
        exact ⟨outgoing_subset_shadow_range (A.factor j) incoming outgoing hDis u hu,hp.2⟩
    · obtain ⟨a,b,hx,_,hs,_⟩ := hB (x,y) h
      have ha := (hLabel x a).mpr (hEligible a hx)
      obtain rfl := Option.some.inj (ha.symm.trans hl)
      exact ⟨hs,(mem_erase.mp (mem_inter.mp hx).2).2⟩
  · intro x y u h hl
    rcases mem_union.mp h with h | h
    · obtain ⟨hAdj,hExc⟩ := (mem_filter.mp h).2
      have hy := (hLabel y u).mp hl
      have hOy := hOrd u hy
      rcases hF x y hAdj with hh | hh | hh
      · exact (hExc.elim (fun h => h hh.1) (fun h => h hh.2)).elim
      · have hp := D.mem_half_of_mem_vertices_and_pCell true j u y hh.2.2 (mem_erase.mp hy).2
        exact incoming_subset_shadow_range (A.factor j) incoming outgoing u ((D.mem_allPCells_iff _ _ _).mpr hp.1)
      · exact (hh.1 hOy).elim
    · obtain ⟨a,b,_,hy,_,hr⟩ := hB (x,y) h
      have hb := (hLabel y b).mpr (hEligible b hy)
      obtain rfl := Option.some.inj (hb.symm.trans hl)
      exact hr
  · intro e h
    rcases mem_union.mp h with h | h
    · rcases hF e.1 e.2 (mem_filter.mp h).2.1 with hh | hh | hh
      · exact Or.inl hh.1
      · exact Or.inr hh.2.1
      · exact Or.inl hh.2.1
    · obtain ⟨u,_,hx,_,_,_⟩ := hB e h
      exact Or.inl (hOrd u (hEligible u hx))

end OverfullWork.DirectedRobustExpansion
