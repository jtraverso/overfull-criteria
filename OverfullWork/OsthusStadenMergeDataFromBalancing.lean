module

public import OverfullWork.OsthusStadenPhysicalBridgeRouting

@[expose] public section


/-! Certify the cut links directly from a balanced layer and its
physical bridge stars. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

set_option maxHeartbeats 2500000 in
/-- The red arcs, bridge stars and split-off H3 all use the same physical
vertices. This supplies the routing hypotheses for the merging lemma. -/
theorem layer_merge_data_from_balanced_arcs
    {V I : Type*} [Fintype V] [Fintype I] {r s p mBase m : ℕ} [NeZero (2*s)] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {f : V → Option I} {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {εBase τ ε d : ℝ}
    (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster f i) (2*s) p mBase εBase εBase εBase)
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    (A : UnwoundPrimarySlices G thin E g σ τ ε d R)
    (D : PrimaryRedSelection (p := p) A.coordinates) (hp : 3 ≤ p) (hs : 2 ≤ s) (hm : 2 ≤ m)
    (C : Equiv.Perm I)
    (src dst : RefinedFactorIndex r (2*s) p → I → RefinedVertex I (2*s) p)
    (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
    (j : RefinedFactorIndex r (2*s) p) (κ : ℕ) (δ : ℝ)
    (F : Digraph V) (B : Finset (V × V)) :
    let original := fun (k : RefinedFactorIndex r (2*s) p) => primaryPCells (R k.1)
    let cell := fun u => (original j u).erase (erase j u)
    let ordinary := univ.biUnion cell
    let incoming := D.allPCells true j
    let outgoing := D.allPCells false j
    let label := trimPCellLabel (A.label j.1) (erase j)
    let half := fun u => primaryHalfCell (R j.1) u (redPhase p j.1.val).2
    let eligible := fun u => balancingHalfCell base (R j.1) (erase j) u (redPhase p j.1.val).2
    let halfIn := fun (k : RefinedFactorIndex r (2*s) p) i =>
      primaryHalfCell (R k.1) ((A.factor k).symm (src k i)) (redPhase p k.1.val).2
    let halfOut := fun (k : RefinedFactorIndex r (2*s) p) i =>
      primaryHalfCell (R k.1) (dst k i) (redPhase p k.1.val).2
    let red := physicalExceptionalArcs F ordinary ∪ B
    (∀ i, (src j i).1.1 = i ∧ (dst j i).1.1 = C i) →
    (∀ i, D.selectedPCell false j ((A.factor j).symm (src j i)) ∧ D.selectedPCell true j (dst j i)) →
    (∀ x y, F.Adj x y →
      (x ∈ ordinary ∧ y ∈ ordinary) ∨
      (x ∉ ordinary ∧ y ∈ ordinary ∧ y ∈ D.vertices true j) ∨
      (y ∉ ordinary ∧ x ∈ ordinary ∧ x ∈ D.vertices false j)) →
    (∀ e ∈ B, ∃ u v, e.1 ∈ eligible u ∧ e.2 ∈ eligible v ∧
      u ∈ Set.range (shadowSend (A.factor j) incoming outgoing) ∧
      v ∈ Set.range (shadowReceive (A.factor j) incoming outgoing)) →
    Disjoint (Set.range (shadowSend (A.factor j) incoming outgoing))
      (Set.range (shadowReceive (A.factor j) incoming outgoing)) →
    ∀ (P : TrimmedPhysicalBridgeLayers G (unwoundSlice E A.label A.factor) A.factor C
        original erase src dst halfIn halfOut κ (2*m) δ d),
      (∀ i x, (F.Adj x (erase j (src j i)) ↔ x ∈ P.incoming j i) ∧
        (F.Adj (erase j (src j i)) x ↔ x ∈ P.outgoing j i)) →
      ∀ {ε₃ d₃ : ℝ} (K : OsthusStadenPhysicalFactors (F ⊔ digraphOfArcs B)
          ordinary cell (A.factor j) red (2*m-1) κ ε₃ d₃),
        Nonempty (LayerBridgeData (A.factor j) incoming outgoing p
          (red.map (Equiv.prodCongr K.coord.symm K.coord.symm).toEmbedding) I) := by
  intro original cell ordinary incoming outgoing label half eligible halfIn halfOut red hTags hDir hArc hB
    hRanges P hP ε₃ d₃ K
  have hCell (u : RefinedVertex I (2*s) p) : cell u ⊆ ordinary :=
    fun x hx => mem_biUnion.mpr ⟨u,mem_univ _,hx⟩
  have hLabel (u : RefinedVertex I (2*s) p) (x : V) : label x = some u ↔ x ∈ cell u :=
    trimPCellLabel_eq_some (A.label j.1) (original j) (erase j) (A.label_cell j.1) x u
  obtain ⟨hSrc,hDst,hInd⟩ := balanced_red_arc_directions_on_physical_layer base D j (erase j) F B hArc hB
  obtain ⟨routing⟩ := red_arc_routing_of_physical_support ordinary cell half label K.coord K.exceptional_coord
    K.ordinary_coord hCell hLabel (A.factor j) incoming outgoing red hRanges
    (fun u => by
      change (primaryHalfCell (R j.1) u (redPhase p j.1.val).2).card < 2*m-1
      rw [primaryHalfCell_card]
      omega) hSrc hDst hInd
  have hOutside (i : I) : erase j (src j i) ∉ ordinary := P.bridge_exceptional j i
  have hBOrd (e : V × V) (he : e ∈ B) : e.1 ∈ ordinary ∧ e.2 ∈ ordinary := by
    obtain ⟨u,v,hu,hv,_,_⟩ := hB e he
    exact ⟨hCell u ((balancingHalfCell_subsets base (R j.1) (erase j) u _).2 hu),
      hCell v ((balancingHalfCell_subsets base (R j.1) (erase j) v _).2 hv)⟩
  refine layer_bridge_data_of_physical_stars D (by omega) hs j C P.primary_spanning
    ordinary cell K.coord K.exceptional_coord K.ordinary_coord red (src j) (dst j)
    (fun i => erase j (src j i)) hTags hDir hOutside ?_ ?_ routing
  · intro i x hx
    rcases mem_union.mp hx with h | h
    · have hh := (mem_erase.mp ((P.star_support j i).1 ((hP i x).1.mp (mem_filter.mp h).2.1)))
      exact mem_erase.mpr ⟨hh.1,primaryHalfCell_subset _ _ _ hh.2⟩
    · exact (hOutside i (hBOrd _ h).2).elim
  · intro i x hx
    rcases mem_union.mp hx with h | h
    · have hh := (mem_erase.mp ((P.star_support j i).2 ((hP i x).2.mp (mem_filter.mp h).2.1)))
      exact mem_erase.mpr ⟨hh.1,primaryHalfCell_subset _ _ _ hh.2⟩
    · exact (hOutside i (hBOrd _ h).1).elim

end OverfullWork.DirectedRobustExpansion
