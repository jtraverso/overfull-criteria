module

public import OverfullWork.OsthusStadenMergeDataFromBalancing
public import OverfullWork.OsthusStadenHamiltonPacksFromPhysicalLayers

@[expose] public section


/-! Complete the physical extraction and merging from the balanced
layers of §5.9 with a common set of margins. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u v

set_option maxHeartbeats 3500000 in
/-- From the balanced physical slices and their own bridge stars,
obtain the full family of edge-disjoint Hamilton cycles of §5.11.
The hypotheses give the numerical margins of the extraction and the
reuse of H3. -/
theorem exists_osthus_staden_hamilton_pack_from_balanced_layers
    (fraction δ δ₃ dMerge εMerge νMerge τMerge γMerge : ℝ)
    (hFraction : 0 < fraction) (hFractionOne : fraction ≤ 1)
    (hδ : 0 ≤ δ) (hδ₃ : 0 < δ₃) (hδ₃One : δ₃ ≤ 1) (hδSplit : δ ≤ δ₃/4)
    (hν : 0 < νMerge) (hWidth : εMerge+νMerge ≤ τMerge) (hεMerge : 0 < εMerge)
    (hτγ : 16*τMerge ≤ γMerge) (hγ : γMerge ≤ 1) (hMerge : 0 < dMerge) :
    ∃ N : ℕ, ∀ {V : Type v} [Fintype V] {I : Type u} [Fintype I] [Nonempty I]
      {r s p mBase m : ℕ} [NeZero (2*s)] [NeZero p]
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
      (κ cutoff minDemand batch : ℕ)
      (F : RefinedFactorIndex r (2*s) p → Digraph V)
      (B : RefinedFactorIndex r (2*s) p → Finset (V × V))
      (reserve : Digraph V) (redCap balancedCap : ℝ),
      N ≤ 2*m-1 →
      balancedCap ≤ ((κ-minDemand:ℕ):ℝ) →
      OsthusStadenDenseFactorMargins (2*m-1) κ cutoff minDemand δ₃ ((1-fraction)*d) →
      κ ≤ (p-4)*batch → δ₃ ≤ εMerge → dMerge ≤ fraction*d-2*δ₃ →
      (batch:ℝ)+νMerge*((2*m-1:ℕ):ℝ) ≤ dMerge*τMerge*((2*m-1:ℕ):ℝ) →
      γMerge*((2*m-1:ℕ):ℝ)+(batch:ℝ) ≤ dMerge*((2*m-1:ℕ):ℝ) →
      (∀ j i, (src j i).1.1 = i ∧ (dst j i).1.1 = C i) →
      (∀ j i, D.selectedPCell false j ((A.factor j).symm (src j i)) ∧
        D.selectedPCell true j (dst j i)) →
      letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
      let J := RefinedFactorIndex r (2*s) p
      let original := fun (j : J) => primaryPCells (R j.1)
      let cell := fun j u => (original j u).erase (erase j u)
      let ordinary := fun j => univ.biUnion (cell j)
      let label := fun (j : J) => trimPCellLabel (A.label j.1) (erase j)
      let incoming := D.allPCells true
      let outgoing := D.allPCells false
      let send := fun (j : J) => shadowSend (A.factor j) (incoming j) (outgoing j)
      let receive := fun (j : J) => shadowReceive (A.factor j) (incoming j) (outgoing j)
      let halfIn := fun (j : J) i =>
        primaryHalfCell (R j.1) ((A.factor j).symm (src j i)) (redPhase p j.1.val).2
      let halfOut := fun (j : J) i =>
        primaryHalfCell (R j.1) (dst j i) (redPhase p j.1.val).2
      let eligible := fun (j : J) u => balancingHalfCell base (R j.1) (erase j) u (redPhase p j.1.val).2
      let red := fun j => physicalExceptionalArcs (F j) (ordinary j) ∪ B j
      let whole := fun j => F j ⊔ digraphOfArcs (B j)
      (∀ j e, e ∈ B j → ∃ a b, e.1 ∈ eligible j a ∧ e.2 ∈ eligible j b ∧
        a ∈ Set.range (send j) ∧ b ∈ Set.range (receive j)) →
      (∀ j, Disjoint (Set.range (send j)) (Set.range (receive j))) →
      ∀ (bridge : TrimmedPhysicalBridgeLayers G (unwoundSlice E A.label A.factor) A.factor C
          original erase src dst halfIn halfOut κ (2*m) δ d),
        OsthusStadenRedLayerProperties G reserve (unwoundSlice E A.label A.factor)
          F A.factor ordinary cell D.vertices (fun j i => erase j (src j i))
          bridge.incoming bridge.outgoing κ redCap δ d →
        OsthusStadenBalancedLayerProperties G whole (fun j => trimLayerArcs (F j) (ordinary j))
          red ordinary cell label A.factor κ balancedCap δ d →
        ∃ Pack : Fin ((r*((2*s-1)*(p-1)))*κ) → Equiv.Perm V,
          (∀ i, HasSpanningCycle (fun x y => Pack i x = y)) ∧ (∀ i x, G.Adj x (Pack i x)) ∧
          ∀ i k, i ≠ k → ∀ x, Pack i x ≠ Pack k x := by
  obtain ⟨N₁,hN₁⟩ := exists_factors_and_h3_of_balanced_physical_layers.{u,v}
    fraction δ δ₃ hFraction hFractionOne hδ hδ₃ hδ₃One hδSplit
  obtain ⟨N₂,hN₂⟩ := exists_hamilton_pack_from_physical_layer_factors.{u,v,u}
    dMerge εMerge νMerge τMerge γMerge hν hWidth hεMerge hτγ hγ hMerge
  refine ⟨max N₁ N₂,?_⟩
  intro V _ I _ _ r s p mBase m _ _ G thin E f g σ εBase τ ε d base R A D hp hs hm C src dst erase
    κ cutoff minDemand batch F B reserve redCap balancedCap hN hCap hDense hBatch hReg hDensity hCost hDegree
    hTags hDir J original cell ordinary label incoming outgoing send receive halfIn halfOut eligible red whole
    hB hRanges bridge hRed hBalanced
  letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
  have hDis (j : J) (u v : RefinedVertex I (2*s) p) (hne : u ≠ v) : Disjoint (cell j u) (cell j v) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hne (Option.some.inj (((A.label_cell j.1 x u).mpr (mem_erase.mp hx).2).symm.trans
      ((A.label_cell j.1 x v).mpr (mem_erase.mp hy).2)))
  have hLabel (j : J) (u : RefinedVertex I (2*s) p) (x : V) : label j x = some u ↔ x ∈ cell j u :=
    trimPCellLabel_eq_some (A.label j.1) (original j) (erase j) (A.label_cell j.1) x u
  obtain ⟨P,_⟩ := hN₁ hBalanced (2*m-1) cutoff minDemand
    ((le_max_left _ _).trans hN) (fun _ => rfl) hDis bridge.cell_size hLabel hCap hDense
  have hBridge (j : J) : Nonempty (LayerBridgeData (A.factor j) (incoming j) (outgoing j) p
      ((red j).map (Equiv.prodCongr (P j).coord.symm (P j).coord.symm).toEmbedding) I) :=
    layer_merge_data_from_balanced_arcs base A D hp hs hm C src dst erase j κ δ (F j) (B j)
      (hTags j) (hDir j) (hRed.arc_support j) (hB j) (hRanges j) bridge (hRed.bridge_adjacency j) (P j)
  have hRoot (j : J) : Nonempty ↥(incoming j ∪ outgoing j) := by
    let i : I := Classical.choice inferInstance
    have hNonempty : (D.pCells true j i).Nonempty := card_pos.mp (by rw [D.pCells_card]; omega)
    obtain ⟨u,hu⟩ := hNonempty
    obtain ⟨z,hz,he⟩ := mem_map.mp hu
    have hu' : u ∈ incoming j := (D.mem_allPCells_iff true j u).mpr ⟨i,z,hz,he.symm⟩
    exact ⟨⟨u,mem_union_left (outgoing j) hu'⟩⟩
  have hPack := hN₂ G whole ordinary cell A.factor red incoming outgoing (2*m-1) κ p batch δ₃ (fraction*d)
    P (fun j => Classical.choice (hBridge j)) (fun j => Classical.choice (hRoot j))
    hBalanced.le hBalanced.disjoint_layers hBatch hδ₃.le hReg hDensity (by omega)
    ((le_max_right _ _).trans hN) hCost hDegree
  have hCard : Fintype.card J = r*((2*s-1)*(p-1)) := by
    calc
      _ = Fintype.card (RefinedFactorIndex r (2*s) p) :=
        Fintype.card_congr (show J ≃ RefinedFactorIndex r (2*s) p from Equiv.refl _)
      _ = _ := card_refined_factor_index r (2*s) p
  rwa [hCard] at hPack

end OverfullWork.DirectedRobustExpansion
