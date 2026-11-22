module

public import OverfullWork.OsthusStadenBalancedArcDirections
public import OverfullWork.OsthusStadenLayerMerge

@[expose] public section


/-! Assemble the cut-link input of §5.11 from the physical bridges. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

set_option maxHeartbeats 1950000 in
/-- The original bridge stars determine the links between the primary
cycles, in the same coordinates as the extracted factors and H3. -/
theorem layer_bridge_data_of_physical_stars
    {V I : Type*} [Fintype V] [Fintype I] {r s p m n : ℕ} [NeZero (2*s)] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ ε d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    {A : UnwoundPrimarySlices G thin E g σ τ ε d R}
    (D : PrimaryRedSelection (p := p) A.coordinates) (hp : 1 < p) (hs : 2 ≤ s)
    (j : RefinedFactorIndex r (2*s) p) (C : Equiv.Perm I) (hC : ∀ u v, C.SameCycle u v)
    (ordinary : Finset V) (cell : RefinedVertex I (2*s) p → Finset V)
    (coord : SliceVertex ↥(ordinaryᶜ : Finset V) (RefinedVertex I (2*s) p) (Fin n) ≃ V)
    (hExc : ∀ x, coord (.inl x) = x.val)
    (hMap : ∀ u, (univ : Finset (Fin n)).map (sliceCellEmbedding coord u) = cell u)
    (red : Finset (V × V))
    (source target : I → RefinedVertex I (2*s) p) (center : I → V)
    (hTag : ∀ i, (source i).1.1 = i ∧ (target i).1.1 = C i)
    (hDir : ∀ i, D.selectedPCell false j ((A.factor j).symm (source i)) ∧
      D.selectedPCell true j (target i))
    (hOutside : ∀ i, center i ∉ ordinary)
    (hIn : ∀ i x, (x,center i) ∈ red → x ∈ cell ((A.factor j).symm (source i)))
    (hOut : ∀ i x, (center i,x) ∈ red → x ∈ cell (target i)) :
    let incoming := D.allPCells true j
    let outgoing := D.allPCells false j
    let pulled := red.map (Equiv.prodCongr coord.symm coord.symm).toEmbedding
    RedArcRouting (A.factor j) incoming outgoing pulled →
    Nonempty (LayerBridgeData (A.factor j) incoming outgoing p pulled I) := by
  letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
  intro incoming outgoing pulled routing
  let project (u : RefinedVertex I (2*s) p) := u.1.1
  have hDis : Disjoint incoming outgoing := by
    apply disjoint_left.mpr
    intro x hx hy
    exact D.pCell_unique_direction j x ⟨(D.mem_allPCells_iff _ _ _).mp hx,(D.mem_allPCells_iff _ _ _).mp hy⟩
  have hSep (u : RefinedVertex I (2*s) p) (hu : u ∈ outgoing) : A.factor j u ∉ incoming := by
    intro hv
    have h := D.distance hp ((D.mem_allPCells_iff false j _).mp hu)
      ((D.mem_allPCells_iff true j _).mp hv) (k := 1) (by decide) (by rw [pow_one])
    omega
  have hSelected (a : ↥(incoming ∪ outgoing)) : ∃ q, D.selectedPCell q j a := by
    rcases mem_union.mp a.property with h | h
    · exact ⟨true,(D.mem_allPCells_iff _ _ _).mp h⟩
    · exact ⟨false,(D.mem_allPCells_iff _ _ _).mp h⟩
  have hSpacing (a b : ↥(incoming ∪ outgoing)) k (hk : 0 < k)
      (h : ((A.factor j)^k) a.val = b.val) : p ≤ k := by
    obtain ⟨q,hq⟩ := hSelected a
    obtain ⟨q',hq'⟩ := hSelected b
    exact D.distance hp hq hq' hk h
  have hOrbit (x y : RefinedVertex I (2*s) p) :
      (A.factor j).SameCycle x y ↔ (σ j.1).SameCycle (project x) (project y) := by
    rcases j with ⟨t,a,b⟩
    exact A.cycles t a b x y
  have hSend (x : RefinedVertex I (2*s) p) (h : x ∈ outgoing) :
      shadowSend (A.factor j) incoming outgoing ⟨x,mem_union_right incoming h⟩ = x := by
    have hn : x ∉ incoming := fun h' => disjoint_left.mp hDis h' h
    simp only [shadowSend,show (⟨x,mem_union_right incoming h⟩ : ↥(incoming ∪ outgoing)).val ∉ incoming from hn,if_false]
  have hReceive (x : RefinedVertex I (2*s) p) (h : x ∈ incoming) :
      shadowReceive (A.factor j) incoming outgoing ⟨x,mem_union_left outgoing h⟩ = x := by
    simp only [shadowReceive,shadowSend,show (⟨x,mem_union_left outgoing h⟩ :
      ↥(incoming ∪ outgoing)).val ∈ incoming from h,if_true,Equiv.apply_symm_apply]
  have hMem (x y : SliceVertex ↥(ordinaryᶜ : Finset V) (RefinedVertex I (2*s) p) (Fin n))
      (h : (x,y) ∈ pulled) : (coord x,coord y) ∈ red := by
    obtain ⟨⟨v,w⟩,hv,he⟩ := mem_map.mp h
    have hx : coord.symm v = x := congrArg Prod.fst he
    have hy : coord.symm w = y := congrArg Prod.snd he
    simpa only [←hx,←hy,coord.apply_symm_apply] using hv
  refine ⟨⟨σ j.1,project,C,routing,hSep,hSpacing,hOrbit,?_,hC,?_⟩⟩
  · intro i
    have hn : ((outgoing.filter (fun u => project u = i))).Nonempty :=
      card_pos.mp (by rw [show (outgoing.filter (fun u => project u = i)) = D.pCells false j i from
        D.allPCells_fibre false j i,D.pCells_card]; omega)
    obtain ⟨u,hu⟩ := hn
    obtain ⟨hOut,hi⟩ := mem_filter.mp hu
    refine ⟨⟨u,mem_union_right _ hOut⟩,?_⟩
    rw [hSend u hOut,hi]
  · intro i
    let pred := (A.factor j).symm (source i)
    have ha : pred ∈ outgoing := (D.mem_allPCells_iff _ _ _).mpr (hDir i).1
    have hb : target i ∈ incoming := (D.mem_allPCells_iff _ _ _).mpr (hDir i).2
    let e : ↥(ordinaryᶜ : Finset V) := ⟨center i,mem_compl.mpr (hOutside i)⟩
    refine ⟨e,⟨pred,mem_union_right _ ha⟩,⟨target i,mem_union_left _ hb⟩,?_,?_,?_,?_⟩
    · rw [hSend pred ha,←(hTag i).1]
      apply (hOrbit _ _).mp
      rw [show source i = A.factor j pred from ((A.factor j).apply_symm_apply _).symm]
      exact (Equiv.Perm.SameCycle.refl _ _).apply_right
    · rw [hReceive (target i) hb]
      change (σ j.1).SameCycle (target i).1.1 (C i)
      rw [(hTag i).2]
    · intro x hx
      rw [hSend pred ha]
      apply (coord_mem_physical_cell_iff ordinary cell coord hMap pred x).mp
      have h := hMem _ _ hx
      rw [hExc] at h
      exact hIn i (coord x) h
    · intro x hx
      rw [hReceive (target i) hb]
      apply (coord_mem_physical_cell_iff ordinary cell coord hMap (target i) x).mp
      have h := hMem _ _ hx
      rw [hExc] at h
      exact hOut i (coord x) h

end OverfullWork.DirectedRobustExpansion
