module

public import OverfullWork.OsthusStadenFactorsFromBalancedLayer

@[expose] public section


/-! Transfer the directional half-cell support to the routing input of §5.11. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- A physical cell corresponds exactly to the ordinary coordinate cell. -/
theorem coord_mem_physical_cell_iff {U V : Type*} [Fintype V] {n : ℕ}
    (ordinary : Finset V) (cell : U → Finset V)
    (coord : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n) ≃ V)
    (hMap : ∀ u, (univ : Finset (Fin n)).map (sliceCellEmbedding coord u) = cell u)
    (u : U) (x : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n)) :
    coord x ∈ cell u ↔ x ∈ sliceCell u := by
  rw [←hMap u]
  unfold sliceCell
  constructor
  · intro h
    obtain ⟨w,_,hw⟩ := mem_map.mp h
    exact mem_map.mpr ⟨w,mem_univ _,coord.injective hw⟩
  · intro hx
    obtain ⟨w,_,rfl⟩ := mem_map.mp hx
    exact mem_map.mpr ⟨w,mem_univ _,rfl⟩

set_option maxHeartbeats 1200000 in
/-- Directional supports, the half-cell bound, and independence of the
exceptional set give the red routing on the exact extraction coordinates. -/
theorem red_arc_routing_of_physical_support
    {U V : Type*} [Fintype U] [Fintype V] {n : ℕ}
    (ordinary : Finset V) (cell half : U → Finset V) (label : V → Option U)
    (coord : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n) ≃ V)
    (hExc : ∀ x, coord (.inl x) = x.val)
    (hMap : ∀ u, (univ : Finset (Fin n)).map (sliceCellEmbedding coord u) = cell u)
    (hCell : ∀ u, cell u ⊆ ordinary) (hLabel : ∀ u x, label x = some u ↔ x ∈ cell u)
    (σ : Equiv.Perm U) (incoming outgoing : Finset U) (A : Finset (V × V))
    (hRanges : Disjoint (Set.range (shadowSend σ incoming outgoing)) (Set.range (shadowReceive σ incoming outgoing)))
    (hHalf : ∀ u, (half u).card < n)
    (hSource : ∀ x y u, (x,y) ∈ A → label x = some u →
      u ∈ Set.range (shadowSend σ incoming outgoing) ∧ x ∈ half u)
    (hTarget : ∀ x y u, (x,y) ∈ A → label y = some u →
      u ∈ Set.range (shadowReceive σ incoming outgoing))
    (hInd : ∀ e ∈ A, e.1 ∈ ordinary ∨ e.2 ∈ ordinary) :
    Nonempty (RedArcRouting σ incoming outgoing (A.map (Equiv.prodCongr coord.symm coord.symm).toEmbedding)) := by
  let A' := A.map (Equiv.prodCongr coord.symm coord.symm).toEmbedding
  have hLab := physical_label_eq_sliceLabel ordinary cell label coord hExc hMap hCell hLabel
  have hMem := (transport_balanced_arc_data coord sliceLabel label hLab A).1
  have hOut (u : U) (x : Fin n) (y : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n))
      (h : (Sum.inr (u,x),y) ∈ A') :
      u ∈ Set.range (shadowSend σ incoming outgoing) ∧ coord (.inr (u,x)) ∈ half u :=
    hSource _ _ u ((hMem _ _).mp h) (hLab (.inr (u,x)))
  have hIn (u : U) (x : Fin n) (y : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n))
      (h : (y,Sum.inr (u,x)) ∈ A') : u ∈ Set.range (shadowReceive σ incoming outgoing) :=
    hTarget _ _ u ((hMem _ _).mp h) (hLab (.inr (u,x)))
  refine ⟨⟨?_,?_,?_,?_,?_⟩⟩
  · intro i hi x hx y h
    obtain ⟨w,_,rfl⟩ := mem_map.mp hx
    exact hi.1 (hOut i w y h).1
  · intro i w y hi h
    exact Set.disjoint_left.mp hRanges hi (hIn i w y h)
  · intro i w y hi h
    exact Set.disjoint_left.mp hRanges (hOut i w y h).1 hi
  · intro e f h
    have h' := hInd _ ((hMem _ _).mp h)
    rw [hExc,hExc] at h'
    exact h'.elim (mem_compl.mp e.property) (mem_compl.mp f.property)
  · intro a
    let i := shadowSend σ incoming outgoing a
    let S := (sliceCell i).filter (fun x => coord x ∈ half i)
    have hSub : S.map coord.toEmbedding ⊆ half i := by
      intro v hv
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
      exact (mem_filter.mp hx).2
    have hSize := (card_map coord.toEmbedding).symm.trans_le (card_le_card hSub)
    refine ⟨S,by rw [Fintype.card_fin]; exact hSize.trans_lt (hHalf i),?_⟩
    intro x hx y hy
    obtain ⟨w,_,rfl⟩ := mem_map.mp hx
    exact mem_filter.mpr ⟨hx,(hOut i w y hy).2⟩

end OverfullWork.DirectedRobustExpansion
