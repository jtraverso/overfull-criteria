module

public import OverfullWork.OsthusStadenSuccessorCoordinates

@[expose] public section


/-! Read the balanced red arc set in the same coordinates as H3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

/-- On the physical slice coordinates, the cell label is the
coordinate's first ordinary component and is absent on the exceptional subtype. -/
theorem physical_label_eq_sliceLabel {U V : Type*} [Fintype V] {n : ℕ}
    (ordinary : Finset V) (cell : U → Finset V) (label : V → Option U)
    (coord : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n) ≃ V)
    (hExc : ∀ x, coord (.inl x) = x.val)
    (hMap : ∀ u, (univ : Finset (Fin n)).map (sliceCellEmbedding coord u) = cell u)
    (hCell : ∀ u, cell u ⊆ ordinary)
    (hLabel : ∀ u x, label x = some u ↔ x ∈ cell u)
    (x : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n)) :
    label (coord x) = sliceLabel x := by
  rcases x with e | ⟨u,w⟩
  · rw [hExc,sliceLabel]
    cases he : label e.val with
    | none => rfl
    | some u => exact ((mem_compl.mp e.property) (hCell u ((hLabel u _).mp he))).elim
  · apply (hLabel u _).mpr
    rw [←hMap u]
    exact mem_map.mpr ⟨w,mem_univ _,rfl⟩

/-- Pull back the indicator, the row and column degrees, and the labelled
arc masses using a single equivalence of the vertices. -/
theorem transport_balanced_arc_data
    {X V U : Type*} [Fintype X] [Fintype V]
    (coord : X ≃ V) (labelX : X → Option U) (labelV : V → Option U)
    (hLabel : ∀ x, labelV (coord x) = labelX x) (A : Finset (V × V)) :
    let pulled := A.map (Equiv.prodCongr coord.symm coord.symm).toEmbedding
    (∀ x y, ((x,y) ∈ pulled ↔ (coord x,coord y) ∈ A)) ∧
    (∀ x, inDegree (digraphOfArcs pulled) x = inDegree (digraphOfArcs A) (coord x) ∧
      outDegree (digraphOfArcs pulled) x = outDegree (digraphOfArcs A) (coord x)) ∧
    ∀ q u, clusterArcMass labelX pulled q u = clusterArcMass labelV A q u := by
  intro pulled
  let e := (Equiv.prodCongr coord.symm coord.symm).toEmbedding
  have he (p : V × V) : e p = (coord.symm p.1,coord.symm p.2) := rfl
  have hm (x y : X) : (x,y) ∈ pulled ↔ (coord x,coord y) ∈ A := by
    constructor
    · intro h
      obtain ⟨⟨v,w⟩,hw,hh⟩ := mem_map.mp h
      have h₁ : coord.symm v = x := congrArg Prod.fst hh
      have h₂ : coord.symm w = y := congrArg Prod.snd hh
      rw [←h₁,←h₂,coord.apply_symm_apply,coord.apply_symm_apply]
      exact hw
    · intro h
      exact mem_map.mpr ⟨(coord x,coord y),h,by simp [he]⟩
  refine ⟨hm,?_,?_⟩
  · intro x
    rw [digraphOfArcs_inDegree,digraphOfArcs_inDegree,digraphOfArcs_outDegree,digraphOfArcs_outDegree]
    constructor
    · change ((A.map e).filter (fun t => t.2 = x)).card = _
      rw [filter_map,card_map]
      congr 1
      ext t
      simp only [mem_filter,he]
      exact and_congr_right (fun _ => coord.symm_apply_eq)
    · change ((A.map e).filter (fun t => t.1 = x)).card = _
      rw [filter_map,card_map]
      congr 1
      ext t
      simp only [mem_filter,he]
      exact and_congr_right (fun _ => coord.symm_apply_eq)
  · intro q u
    unfold clusterArcMass
    change ((A.map e).filter _).card = _
    rw [filter_map,card_map]
    congr 1
    ext t
    cases q <;> simp only [mem_filter,Function.comp_apply,he,Bool.false_eq_true,if_false,if_true] <;>
      rw [←hLabel,coord.apply_symm_apply]

/-- All red-arc hypotheses of the dense successor completion transfer
to the same coordinates used to split off H3. -/
theorem balanced_red_data_in_successor_coordinates
    {U V : Type*} [Fintype U] [Fintype V] {n : ℕ}
    (ordinary : Finset V) (cell : U → Finset V) (label : V → Option U)
    (coord : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n) ≃ V)
    (hExc : ∀ x, coord (.inl x) = x.val)
    (hMap : ∀ u, (univ : Finset (Fin n)).map (sliceCellEmbedding coord u) = cell u)
    (hCell : ∀ u, cell u ⊆ ordinary)
    (hLabel : ∀ u x, label x = some u ↔ x ∈ cell u)
    (factor : Equiv.Perm U) (D : Digraph V) (R : U → Digraph (Fin n))
    (A : Finset (V × V)) (κ L : ℕ)
    (hR : ∀ u, R u ≤ pullDirectedPair (sliceCellEmbedding coord u) (sliceCellEmbedding coord (factor u)) D)
    (hDis : Disjoint D (digraphOfArcs A))
    (hBalance : ∀ u, clusterArcMass label A true u = clusterArcMass label A false (factor u))
    (hExact : ∀ x, x ∉ ordinary → inDegree (digraphOfArcs A) x = κ ∧ outDegree (digraphOfArcs A) x = κ)
    (hCap : ∀ x ∈ ordinary, inDegree (digraphOfArcs A) x ≤ κ-L ∧ outDegree (digraphOfArcs A) x ≤ κ-L) :
    let B := A.map (Equiv.prodCongr coord.symm coord.symm).toEmbedding
    (∀ u, clusterArcMass sliceLabel B true u = clusterArcMass sliceLabel B false (factor u)) ∧
    (∀ e : ↥(ordinaryᶜ : Finset V),
      inDegree (digraphOfArcs B) (.inl e) = κ ∧ outDegree (digraphOfArcs B) (.inl e) = κ) ∧
    (∀ u w, inDegree (digraphOfArcs B) (.inr (u,w)) ≤ κ-L ∧ outDegree (digraphOfArcs B) (.inr (u,w)) ≤ κ-L) ∧
    ∀ u x y, (R u).Adj x y → (Sum.inr (u,x),Sum.inr (factor u,y)) ∉ B := by
  intro B
  obtain ⟨hMem,hDegrees,hMass⟩ := transport_balanced_arc_data coord sliceLabel label
    (physical_label_eq_sliceLabel ordinary cell label coord hExc hMap hCell hLabel) A
  refine ⟨fun u => (hMass true u).trans ((hBalance u).trans (hMass false (factor u)).symm),?_,?_,?_⟩
  · intro x
    have h := hExact x (mem_compl.mp x.property)
    have he := hDegrees (.inl x)
    rw [hExc] at he
    exact ⟨he.1.trans h.1,he.2.trans h.2⟩
  · intro u w
    have hu : coord (.inr (u,w)) ∈ cell u := by
      rw [←hMap u]
      exact mem_map.mpr ⟨w,mem_univ _,rfl⟩
    have h := hCap _ (hCell u hu)
    have h' := hDegrees (.inr (u,w))
    exact ⟨h'.1.trans_le h.1,h'.2.trans_le h.2⟩
  · intro u x y h h'
    exact disjoint_iff_inf_le.mp hDis ⟨hR u h,(hMem _ _).mp h'⟩

end OverfullWork.DirectedRobustExpansion
