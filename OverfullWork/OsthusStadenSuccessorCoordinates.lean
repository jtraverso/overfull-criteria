module

public import OverfullWork.OsthusStadenBalancedPhysicalGraphs
public import OverfullWork.OsthusStadenPhysicalFactors
public import OverfullWork.KuhnOsthusWrappedPairCoordinates

@[expose] public section


/-! Common coordinates for the ordinary successor pairs in §5.10. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

/-- The embedding of a numbered ordinary cell into the original graph. -/
def sliceCellEmbedding {E U W V : Type*} (coord : SliceVertex E U W ≃ V) (u : U) : W ↪ V :=
  (⟨fun w => Sum.inr (u,w),fun _ _ h => congrArg Prod.snd (Sum.inr.inj h)⟩ :
    W ↪ SliceVertex E U W).trans coord.toEmbedding

/-- Number the vertices of each trimmed cell and keep the physical
exceptional set as its own subtype. The resulting coordinates cover
the original host exactly once. -/
theorem exists_slice_coordinates_of_trimmed_cells
    {U V : Type*} [Fintype U] [Fintype V] (ordinary : Finset V) (cell : U → Finset V) (n : ℕ)
    (hCover : univ.biUnion cell = ordinary)
    (hDis : ∀ u v, u ≠ v → Disjoint (cell u) (cell v))
    (hSize : ∀ u, (cell u).card = n) :
    ∃ coord : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n) ≃ V,
      (∀ x, coord (.inl x) = x.val) ∧
      ∀ u, (univ : Finset (Fin n)).map
        (sliceCellEmbedding coord u) =
          cell u := by
  let e (u : U) : Fin n ≃ ↥(cell u) :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans (hSize u))).symm
  let encode : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n) → V :=
    Sum.elim Subtype.val (fun uw => (e uw.1 uw.2).val)
  have hIn (u : U) (x : V) (hx : x ∈ cell u) : x ∈ ordinary :=
    hCover ▸ mem_biUnion.mpr ⟨u,mem_univ _,hx⟩
  have hInj : Function.Injective encode := by
    intro x y h
    rcases x with x | ⟨u,x⟩ <;> rcases y with y | ⟨v,y⟩
    · exact congrArg Sum.inl (Subtype.ext h)
    · have he : x.val = (e v y).val := h
      exact ((mem_compl.mp x.property) (he.symm ▸ hIn v _ (e v y).property)).elim
    · have he : (e u x).val = y.val := h
      exact ((mem_compl.mp y.property) (he ▸ hIn u _ (e u x).property)).elim
    · have he : (e u x).val = (e v y).val := h
      have hv : u = v := Classical.byContradiction fun hn =>
        disjoint_left.mp (hDis u v hn) (e u x).property (he.symm ▸ (e v y).property)
      subst v
      exact congrArg (fun w => Sum.inr (u,w)) ((e u).injective (Subtype.ext he))
  have hSurj : Function.Surjective encode := by
    intro x
    by_cases hx : x ∈ ordinary
    · rw [←hCover] at hx
      obtain ⟨u,_,hu⟩ := mem_biUnion.mp hx
      obtain ⟨w,hw⟩ := (e u).surjective ⟨x,hu⟩
      exact ⟨.inr (u,w),congrArg Subtype.val hw⟩
    · exact ⟨.inl ⟨x,mem_compl.mpr hx⟩,rfl⟩
  let coord := Equiv.ofBijective encode ⟨hInj,hSurj⟩
  refine ⟨coord,fun _ => rfl,?_⟩
  intro u
  ext x
  constructor
  · intro hx
    obtain ⟨w,_,rfl⟩ := mem_map.mp hx
    exact (e u w).property
  · intro hx
    obtain ⟨w,hw⟩ := (e u).surjective ⟨x,hx⟩
    exact mem_map.mpr ⟨w,mem_univ _,congrArg Subtype.val hw⟩

universe u v

/-- In the same coordinates, split the actual ordinary successor
pairs into H3 and the superregular remainder for the κ-factor. -/
theorem exists_h3_of_physical_successor_pairs
    (fraction ε δ : ℝ) (hp : 0 < fraction) (hp₁ : fraction ≤ 1)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hSmall : ε ≤ δ/4) :
    ∃ N : ℕ, ∀ {U : Type u} [Fintype U] {V : Type v} [Fintype V]
      (D : Digraph V) (factor : Equiv.Perm U) (ordinary : Finset V) (cell : U → Finset V)
      (n : ℕ) (d : ℝ), N ≤ n →
      univ.biUnion cell = ordinary →
      (∀ u v, u ≠ v → Disjoint (cell u) (cell v)) →
      (∀ u, (cell u).card = n) →
      (∀ u, IsSuperregularPair D ε d (cell u) (cell (factor u))) →
      ∃ coord : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n) ≃ V,
        (∀ x, coord (.inl x) = x.val) ∧
        let emb (u : U) : Fin n ↪ V :=
          sliceCellEmbedding coord u
        (∀ u, (univ : Finset (Fin n)).map (emb u) = cell u) ∧
        ∃ H R : U → Digraph (Fin n),
          (∀ u, IsCentredSuperregular (H u) δ (fraction*d)) ∧
          (∀ u, IsCentredSuperregular (R u) δ ((1-fraction)*d)) ∧
          (∀ u, Disjoint (H u) (R u)) ∧
          ∀ u, pullDirectedPair (emb u) (emb (factor u)) D = H u ⊔ R u := by
  obtain ⟨N,hN⟩ := exists_h3_superregular_split.{0} fraction ε δ hp hp₁ hε hδ hδ₁ hSmall
  refine ⟨N,?_⟩
  intro U _ V _ D factor ordinary cell n d hSize hCover hDis hCard hPair
  obtain ⟨coord,hExc,hMap⟩ := exists_slice_coordinates_of_trimmed_cells ordinary cell n hCover hDis hCard
  refine ⟨coord,hExc,hMap,?_⟩
  let emb (u : U) : Fin n ↪ V :=
    sliceCellEmbedding coord u
  let P (u : U) := pullDirectedPair (emb u) (emb (factor u)) D
  have hP (u : U) : IsCentredSuperregular (P u) ε d := by
    have h := superregular_pullDirectedPair D (emb u) (emb (factor u)) univ univ ε d (by
      rw [hMap u,hMap (factor u)]
      exact hPair u)
    refine ⟨⟨h.1,h.2.1⟩,fun x => ?_⟩
    change |((inProfile (P u) x).card:ℝ)-d*(Fintype.card (Fin n):ℝ)| ≤ _ ∧
      |((outProfile (P u) x).card:ℝ)-d*(Fintype.card (Fin n):ℝ)| ≤ _
    exact ⟨by simpa only [profileCount,univ_inter,card_univ,P] using h.2.2.2 x (mem_univ _),
      by simpa only [profileCount,univ_inter,card_univ,P] using h.2.2.1 x (mem_univ _)⟩
  choose H R hH hR hSep hEq using fun u => hN (P u) d (by simpa only [Fintype.card_fin] using hSize) (hP u)
  exact ⟨H,R,hH,hR,hSep,hEq⟩

end OverfullWork.DirectedRobustExpansion
