module

public import OverfullWork.KuhnOsthusWrappedPairCoordinates
public import OverfullWork.KuhnOsthusExceptionalPairStability
public import OverfullWork.InducedDigraphSampling

@[expose] public section


/-! Read the same physical cluster partition on the ordinary subtype
used for the chord and parity reserves. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical

/-- A partition of the ordinary vertices determines their cluster
coordinates. Restricting to the ordinary subtype leaves the physical
sets, cardinalities, and lower superregular pairs unchanged. -/
theorem exists_kuhn_osthus_winding_ordinary_coordinates
    {I V : Type*} [Fintype V] (G : Digraph V) (Z : Finset V) (X : I → Finset V)
    (hOrdinary : ∀ i, Disjoint (X i) Z)
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hCover : ∀ x ∉ Z, ∃ i, x ∈ X i) :
    ∃ c : ↥Zᶜ → I,
      let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
      let A (i : I) := (univ : Finset ↥Zᶜ).filter (fun x => c x = i)
      (∀ i x, c x = i ↔ x.val ∈ X i) ∧ (∀ i, (A i).map e = X i) ∧
      (∀ i, (A i).card = (X i).card) ∧
      ∀ i j ε d, IsLowerSuperregularPair G ε d (X i) (X j) →
        IsLowerSuperregularPair (induced G Zᶜ) ε d (A i) (A j) := by
  classical
  let c (x : ↥Zᶜ) := (hCover x.val (mem_compl.mp x.prop)).choose
  let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
  let A (i : I) := (univ : Finset ↥Zᶜ).filter (fun x => c x = i)
  have hCoord (i : I) (x : ↥Zᶜ) : c x = i ↔ x.val ∈ X i := by
    have hx : x.val ∈ X (c x) := (hCover x.val (mem_compl.mp x.prop)).choose_spec
    refine ⟨fun h => h ▸ hx,fun hi => ?_⟩
    by_contra h
    exact disjoint_left.mp (hDisjoint _ _ h) hx hi
  have hMap (i : I) : (A i).map e = X i := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (hCoord _ _).mp (mem_filter.mp hv).2
    · intro hx
      let v : ↥Zᶜ := ⟨x,mem_compl.mpr (fun hz => disjoint_left.mp (hOrdinary i) hx hz)⟩
      exact ⟨v,mem_filter.mpr ⟨mem_univ _,(hCoord i v).mpr hx⟩,rfl⟩
  refine ⟨c,hCoord,hMap,fun i => (card_map e).symm.trans (congrArg card (hMap i)),?_⟩
  intro i j ε d h
  obtain ⟨d',hLow,hHigh,hPair⟩ := h
  change IsLowerSuperregularPair (pullDirectedPair e e G) ε d (A i) (A j)
  refine ⟨d',hLow,hHigh,superregular_pullDirectedPair G e e (A i) (A j) ε d' ?_⟩
  rwa [hMap,hMap]

end OverfullWork.DirectedRobustExpansion
