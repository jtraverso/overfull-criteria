module

public import OverfullWork.OsthusStadenCoreExceptionOnLayers
public import OverfullWork.OsthusStadenPhysicalBridgeAssembly

@[expose] public section


/-! Add the exact core arcs without changing the bridge incidences or
the ordinary successor pairs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

private theorem degrees_eq_of_incidence_iff {V : Type*} [Fintype V]
    (D H : Digraph V) (x : V)
    (hin : ∀ y, D.Adj y x ↔ H.Adj y x) (hout : ∀ y, D.Adj x y ↔ H.Adj x y) :
    inDegree D x = inDegree H x ∧ outDegree D x = outDegree H x := by
  have hI : inProfile D x = inProfile H x := by
    ext y
    simpa only [inProfile,mem_filter,mem_univ,true_and] using hin y
  have hO : outProfile D x = outProfile H x := by
    ext y
    simpa only [outProfile,mem_filter,mem_univ,true_and] using hout y
  exact ⟨congrArg Finset.card hI,congrArg Finset.card hO⟩

/-- Adding core arcs to the bridged layers preserves their disjointness,
all previous non-core exceptional degrees, and the old ordinary pairs. -/
theorem adjoin_exact_core_exception_arcs {V L : Type*} [Fintype V]
    (G : Digraph V) (Z : Finset V) (ordinary : L → Finset V)
    (bridgeLayer core : L → Digraph V) (κ : ℕ)
    (hBridge : ∀ j, bridgeLayer j ≤ G) (hCore : ∀ j, core j ≤ G)
    (hDisBridge : ∀ j k, j ≠ k → Disjoint (bridgeLayer j) (bridgeLayer k))
    (hDisCore : ∀ j k, j ≠ k → Disjoint (core j) (core k))
    (hZ : ∀ j, Disjoint Z (ordinary j))
    (hAvoid : ∀ j x y, (bridgeLayer j).Adj x y → x ∉ Z ∧ y ∉ Z)
    (hSupport : ∀ j x y, (core j).Adj x y →
      (x ∈ Z ∧ y ∈ ordinary j) ∨ (y ∈ Z ∧ x ∈ ordinary j))
    (hInd : ∀ j x y, x ∉ ordinary j → y ∉ ordinary j → ¬ (bridgeLayer j).Adj x y)
    (hExact : ∀ j x, x ∈ Z → inDegree (core j) x = κ ∧ outDegree (core j) x = κ) :
    let G' := fun j => bridgeLayer j ⊔ core j
    (∀ j, G' j ≤ G) ∧ (∀ j k, j ≠ k → Disjoint (G' j) (G' k)) ∧
    (∀ j x, x ∈ Z → inDegree (G' j) x = κ ∧ outDegree (G' j) x = κ) ∧
    (∀ j x, x ∉ Z → x ∉ ordinary j →
      inDegree (G' j) x = inDegree (bridgeLayer j) x ∧
        outDegree (G' j) x = outDegree (bridgeLayer j) x) ∧
    (∀ j, ∀ x ∈ ordinary j, ∀ y ∈ ordinary j, (G' j).Adj x y ↔ (bridgeLayer j).Adj x y) ∧
    ∀ j x y, x ∉ ordinary j → y ∉ ordinary j → ¬ (G' j).Adj x y := by
  let G' (j : L) := bridgeLayer j ⊔ core j
  have hBoth (j : L) (x y : V) (hx : x ∉ Z) (hy : y ∉ Z) : ¬ (core j).Adj x y := by
    intro h
    rcases hSupport j x y h with h | h
    · exact hx h.1
    · exact hy h.1
  refine ⟨fun j => sup_le (hBridge j) (hCore j),?_,?_,?_,?_,?_⟩
  · intro j k hne
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hj,hk⟩
    rcases hj with h | h <;> rcases hk with h' | h'
    · exact disjoint_iff_inf_le.mp (hDisBridge j k hne) ⟨h,h'⟩
    · exact hBoth k x y (hAvoid j x y h).1 (hAvoid j x y h).2 h'
    · exact hBoth j x y (hAvoid k x y h').1 (hAvoid k x y h').2 h
    · exact disjoint_iff_inf_le.mp (hDisCore j k hne) ⟨h,h'⟩
  · intro j x hx
    have h := degrees_eq_of_incidence_iff (G' j) (core j) x
      (fun y => ⟨fun h => h.elim (fun b => ((hAvoid j y x b).2 hx).elim) id,Or.inr⟩)
      (fun y => ⟨fun h => h.elim (fun b => ((hAvoid j x y b).1 hx).elim) id,Or.inr⟩)
    exact ⟨h.1.trans (hExact j x hx).1,h.2.trans (hExact j x hx).2⟩
  · intro j x hx hxOrd
    apply degrees_eq_of_incidence_iff (G' j) (bridgeLayer j) x
    · refine fun y => ⟨?_,Or.inl⟩
      rintro (h | h)
      · exact h
      · rcases hSupport j y x h with h | h
        · exact (hxOrd h.2).elim
        · exact (hx h.1).elim
    · refine fun y => ⟨?_,Or.inl⟩
      rintro (h | h)
      · exact h
      · rcases hSupport j x y h with h | h
        · exact (hx h.1).elim
        · exact (hxOrd h.2).elim
  · intro j x hx y hy
    refine ⟨?_,Or.inl⟩
    rintro (h | h)
    · exact h
    · rcases hSupport j x y h with h | h
      · exact (disjoint_left.mp (hZ j) h.1 hx).elim
      · exact (disjoint_left.mp (hZ j) h.1 hy).elim
  · intro j x y hx hy h
    rcases h with h | h
    · exact hInd j x y hx hy h
    · rcases hSupport j x y h with h | h
      · exact hy h.2
      · exact hx h.2

/-- A clipped red half lies in the ordinary part after the same
one-vertex deletion has been performed in its p-cell. -/
theorem clipped_primary_half_mem_ordinary
    {V I J : Type*} [Fintype V] [Fintype I]
    {profiles : J → Finset V} {f : V → Option I} {s p m : ℕ} [NeZero s] [NeZero p]
    {ε₁ ε₂ ε₃ : ℝ}
    (R : ∀ i, PrimaryNestedRefinement profiles (cluster f i) s p m ε₁ ε₂ ε₃)
    (erase : RefinedVertex I s p → V) (a : RefinedVertex I s p) (half : Bool) :
    (primaryHalfCell R a half).erase (erase a) ⊆
      univ.biUnion (fun b => (primaryPCells R b).erase (erase b)) := by
  intro x hx
  obtain ⟨hne,hMem⟩ := mem_erase.mp hx
  exact mem_biUnion.mpr ⟨a,mem_univ _,mem_erase.mpr ⟨hne,primaryHalfCell_subset R a half hMem⟩⟩

/-- A bridged layer uses only vertices in its original ordinary cells.
In particular it is disjoint from the core arcs when those cells
avoid the core exceptional set. -/
theorem addTrimmedBridgeStars_avoids_core
    {V U I : Type*} [Fintype U] [Fintype I]
    (D : Digraph V) (cell : U → Finset V) (erase : U → V)
    (center : I → V) (incoming outgoing : I → Finset V) (Z : Finset V)
    (hCell : ∀ u, Disjoint (cell u) Z) (hCenter : ∀ i, center i ∉ Z)
    (hIn : ∀ i, incoming i ⊆ univ.biUnion cell) (hOut : ∀ i, outgoing i ⊆ univ.biUnion cell) :
    ∀ x y, (addTrimmedBridgeStars D cell erase center incoming outgoing).Adj x y →
      x ∉ Z ∧ y ∉ Z := by
  have hOrd (x : V) (hx : x ∈ univ.biUnion cell) : x ∉ Z := by
    obtain ⟨u,_,hu⟩ := mem_biUnion.mp hx
    exact fun h => disjoint_left.mp (hCell u) hu h
  have hTrim (x : V) (hx : x ∈ univ.biUnion (fun u => (cell u).erase (erase u))) : x ∉ Z := by
    obtain ⟨u,_,hu⟩ := mem_biUnion.mp hx
    exact fun h => disjoint_left.mp (hCell u) (mem_erase.mp hu).2 h
  rintro x y (⟨_,hx,hy⟩ | ⟨i,_,⟨hx,rfl⟩ | ⟨rfl,hy⟩⟩)
  · exact ⟨hTrim x hx,hTrim y hy⟩
  · exact ⟨hOrd x (hIn i hx),hCenter i⟩
  · exact ⟨hCenter i,hOrd y (hOut i hy)⟩

end OverfullWork.DirectedRobustExpansion
