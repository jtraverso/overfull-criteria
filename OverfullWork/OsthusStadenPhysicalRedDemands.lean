module

public import OverfullWork.OsthusStadenPhysicalRedGeometry
public import OverfullWork.OsthusStadenShadowFromPrimaryLayers

@[expose] public section


/-! Count the physical demands of the red layers before choosing the shadow arcs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical

/-- Equation (31), counted using the ordinary vertices of the physical
p-cell and the exceptional complement of the whole layer. -/
noncomputable def cellExceptionalArcCount {V : Type*} [Fintype V]
    (F : Digraph V) (ordinary cell : Finset V) (outgoing : Bool) : ℕ :=
  ∑ x ∈ cell, (ordinaryᶜ ∩ (if outgoing then outProfile F x else inProfile F x)).card

/-- Double-count the ordinary-exceptional arcs in one direction. With
Red1 and Red2, both totals are the same exceptional size times κ. -/
theorem sum_cell_exceptional_arc_counts
    {V U : Type*} [Fintype V] [Fintype U] (F : Digraph V) (ordinary : Finset V)
    (cell : U → Finset V) (κ : ℕ) (q : Bool)
    (hPartition : univ.biUnion cell = ordinary)
    (hDis : ∀ u v, u ≠ v → Disjoint (cell u) (cell v))
    (hInd : ∀ x y, x ∉ ordinary → y ∉ ordinary → ¬ F.Adj x y)
    (hExact : ∀ x, x ∉ ordinary → inDegree F x = κ ∧ outDegree F x = κ) :
    (∑ u,cellExceptionalArcCount F ordinary (cell u) q) = (ordinaryᶜ : Finset V).card*κ := by
  let adj (x y : V) := if q then F.Adj x y else F.Adj y x
  have hFrom (x : V) :
      ordinaryᶜ ∩ (if q then outProfile F x else inProfile F x) = ordinaryᶜ.filter (adj x) := by
    ext y
    cases q <;> simp [adj,outProfile,inProfile]
  have hTo (y : V) (hy : y ∈ (ordinaryᶜ : Finset V)) :
      (ordinary.filter (fun x => adj x y)).card = κ := by
    have hAdj (x : V) (h : adj x y) : x ∈ ordinary := by
      by_contra hn
      cases q
      · exact hInd y x (mem_compl.mp hy) hn h
      · exact hInd x y hn (mem_compl.mp hy) h
    have he : ordinary.filter (fun x => adj x y) = univ.filter (fun x => adj x y) := by
      ext x
      simp only [mem_filter,mem_univ,true_and]
      exact ⟨And.right,fun h => ⟨hAdj x h,h⟩⟩
    rw [he]
    cases q
    · exact (hExact y (mem_compl.mp hy)).2
    · exact (hExact y (mem_compl.mp hy)).1
  unfold cellExceptionalArcCount
  simp only [hFrom]
  rw [←sum_biUnion (fun u _ v _ h => hDis u v h),hPartition]
  simp only [card_filter]
  rw [sum_comm]
  calc
    (∑ y ∈ (ordinaryᶜ : Finset V), ∑ x ∈ ordinary, if adj x y then 1 else 0) =
        ∑ y ∈ (ordinaryᶜ : Finset V), κ := by
      apply sum_congr rfl
      intro y hy
      rw [←card_filter]
      exact hTo y hy
    _ = _ := by simp

/-- The bound in Red3 gives the total demand of an individual cell. -/
theorem cell_exceptional_arc_count_le {V : Type*} [Fintype V] (F : Digraph V)
    (ordinary cell : Finset V) (q : Bool) (cap : ℝ)
    (hCap : ∀ x ∈ cell, profileCount ordinaryᶜ (if q then outProfile F x else inProfile F x) ≤ cap) :
    (cellExceptionalArcCount F ordinary cell q:ℝ) ≤ (cell.card:ℝ)*cap := by
  unfold cellExceptionalArcCount
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _ ∈ cell,cap := sum_le_sum hCap
    _ = _ := by simp

/-- A p-cell without a red endpoint in this direction has zero demand. -/
theorem cell_exceptional_arc_count_of_no_red_endpoints {V : Type*} [Fintype V] (F : Digraph V)
    (ordinary cell : Finset V) (q : Bool)
    (hCell : cell ⊆ ordinary) (hDis : Disjoint cell (ordinaryRedEndpoints F ordinary (!q))) :
    cellExceptionalArcCount F ordinary cell q = 0 := by
  apply sum_eq_zero
  intro x hx
  apply card_eq_zero.mpr
  refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  obtain ⟨hyOrd,hy⟩ := mem_inter.mp hy
  apply disjoint_left.mp hDis hx
  refine mem_filter.mpr ⟨hCell hx,y,mem_compl.mp hyOrd,?_⟩
  cases q
  · exact (mem_filter.mp hy).2
  · exact (mem_filter.mp hy).2

set_option maxHeartbeats 700000 in
/-- Equations (31)–(32) on the cells and the shadow vertex set of
the actual trimmed layer. The two red directions have the same total
demand, and the bound from Red3 applies to every physical p-cell. -/
theorem physical_red_demands_on_unwound_layer
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero (2*s)] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ ε d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    {A : UnwoundPrimarySlices G thin E g σ τ ε d R}
    (D : PrimaryRedSelection (p := p) A.coordinates)
    (j : RefinedFactorIndex r (2*s) p) (F : Digraph V) (κ : ℕ) (cap : ℝ)
    (erase : RefinedVertex I (2*s) p → V)
    (hErase : ∀ u, erase u ∈ primaryPCells (R j.1) u) :
    let cell := fun u => (primaryPCells (R j.1) u).erase (erase u)
    let ordinary := univ.biUnion cell
    let demand := fun q u => cellExceptionalArcCount F ordinary (cell u) q
    let T := ↥(@Union.union _ (@Finset.instUnion _ (Classical.decEq _))
      (D.allPCells true j) (D.allPCells false j))
    (∀ x y, x ∉ ordinary → y ∉ ordinary → ¬ F.Adj x y) →
    (∀ x, x ∉ ordinary → inDegree F x = κ ∧ outDegree F x = κ) →
    (∀ q, ordinaryRedEndpoints F ordinary q ⊆ D.vertices q j) →
    (∀ x ∈ ordinary, ∀ q : Bool, profileCount ordinaryᶜ (if q then outProfile F x else inProfile F x) ≤ cap) →
    (∀ q u, u ∉ D.allPCells (!q) j → demand q u = 0) ∧
    (∀ q u, (demand q u:ℝ) ≤ ((2*m-1:ℕ):ℝ)*cap) ∧
    (∀ q, (∑ v : T,demand q v) = (ordinaryᶜ : Finset V).card*κ) := by
  letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
  intro cell ordinary demand T hInd hExact hDir hCap
  have hCell (u : RefinedVertex I (2*s) p) : cell u ⊆ ordinary := by
    intro x hx
    exact mem_biUnion.mpr ⟨u,mem_univ _,hx⟩
  have hZero (q : Bool) (u : RefinedVertex I (2*s) p) (hu : u ∉ D.allPCells (!q) j) : demand q u = 0 := by
    apply cell_exceptional_arc_count_of_no_red_endpoints F ordinary (cell u) q (hCell u)
    apply disjoint_left.mpr
    intro x hx hRed
    have hh := (D.mem_half_of_mem_vertices_and_pCell (!q) j u x (hDir _ hRed) (mem_erase.mp hx).2).1
    exact hu ((D.mem_allPCells_iff _ _ _).mpr hh)
  have hDis (u v : RefinedVertex I (2*s) p) (hne : u ≠ v) : Disjoint (cell u) (cell v) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hne (Option.some.inj (((A.label_cell j.1 x u).mpr (mem_erase.mp hx).2).symm.trans
      ((A.label_cell j.1 x v).mpr (mem_erase.mp hy).2)))
  refine ⟨hZero,?_,?_⟩
  · intro q u
    have h := cell_exceptional_arc_count_le F ordinary (cell u) q cap (fun x hx => by
      cases q
      · simpa only [Bool.false_eq_true,if_false] using hCap x (hCell u hx) false
      · simpa only [if_true] using hCap x (hCell u hx) true)
    have hSize : (cell u).card = 2*m-1 := (card_erase_of_mem (hErase u)).trans
      (congrArg (·-1) (A.size_cells j.1 u))
    rwa [hSize] at h
  · intro q
    let red := D.allPCells true j ∪ D.allPCells false j
    have hRestrict : (∑ u ∈ red,demand q u) = ∑ u,demand q u :=
      sum_subset (subset_univ _) (fun u _ hu => hZero q u (fun h => hu (by
        cases q
        · exact mem_union_left _ h
        · exact mem_union_right _ h)))
    rw [←sum_subtype red (fun _ => Iff.rfl) (demand q),hRestrict]
    exact sum_cell_exceptional_arc_counts F ordinary cell κ q rfl hDis hInd hExact

end OverfullWork.DirectedRobustExpansion
