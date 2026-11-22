module

public import OverfullWork.OsthusStadenPhysicalRedLayerCompletion

@[expose] public section


/-! Red4–Red6 for the endpoints actually used by the three exceptional families. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

/-- The ordinary endpoints of red arcs in the given direction.
The true direction receives red arcs, and the false direction sends them. -/
noncomputable def ordinaryRedEndpoints {V : Type*} [Fintype V]
    (F : Digraph V) (ordinary : Finset V) (q : Bool) : Finset V :=
  ordinary.filter (fun x => ∃ y, y ∉ ordinary ∧ if q then F.Adj y x else F.Adj x y)

theorem OsthusStadenRedLayerProperties.ordinaryRedEndpoints_subset
    {L U I V : Type*} [Fintype V] {G reserve : Digraph V} {initial F : L → Digraph V}
    {factor : L → Equiv.Perm U} {ordinary : L → Finset V} {cell : L → U → Finset V}
    {red : Bool → L → Finset V} {center : L → I → V} {incoming outgoing : L → I → Finset V}
    {κ : ℕ} {cap δ d : ℝ}
    (P : OsthusStadenRedLayerProperties G reserve initial F factor ordinary cell red center incoming outgoing κ cap δ d)
    (j : L) (q : Bool) : ordinaryRedEndpoints (F j) (ordinary j) q ⊆ red q j := by
  intro x hx
  obtain ⟨hxOrd,y,hy,hxy⟩ := mem_filter.mp hx
  cases q
  · rcases P.arc_support j x y hxy with h | h | h
    · exact (hy h.2).elim
    · exact (h.1 hxOrd).elim
    · exact h.2.2
  · rcases P.arc_support j y x hxy with h | h | h
    · exact (hy h.1).elim
    · exact h.2.2
    · exact (h.1 hxOrd).elim

/-- The actual exceptional arcs use at most the prescribed half-cell,
are separated along a factor cycle, and never use a single cell in both directions. -/
theorem red_geometry_of_exceptional_endpoints
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero (2*s)] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ ε d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    {A : UnwoundPrimarySlices G thin E g σ τ ε d R}
    (D : PrimaryRedSelection (p := p) A.coordinates) (hp : 1 < p)
    (j : RefinedFactorIndex r (2*s) p) (F : Digraph V) (ordinary : Finset V)
    (hRed : ∀ q, ordinaryRedEndpoints F ordinary q ⊆ D.vertices q j) :
    let used := ordinaryRedEndpoints F ordinary
    let cell := primaryPCells (R j.1)
    (∀ u, ((used true ∪ used false) ∩ cell u).card ≤ m) ∧
    (∀ q q' u v, (used q ∩ cell u).Nonempty → (used q' ∩ cell v).Nonempty →
      ∀ k, 0 < k → ((A.factor j)^k) u = v → p ≤ k) ∧
    ∀ u, ¬ ((used true ∩ cell u).Nonempty ∧ (used false ∩ cell u).Nonempty) := by
  intro used cell
  have hSub (q : Bool) (u : RefinedVertex I (2*s) p) :
      used q ∩ cell u ⊆ D.vertices q j ∩ cell u :=
    inter_subset_inter (hRed q) (Subset.rfl)
  refine ⟨?_,?_,?_⟩
  · intro u
    have h : (used true ∪ used false) ∩ cell u ⊆
        (D.vertices true j ∪ D.vertices false j) ∩ cell u :=
      inter_subset_inter (union_subset_union (hRed true) (hRed false)) (Subset.rfl)
    exact (card_le_card h).trans (D.red4_on_vertices j u)
  · intro q q' u v hu hv k hk hPath
    obtain ⟨x,hx⟩ := hu
    obtain ⟨y,hy⟩ := hv
    have hx' := mem_inter.mp (hSub q u hx)
    have hy' := mem_inter.mp (hSub q' v hy)
    exact D.distance hp (D.mem_half_of_mem_vertices_and_pCell q j u x hx'.1 hx'.2).1
      (D.mem_half_of_mem_vertices_and_pCell q' j v y hy'.1 hy'.2).1 hk hPath
  · intro u h
    exact D.red6_on_vertices j u ⟨h.1.mono (hSub true u),h.2.mono (hSub false u)⟩

end OverfullWork.DirectedRobustExpansion
