module

public import OverfullWork.CombinedCoreSupport
public import OverfullWork.FournierCoreCriterion

@[expose] public section


/-! # Exact reduction to the induced critical support

The reverse implication is an obstruction argument. It does not assert
that an arbitrary prescribed colouring extends from the support.
-/
namespace OverfullWork.DeficitCore
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- Any vertex set capturing every extracted critical copy gives an exact
reduction of existence of a Δ-edge-colouring to its induced subgraph. -/
theorem colourable_iff_induce_of_critical_capture (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V)
    (hcapture : ∀ w : FournierCore.CriticalCopy G, ∀ x, w.embedding x ∈ S) :
    G.EdgeColorable G.maxDegree ↔ (G.induce (S : Set V)).EdgeColorable G.maxDegree := by
  constructor
  · exact Critical.colourable_of_copy (Copy.induce G (S : Set V))
  · intro hc
    by_contra hnc
    obtain ⟨w⟩ := FournierCore.exists_criticalCopy G hnc
    let fhom : w.graph →g G.induce (S : Set V) :=
      { toFun := fun x => ⟨w.embedding x, hcapture w x⟩
        map_rel' := fun hxy => w.embedding.toHom.map_adj hxy }
    have hinj : Function.Injective fhom := by
      intro x y he
      exact w.embedding.injective (congrArg Subtype.val he)
    have hH := Critical.colourable_of_copy (fhom.toCopy hinj) hc
    apply w.critical.2.1
    rwa [w.maxDegree_eq]

/-- Existence of a proper Δ-edge-colouring reduces exactly to the combined
core's candidate support, with the original palette size retained. -/
theorem colourable_iff_support_induce (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.EdgeColorable G.maxDegree ↔
      (G.induce (candidateSupport G : Set V)).EdgeColorable G.maxDegree := by
  apply colourable_iff_induce_of_critical_capture
  intro w x
  exact critical_vertex_mem_candidateSupport w.embedding w.maxDegree_eq w.critical w.no_isolates x

/-- A nonempty core supplies a maximum-degree vertex whose entire
neighbourhood remains in the support. Thus the original Δ is preserved. -/
theorem maxDegree_support_induce_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcore : (core G).Nonempty) :
    (G.induce (candidateSupport G : Set V)).maxDegree = G.maxDegree := by
  classical
  obtain ⟨x, hx⟩ := hcore
  let v : (candidateSupport G : Set V) := ⟨x, core_subset_candidateSupport G hx⟩
  have hd : (G.induce (candidateSupport G : Set V)).degree v = G.degree x := by
    rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
    apply Fintype.card_congr
    refine
      { toFun := fun y => ⟨y.val.val, y.property⟩
        invFun := fun y => ⟨⟨y.val, core_neighbours_mem_candidateSupport G hx y.property⟩, y.property⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro y; rfl
    · intro y; rfl

  have hxD : G.degree x = G.maxDegree := ((core_is_admissible G).1 x hx).1
  have hlow := (G.induce (candidateSupport G : Set V)).degree_le_maxDegree v
  have hupp := (Copy.induce G (candidateSupport G : Set V)).maxDegree_mono
  omega

/-- An empty combined core leaves no maximum-degree critical obstruction. -/
theorem edgeColourable_of_core_eq_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (hempty : core G = ∅) : G.EdgeColorable G.maxDegree := by
  by_contra hnc
  obtain ⟨w⟩ := FournierCore.exists_criticalCopy G hnc
  haveI : Nonempty w.vertices := w.critical.1.nonempty
  obtain ⟨x, hx⟩ := w.graph.exists_maximal_degree_vertex
  have hsub := critical_maximum_image_subset_core w.embedding w.maxDegree_eq w.critical w.no_isolates
  have hxM : x ∈ (univ : Finset w.vertices).filter (fun z => w.graph.degree z = w.graph.maxDegree) :=
    mem_filter.mpr ⟨mem_univ x, hx.symm⟩
  have hh := hsub (mem_image.mpr ⟨x, hxM, rfl⟩)
  rw [hempty] at hh
  simpa using hh

end OverfullWork.DeficitCore
