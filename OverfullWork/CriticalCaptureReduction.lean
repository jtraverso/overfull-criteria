module

public import OverfullWork.FournierCoreCriterion

@[expose] public section


/-! # Exact reductions that capture every critical obstruction

A reduction need only contain a copy of each maximum-degree critical
obstruction. The target can have a different vertex type. All colourings
retain the original graph's palette size; no extension of a prescribed
colouring is asserted.
-/
namespace OverfullWork.CriticalCapture
open SimpleGraph
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- An embedded reduction capturing all critical copies preserves the
existence of a colouring with the original maximum-degree palette. -/
theorem colourable_iff_of_copy_critical_capture
    {W : Type v} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {P : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel P.Adj]
    (f : Copy P G)
    (hcapture : ∀ w : FournierCore.CriticalCopy G, Nonempty (Copy w.graph P)) :
    G.EdgeColorable G.maxDegree ↔ P.EdgeColorable G.maxDegree := by
  refine ⟨Critical.colourable_of_copy f,fun hc => ?_⟩
  by_contra hnc
  obtain ⟨w⟩ := FournierCore.exists_criticalCopy G hnc
  obtain ⟨g⟩ := hcapture w
  have hH := Critical.colourable_of_copy g hc
  apply w.critical.2.1
  rwa [w.maxDegree_eq]

/-- Spanning restrictions are a special case of exact critical capture. -/
theorem colourable_iff_of_critical_capture
    {G P : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel P.Adj]
    (hle : P≤G)
    (hcapture : ∀ w : FournierCore.CriticalCopy G, Nonempty (Copy w.graph P)) :
    G.EdgeColorable G.maxDegree ↔ P.EdgeColorable G.maxDegree :=
  colourable_iff_of_copy_critical_capture (Copy.ofLE P G hle) hcapture

/-- A maximum-degree-preserving reduction transports its overfull
criterion to the original graph. Only the easy direction of overfull
transport through a copy is needed. -/
theorem overfull_criterion_of_copy_critical_capture
    {W : Type v} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {P : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel P.Adj]
    (f : Copy P G) (hmax : P.maxDegree=G.maxDegree)
    (hcapture : ∀ w : FournierCore.CriticalCopy G, Nonempty (Copy w.graph P))
    (hcriterion : P.EdgeColorable P.maxDegree ↔ ¬P.HasOverfullSubgraph) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph := by
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  have hnoP := Critical.no_overfull_of_copy f hmax hno
  have hc := hcriterion.mpr hnoP
  apply (colourable_iff_of_copy_critical_capture f hcapture).mpr
  simpa only [hmax] using hc

theorem overfull_criterion_of_critical_capture
    {G P : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel P.Adj]
    (hle : P≤G) (hmax : P.maxDegree=G.maxDegree)
    (hcapture : ∀ w : FournierCore.CriticalCopy G, Nonempty (Copy w.graph P))
    (hcriterion : P.EdgeColorable P.maxDegree ↔ ¬P.HasOverfullSubgraph) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph :=
  overfull_criterion_of_copy_critical_capture (Copy.ofLE P G hle) hmax hcapture hcriterion

/-- Maximum-degree equality need not be assumed for a spanning captured
reduction. If an obstruction exists, Vizing forces equality automatically. -/
theorem overfull_criterion_of_captured_restriction
    {G P : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel P.Adj]
    (hle : P≤G)
    (hcapture : ∀ w : FournierCore.CriticalCopy G, Nonempty (Copy w.graph P))
    (hcriterion : P.EdgeColorable P.maxDegree ↔ ¬P.HasOverfullSubgraph) :
    G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph := by
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  by_contra hnc
  have hncP : ¬P.EdgeColorable G.maxDegree :=
    fun hc => hnc ((colourable_iff_of_critical_capture hle hcapture).mpr hc)
  have hmax := Critical.maxDegree_eq_of_obstruction hle hncP
  exact hnc ((overfull_criterion_of_critical_capture hle hmax hcapture hcriterion).mpr hno)

end OverfullWork.CriticalCapture
