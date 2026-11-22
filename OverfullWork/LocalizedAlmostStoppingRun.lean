module

public import OverfullWork.AlmostStoppingReductionRun
public import OverfullWork.AlmostOverfullOriginalGeometry

@[expose] public section


/-! # An actual bounded run with a small, sparse original-graph stop

This assembles the constructed run and the independently proved original
almost-overfull geometry. All three integer scales and the order threshold
precede the graph and the round budget. The stopping set belongs to the
current critical copy, whose vertex type may differ from the initial one.
No stopping-set elimination or factorization is assumed or asserted.
-/
namespace OverfullWork.LocalizedAlmostStoppingRun
open SimpleGraph Finset BoundedCriticalReductionRun AlmostStoppingReductionRun
open OddCutDeficit SparseDeficitCore
open scoped Classical
universe u
set_option maxHeartbeats 4000000

/-- Every allowed run either completes its budget or has an actual odd
almost-overfull witness with small and sparse complement in its current
critical graph. The run, all transitions, and the witness are outputs. -/
theorem above_half_localized_almost_stopping_run (ε : ℝ) (hε : 0<ε) :
    ∃qR qS qT : ℕ,2≤qR ∧ 2≤qS ∧ 2≤qT ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (hc : Overfull.IsDeltaCritical G) (hno : ¬G.HasOverfullSubgraph),
        2*N+2≤Fintype.card V →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ∀m : ℕ,4*(m:ℝ)≤ε*(Fintype.card V:ℝ) →
        ∃j : ℕ,j≤m ∧ ∃C : CriticalGraph.{u},
          Nonempty (Run (initial G hc hno) C j) ∧
          (j=m ∨
            let a:=C.order/(8*qT)
            let B:=stoppingBudget qR qS C
            ∃X : Finset C.vertices,Odd X.card ∧
              deficitMass C.graph C.graph.maxDegree X+
                (∑v∈Xᶜ,C.graph.degree v)≤C.graph.maxDegree+B ∧
              cutEdges C.graph X+deficitMass C.graph C.graph.maxDegree X≤
                C.graph.maxDegree+B ∧
              2*internalEdges C.graph Xᶜ≤B ∧
              (Xᶜ\exceptions C.graph C.graph.maxDegree a).card≤1 ∧
              Xᶜ.card≤C.order/(4096*qT^2)+1) := by
  obtain ⟨qR,qS,hqR,hqS,NR,hRun⟩:=
    above_half_bounded_almost_stopping_run.{u} ε hε
  obtain ⟨qT,hqT,NT,hGeometry⟩:=
    AlmostOverfullOriginalGeometry.above_half_original_almost_geometry.{u}
      (ε/2) (by positivity)
  refine ⟨qR,qS,qT,hqR,hqS,hqT,max NR NT,?_⟩
  intro V _ _ G _ hc hno hn hdense m hbudget
  have hnR : 2*NR+2≤Fintype.card V := by omega
  have hnT : 2*NT+2≤Fintype.card V := by omega
  obtain ⟨j,hjm,C,⟨p⟩,hEnd⟩:=hRun G hc hno hnR hdense m hbudget
  refine ⟨j,hjm,C,⟨p⟩,?_⟩
  rcases hEnd with hEnd|hAlmost
  · exact Or.inl hEnd
  · right
    obtain ⟨hsize,hd⟩:=run_margins ε hε NT m p hnT hdense hbudget hjm
    exact hGeometry qR qS hqR hqS C.graph hsize C.critical hd C.no_overfull hAlmost

end OverfullWork.LocalizedAlmostStoppingRun
