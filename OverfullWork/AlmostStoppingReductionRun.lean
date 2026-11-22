module

public import OverfullWork.BoundedCriticalReductionRun
public import OverfullWork.SparseCompatibleReduction

@[expose] public section


/-! # Actual bounded reductions with an original-graph almost-overfull stop

The sparse compatible reduction supplies each actual next layer, and a
critical witness is extracted in its actual no-overfull residue. The
other branch stops on an almost-overfull set before deleting a layer.
The uniform threshold precedes both the graph and the finite step budget.
There is no indefinite iteration or elimination of the stopping branch.

The one-step theorem retains the missing-degree bound. The existing Run
type retains the constructed layers and critical copies, but does not
store that additional numerical annotation on every transition.
-/
namespace OverfullWork.AlmostStoppingReductionRun
open SimpleGraph Finset BoundedCriticalReductionRun
open AlmostOverfullLayerCompatibility
open scoped Classical
universe u
set_option maxHeartbeats 4000000

def stoppingBudget (qR qS : ℕ) (C : CriticalGraph.{u}) : ℕ :=
  (2*(C.order/(4096*qR^2))+2)+8*(C.order/(4096*qS^2))

/-- The actual next step includes its sparse missing-degree estimate;
no-overfullness of its residue and the critical copy are constructed. -/
theorem above_half_sparse_step_or_almost (ε : ℝ) (hε : 0<ε) :
    ∃qR qS : ℕ,2≤qR ∧ 2≤qS ∧ ∃N : ℕ,
      ∀C : CriticalGraph.{u},N≤C.order →
        ((1:ℝ)/2+ε)*(C.order:ℝ)≤(C.graph.maxDegree:ℝ) →
        HasOddAlmostOverfullSet C.graph (stoppingBudget qR qS C) ∨
          ∃s : Step C,(∑v:C.vertices,(2-s.reduction.layer.degree v))≤
            2*(C.order/(4096*qR^2))+2 := by
  obtain ⟨qR,qS,hqR,hqS,N,hfork⟩:=
    SparseCompatibleReduction.above_half_sparse_compatible_or_almost.{u} ε hε
  refine ⟨qR,qS,hqR,hqS,N,?_⟩
  intro C hn hdense
  have hnext:=hfork C.graph hn C.critical hdense C.no_overfull
  change HasOddAlmostOverfullSet C.graph (stoppingBudget qR qS C) ∨
    ∃r : CriticalTwoColourReduction.Reduction C.graph,
      (∑v:C.vertices,(2-r.layer.degree v))≤2*(C.order/(4096*qR^2))+2 ∧
      ¬(C.graph\r.layer).HasOverfullSubgraph at hnext
  rcases hnext with halmost|⟨r,hMissing,hnoR⟩
  · exact Or.inl halmost
  · obtain ⟨w⟩:=Critical.exists_criticalWitness (C.graph\r.layer)
      r.residual_uncolourable hnoR
    let s : Step C:=⟨r,hnoR,w⟩
    exact Or.inr ⟨s,hMissing⟩

/-- Every permitted finite budget has a constructed run, ending either
at that budget or at a certified almost-overfull set of its current
critical graph. No layer is removed in the stopping branch. -/
theorem above_half_bounded_almost_stopping_run (ε : ℝ) (hε : 0<ε) :
    ∃qR qS : ℕ,2≤qR ∧ 2≤qS ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (hc : Overfull.IsDeltaCritical G) (hno : ¬G.HasOverfullSubgraph),
        2*N+2≤Fintype.card V →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ∀m : ℕ,4*(m:ℝ)≤ε*(Fintype.card V:ℝ) →
        ∃j : ℕ,j≤m ∧ ∃C : CriticalGraph.{u},
          Nonempty (Run (initial G hc hno) C j) ∧
          (j=m ∨ HasOddAlmostOverfullSet C.graph (stoppingBudget qR qS C)) := by
  obtain ⟨qR,qS,hqR,hqS,N,hfork⟩:=above_half_sparse_step_or_almost.{u}
    (ε/2) (by positivity)
  refine ⟨qR,qS,hqR,hqS,N,?_⟩
  intro V _ _ G _ hc hno hn hdense m hbudget
  let B:=initial G hc hno
  have build : ∀t j : ℕ,j+t=m → ∀C : CriticalGraph.{u},Run B C j →
      ∃i : ℕ,i≤m ∧ ∃D : CriticalGraph.{u},Nonempty (Run B D i) ∧
        (i=m ∨ HasOddAlmostOverfullSet D.graph (stoppingBudget qR qS D)) := by
    intro t
    induction t with
    | zero =>
      intro j hj C p
      exact ⟨j,by omega,C,⟨p⟩,Or.inl (by omega)⟩
    | succ t ih =>
      intro j hj C p
      have hjm : j≤m := by omega
      obtain ⟨hsize,hd⟩:=run_margins ε hε N m p hn hdense hbudget hjm
      by_cases halmost : HasOddAlmostOverfullSet C.graph (stoppingBudget qR qS C)
      · exact ⟨j,hjm,C,⟨p⟩,Or.inr halmost⟩
      · obtain ⟨s,_hMissing⟩:=(hfork C hsize hd).resolve_left halmost
        exact ih (j+1) (by omega) s.target (Run.snoc p s)
  exact build m 0 (by omega) B (Run.nil B)

end OverfullWork.AlmostStoppingReductionRun
