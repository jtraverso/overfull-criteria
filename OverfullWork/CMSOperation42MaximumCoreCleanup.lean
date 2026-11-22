module

public import OverfullWork.CMSOperation42MaximumCoreRound

@[expose] public section


/-! Algorithm 2 after a maximum-core round preserves the fixed
induced core and drops the core budget by exactly three. The
complementary excess falls by two. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph OddCutDeficit CleanedSourceVAL NormalizedAlmostStoppingRun
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

structure MaximumCoreCleanRound (G : SimpleGraph V) [DecidableRel G.Adj] (X U : Finset V) where
  round : MaximumCoreThreeCrossRound.Round G X U
  graph : SimpleGraph V
  deletion : MaximumNeighbourCleanup.DeletionRun Xᶜ (G \ round.matching) graph
  le_residue : graph ≤ G \ round.matching
  maximum : graph.maxDegree = G.maxDegree-1
  uncolourable : ¬graph.EdgeColorable graph.maxDegree
  no_overfull : ¬graph.HasOverfullSubgraph
  core : graph.induce (X : Set V) = (G \ round.matching).induce (X : Set V)
  independent : graph.IsIndepSet (↑(Xᶜ) : Set V)
  ready : IsReady graph Xᶜ
  light_pairs : ∀ y ∈ Xᶜ,∀ z ∈ Xᶜ,y ≠ z → graph.degree y+graph.degree z < graph.maxDegree+2
  budget_drop : ClassTwoMatchingRun.budget graph X+3 = ClassTwoMatchingRun.budget G X

set_option maxHeartbeats 1600000 in
theorem exists_cleanup_of_maximum_core_round (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hReady : IsReady G c.setᶜ)
    (U : Finset V) (hU : U ⊆ c.setᶜ) (hThree : U.card = 3)
    (hTop : ∀ u ∈ U,∀ v ∈ c.setᶜ,v ∉ U → G.degree v ≤ G.degree u)
    (q : MaximumCoreThreeCrossRound.Round G c.set U) (hSmall : 4*(B+K+2)+1 ≤ G.maxDegree)
    (hNo : ¬(G \ q.matching).HasOverfullSubgraph) :
    ∃ s : MaximumCoreCleanRound G c.set U,s.round = q := by
  let X := c.set
  let R := G \ q.matching
  have hConstraints := q.residual_constraints hReady hU hThree hTop hSmall
  obtain ⟨H,hRun,hLe,hMax,hNC,hNoH,hKeep,hNonmax,hRich⟩ :=
    MaximumNeighbourCleanup.exists_cleanup_no_overfull R q.residual_uncolourable Xᶜ hConstraints.1 hNo
  have hX : ((↑(Xᶜ) : Set V)ᶜ) = (X : Set V) := by ext v; simp
  rw [hX] at hKeep
  have hGInd : G.IsIndepSet (↑(Xᶜ) : Set V) := by simpa only [coe_compl] using c.independent
  have hRInd := FixedCoreBudgetTransport.independent_of_le G R Xᶜ hGInd sdiff_le
  have hHInd := FixedCoreBudgetTransport.independent_of_le R H Xᶜ hRInd hLe
  have hPairs (y : V) (hy : y ∈ Xᶜ) (z : V) (hz : z ∈ Xᶜ) (hyz : y ≠ z) :
      H.degree y+H.degree z < H.maxDegree+2 := by
    rw [hMax]
    have hY := H.degree_le_of_le hLe (v := y)
    have hZ := H.degree_le_of_le hLe (v := z)
    have hP := hConstraints.2 y hy z hz hyz
    simp only [R,SimpleGraph.maxDegree,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hY hZ hP ⊢
    omega
  have hBudget : ClassTwoMatchingRun.budget H X = ClassTwoMatchingRun.budget R X :=
    FixedCoreBudgetTransport.budget_eq_of_fixed_core R H X hKeep hMax hRInd hHInd
  have hDrop : ClassTwoMatchingRun.budget R X+3 = ClassTwoMatchingRun.budget G X :=
    q.budget_drop_three hU hThree
  exact ⟨⟨q,H,hRun,hLe,hMax.trans q.residual_maxDegree,hNC,hNoH,hKeep,hHInd,
    ⟨hNonmax,hRich⟩,hPairs,by rw [hBudget,hDrop]⟩,rfl⟩

theorem MaximumCoreCleanRound.excess_decreases {G : SimpleGraph V} [DecidableRel G.Adj]
    {X U : Finset V} (s : MaximumCoreCleanRound G X U)
    (hCore : ∀ v ∈ X,G.degree v = G.maxDegree)
    (hLarge : G.maxDegree+2 ≤ ∑ w ∈ Xᶜ,G.degree w) (v : V) (hv : v ∈ X) :
    ((∑ w ∈ Xᶜ,s.graph.degree w)-s.graph.degree v)+2 ≤
      (∑ w ∈ Xᶜ,G.degree w)-G.maxDegree := by
  have hZero : deficitMass G G.maxDegree X = 0 := by
    apply sum_eq_zero
    intro w hw
    rw [hCore w hw,Nat.sub_self]
  have hDrop := s.budget_drop
  unfold ClassTwoMatchingRun.budget at hDrop
  rw [hZero,zero_add] at hDrop
  have hDef : s.graph.maxDegree-s.graph.degree v ≤ deficitMass s.graph s.graph.maxDegree X :=
    single_le_sum (fun w _ => Nat.zero_le (s.graph.maxDegree-s.graph.degree w)) hv
  have hD := s.graph.degree_le_maxDegree v
  have hMax := s.maximum
  omega

theorem MaximumCoreCleanRound.robust_core {G : SimpleGraph V} [DecidableRel G.Adj]
    {X U : Finset V} (s : MaximumCoreCleanRound G X U) (r t : ℕ)
    (hRob : RobustExpansion.IsRobustAt (G.induce (X : Set V)) r t) :
    RobustExpansion.IsRobustAt (s.graph.induce (X : Set V)) (r-1) t :=
  robust_core_after_matching_and_cleanup s.round.matching s.round.degree_le_one s.core r t hRob

end OverfullWork.CMSMatchingRemoval
