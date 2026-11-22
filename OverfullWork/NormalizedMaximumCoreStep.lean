module

public import OverfullWork.MaximumCoreResidualConstraints
public import OverfullWork.NormalizedClassTwoIteration

@[expose] public section


/-! Advance the all-maximum normalized core by an actual safe three-cross round. -/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun CleanedSourceVAL
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
set_option maxHeartbeats 32000000

structure MaximumCoreStep {B : ℕ} (s : State V B K) where
  selected : Finset V
  selected_subset : selected ⊆ s.cut.setᶜ
  selected_card : selected.card=3
  top : ∀ u ∈ selected, ∀ v ∈ s.cut.setᶜ, v ∉ selected → s.graph.degree v ≤ s.graph.degree u
  round : MaximumCoreThreeCrossRound.Round s.graph s.cut.set selected
  round_no_overfull : ¬(s.graph\round.matching).HasOverfullSubgraph
  next : State V (B-2) K
  budget_parameter_positive : 2 ≤ B
  next_le_residue : next.graph ≤ s.graph\round.matching
  maximum : next.graph.maxDegree+1=s.graph.maxDegree
  budget_decreases :
    (deficitMass next.graph next.graph.maxDegree next.cut.set+(∑ v ∈ next.cut.setᶜ, next.graph.degree v))+3 ≤
      deficitMass s.graph s.graph.maxDegree s.cut.set+(∑ v ∈ s.cut.setᶜ, s.graph.degree v)

theorem exists_maximum_core_step {B : ℕ} (s : State V B K) (hM : Margins s)
    (hCore : ∀ v ∈ s.cut.set, s.graph.degree v=s.graph.maxDegree)
    (hLarge : s.graph.maxDegree < ∑ y ∈ s.cut.setᶜ, s.graph.degree y) :
    Nonempty (MaximumCoreStep s) := by
  obtain ⟨U,hU,hThree,hTop,r,hNo⟩ := MaximumCoreThreeCrossRound.exists_safe_round s.graph s.cut
    s.uncolourable s.ready hCore hLarge hM.2.1 hM.2.2
  have hSourceTotal := MaximumCoreThreeCrossRound.source_total_ge_add_two s.graph s.cut hCore hLarge
  have hBudget := s.cut.budget
  have hB : 2 ≤ B := by omega
  have hX : s.cut.set.Nonempty := by
    apply card_pos.mp
    obtain ⟨m,hm⟩ := s.cut.odd
    omega
  have hDrop := r.budget_drop_three hU hThree
  have hBudgetR := r.budget_bound_improves_two hU hThree hX B s.cut.budget
  have hBudgetR' : deficitMass (s.graph\r.matching) (s.graph\r.matching).maxDegree s.cut.set+
      (∑ v ∈ s.cut.setᶜ, (s.graph\r.matching).degree v) ≤ (s.graph\r.matching).maxDegree+(B-2) := by omega
  have hInd : s.graph.IsIndepSet (↑(s.cut.setᶜ):Set V) := by simpa only [coe_compl] using s.cut.independent
  have hIndR := FixedCoreBudgetTransport.independent_of_le s.graph (s.graph\r.matching) s.cut.setᶜ hInd sdiff_le
  have hConstraints := r.residual_constraints s.ready hU hThree hTop hM.2.2
  obtain ⟨H,hLe,hMax,hNC,hNoH,c,hCard,hReady,hBudgetH⟩ :=
    JointCutNormalization.exists_joint_normalization (s.graph\r.matching) r.residual_uncolourable hNo
      s.cut.set s.cut.odd (B-2) K s.cut.complement_small hIndR hConstraints.1 hConstraints.2 hBudgetR'
  let t : State V (B-2) K := ⟨H,c,hReady,hNC,hNoH⟩
  have hMaximum : t.graph.maxDegree+1=s.graph.maxDegree := by
    have hPos : 0 < s.graph.maxDegree := by have hh := hM.2.2;omega
    have hr := r.residual_maxDegree
    change H.maxDegree+1=s.graph.maxDegree
    omega
  have hBudgetStep :
      (deficitMass t.graph t.graph.maxDegree t.cut.set+(∑ v ∈ t.cut.setᶜ, t.graph.degree v))+3 ≤
        deficitMass s.graph s.graph.maxDegree s.cut.set+(∑ v ∈ s.cut.setᶜ, s.graph.degree v) := by
    change (deficitMass H H.maxDegree c.set+(∑ v ∈ c.setᶜ, H.degree v))+3 ≤ _
    omega
  exact ⟨⟨U,hU,hThree,hTop,r,hNo,t,hB,hLe,hMaximum,hBudgetStep⟩⟩

theorem MaximumCoreStep.le {B : ℕ} {s : State V B K} (p : MaximumCoreStep s) : p.next.graph ≤ s.graph :=
  p.next_le_residue.trans sdiff_le

theorem MaximumCoreStep.margins {B : ℕ} {s : State V B K} (p : MaximumCoreStep s)
    (hM : Margins s) : Margins p.next := by
  have hB := p.budget_parameter_positive
  have hMax := p.maximum
  rcases hM with ⟨h₁,h₂,h₃⟩
  unfold Margins
  omega

end OverfullWork.NormalizedClassTwoStep
