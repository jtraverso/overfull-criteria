module

public import OverfullWork.ReducedTerminalAboveHalf
public import OverfullWork.SmallCentreCriticalExclusion

@[expose] public section


/-! Original critical-source fork after both newly proved eliminations.

The direct small-centre branch is excluded. All-maximum normalized cores
advance by three-cross rounds. No criticality of their targets is assumed.
-/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u
set_option maxHeartbeats 32000000

theorem above_half_reduction_or_reduced_terminal (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 8 ≤ Q ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N ≤ Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ) ≤ (G.maxDegree:ℝ) → ¬G.HasOverfullSubgraph →
        let k := Fintype.card V/(4096*Q^2)
        (∃ r : CriticalTwoColourReduction.Reduction G,
          (∑ v : V, (2-r.layer.degree v)) ≤ 2*k+2 ∧ ¬(G\r.layer).HasOverfullSubgraph) ∨
        ∃ s : State V (6*k+6) (k+1), s.graph ≤ G ∧ s.graph.maxDegree=G.maxDegree ∧
          ∃ C : ℕ, ∃ t : State V C (k+1), ∃ j : ℕ,
            ReducedRun s t j ∧ ReducedTerminal t ∧ Margins t ∧
              C+2*j=6*k+6 ∧ t.graph.maxDegree+j=G.maxDegree ∧ t.graph ≤ G := by
  obtain ⟨QM,hQM,NM,hMargins⟩ := PaperFirstRoundAboveHalf.uniform_margins ε hε
  obtain ⟨QE,hQE,NE,hExclude⟩ := NormalizedCanonicalCandidate.above_half_small_centre_critical_exclusion.{u} ε hε
  let Q := max QM QE
  have hMQ : QM ≤ Q := le_max_left _ _
  have hEQ : QE ≤ Q := le_max_right _ _
  have hQ : 8 ≤ Q := hQE.trans hEQ
  obtain ⟨NF,hFork⟩ := FlexibleAlmostReduction.above_half_normalized_fork_at_budget.{u} ε hε Q (by omega)
  refine ⟨Q,hQ,max NM (max NE NF),?_⟩
  intro V _ _ G _ hn hcrit hdense hNo
  have hDivM : Fintype.card V/(4096*Q^2) ≤ Fintype.card V/(4096*QM^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hMQ 2)) (by positivity)
  have hDivE : Fintype.card V/(4096*Q^2) ≤ Fintype.card V/(4096*QE^2) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hEQ 2)) (by positivity)
  have hBounds := hMargins (Fintype.card V) G.maxDegree (by omega) hdense
  dsimp only at hBounds ⊢
  rcases hFork G (by omega) hcrit hdense hNo with hCert|hReduction
  · obtain ⟨c⟩ := hCert
    by_cases hSmall : ∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x
    · exact (hExclude G c (by omega) hcrit hdense hNo (by omega) (by omega) hSmall).elim
    · right
      push Not at hSmall
      obtain ⟨x,hx,hLarge⟩ := hSmall
      have hNonmax := CriticalIndependentPairMatching.complement_nonmaximum G hcrit c hx hLarge
      have hInd : G.IsIndepSet (↑(c.setᶜ):Set V) := by simpa only [coe_compl] using c.independent
      obtain ⟨H,hLe,hMax,hNC,hNoH,c',_,hReady,_⟩ :=
        JointCutNormalization.exists_joint_normalization G hcrit.2.1 hNo c.set c.odd _ _
          c.complement_small hInd hNonmax c.light_pairs c.budget
      let s : State V (6*(Fintype.card V/(4096*Q^2))+6) (Fintype.card V/(4096*Q^2)+1) :=
        ⟨H,c',hReady,hNC,hNoH⟩
      have hM : Margins s := by
        unfold Margins
        change Fintype.card V+2*(6*(Fintype.card V/(4096*Q^2))+6)+(Fintype.card V/(4096*Q^2)+1)+3 ≤
          2*H.maxDegree ∧ _
        rw [hMax]
        exact ⟨by have hh := hBounds.1;omega,by have hh := hBounds.2.1;omega,by have hh := hBounds.2.2;omega⟩
      obtain ⟨C,t,j,hRun,hTerminal,hMT,hBudget,hDegree,hLeT⟩ := exists_reduced_terminal_run s hM
      refine ⟨s,hLe,hMax,C,t,j,hRun,hTerminal,hMT,hBudget,?_,hLeT.trans hLe⟩
      simpa only [s,hMax] using hDegree
  · left
    obtain ⟨r,hMissing,hNoR⟩ := hReduction
    refine ⟨r,hMissing,?_⟩
    have transport (d₁ d₂ : DecidableRel (G\r.layer).Adj) :
        (¬@SimpleGraph.HasOverfullSubgraph V _ _ (G\r.layer) d₁) →
          ¬@SimpleGraph.HasOverfullSubgraph V _ _ (G\r.layer) d₂ := by
      cases Subsingleton.elim d₁ d₂
      exact id
    exact transport _ _ hNoR

end OverfullWork.NormalizedClassTwoStep
