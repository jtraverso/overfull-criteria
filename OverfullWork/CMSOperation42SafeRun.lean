module

public import OverfullWork.CMSOperation42MaximumCoreCleanup

@[expose] public section


/-! The two safe kinds of matching removal can be interleaved on the
same core. The exact budget identity bounds every constructed
prefix by half the initial odd-cut slack. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion OddCutDeficit NearTightOddSetGeometry
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

inductive SafeFixedCoreStep (X : Finset V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph V → Prop
  | ordinary (s : ClassTwoCleanupRound.CleanRound G X) (hNo : ¬s.graph.HasOverfullSubgraph) :
      SafeFixedCoreStep X G s.graph
  | maximum {U : Finset V} (s : MaximumCoreCleanRound G X U) : SafeFixedCoreStep X G s.graph

theorem SafeFixedCoreStep.le {X : Finset V} {G H : SimpleGraph V} [DecidableRel G.Adj]
    (p : SafeFixedCoreStep X G H) : H ≤ G := by
  cases p with
  | ordinary s _ => exact s.le_residue.trans sdiff_le
  | maximum s => exact s.le_residue.trans sdiff_le

theorem SafeFixedCoreStep.maximum_add_one {X : Finset V} {G H : SimpleGraph V}
    [DecidableRel G.Adj] [dH : DecidableRel H.Adj]
    (p : SafeFixedCoreStep X G H) (hX : X.Nonempty) : H.maxDegree+1 = G.maxDegree := by
  cases p with
  | ordinary s _ =>
    cases Subsingleton.elim dH (fun u v => Classical.propDecidable (s.graph.Adj u v))
    have hMax := s.maximum
    have hPos := s.anchor_nonmaximum
    omega
  | maximum s =>
    cases Subsingleton.elim dH (fun u v => Classical.propDecidable (s.graph.Adj u v))
    obtain ⟨x,hx⟩ := hX
    have hOne := s.round.core_degrees x hx
    have hLe := s.round.matching.degree_le_of_le s.round.le_original (v := x)
    have hD := G.degree_le_maxDegree x
    have hMax := s.maximum
    omega

theorem SafeFixedCoreStep.budget_drop_three {X : Finset V} {G H : SimpleGraph V}
    [DecidableRel G.Adj] [dH : DecidableRel H.Adj]
    (p : SafeFixedCoreStep X G H) :
    ClassTwoMatchingRun.budget H X+3 = ClassTwoMatchingRun.budget G X := by
  cases p with
  | ordinary s _ =>
    cases Subsingleton.elim dH (fun u v => Classical.propDecidable (s.graph.Adj u v))
    exact s.budget_drop_three
  | maximum s =>
    cases Subsingleton.elim dH (fun u v => Classical.propDecidable (s.graph.Adj u v))
    exact s.budget_drop

theorem SafeFixedCoreStep.no_overfull {X : Finset V} {G H : SimpleGraph V}
    [DecidableRel G.Adj] [dH : DecidableRel H.Adj]
    (p : SafeFixedCoreStep X G H) : ¬H.HasOverfullSubgraph := by
  cases p with
  | ordinary s hNo =>
    cases Subsingleton.elim dH (fun u v => Classical.propDecidable (s.graph.Adj u v))
    exact hNo
  | maximum s =>
    cases Subsingleton.elim dH (fun u v => Classical.propDecidable (s.graph.Adj u v))
    exact s.no_overfull

theorem SafeFixedCoreStep.robust_core {X : Finset V} {G H : SimpleGraph V}
    [DecidableRel G.Adj] [dH : DecidableRel H.Adj]
    (p : SafeFixedCoreStep X G H) (r t : ℕ)
    (hRob : IsRobustAt (G.induce (X : Set V)) r t) :
    IsRobustAt (H.induce (X : Set V)) (r-1) t := by
  cases p with
  | ordinary s _ =>
    cases Subsingleton.elim dH (fun u v => Classical.propDecidable (s.graph.Adj u v))
    exact clean_round_robust_core s r t hRob
  | maximum s =>
    cases Subsingleton.elim dH (fun u v => Classical.propDecidable (s.graph.Adj u v))
    exact s.robust_core r t hRob

inductive SafeFixedCoreRun (X : Finset V) (G : SimpleGraph V) : SimpleGraph V → ℕ → Prop
  | refl : SafeFixedCoreRun X G G 0
  | step {H J : SimpleGraph V} {j : ℕ} [DecidableRel H.Adj]
      (prior : SafeFixedCoreRun X G H j) (now : SafeFixedCoreStep X H J) :
      SafeFixedCoreRun X G J (j+1)

theorem SafeFixedCoreRun.le {X : Finset V} {G H : SimpleGraph V} {j : ℕ}
    (p : SafeFixedCoreRun X G H j) : H ≤ G := by
  induction p with
  | refl => exact le_rfl
  | step _ s ih => exact s.le.trans ih

theorem SafeFixedCoreRun.budget_and_maximum {X : Finset V} {G H : SimpleGraph V}
    [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj] {j : ℕ}
    (p : SafeFixedCoreRun X G H j) (hX : X.Nonempty) :
    ClassTwoMatchingRun.budget H X+3*j = ClassTwoMatchingRun.budget G X ∧
      H.maxDegree+j = G.maxDegree := by
  revert dH
  induction p with
  | refl =>
    intro dH
    cases Subsingleton.elim dH dG
    simp
  | @step H J j dStep p s ih =>
    intro dJ
    have hPrev := @ih dStep
    have hDrop := s.budget_drop_three (dH := dJ)
    have hMax := s.maximum_add_one (dH := dJ) hX
    omega

theorem SafeFixedCoreRun.robust_core {X : Finset V} {G H : SimpleGraph V}
    [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj] {j : ℕ}
    (p : SafeFixedCoreRun X G H j) (r t : ℕ)
    (hRob : IsRobustAt (G.induce (X : Set V)) r t) :
    IsRobustAt (H.induce (X : Set V)) (r-j) t := by
  revert dH
  induction p with
  | refl =>
    intro dH
    cases Subsingleton.elim dH dG
    simpa only [Nat.sub_zero] using hRob
  | @step H J j dStep p s ih =>
    intro dJ
    simpa only [Nat.sub_sub] using s.robust_core (dH := dJ) (r-j) t (@ih dStep)

theorem SafeFixedCoreRun.no_overfull {X : Finset V} {G H : SimpleGraph V}
    [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj] {j : ℕ}
    (p : SafeFixedCoreRun X G H j) (hNo : ¬G.HasOverfullSubgraph) : ¬H.HasOverfullSubgraph := by
  revert dH
  cases p with
  | refl =>
    intro dH
    cases Subsingleton.elim dH dG
    exact hNo
  | step _ s =>
    intro dH
    exact s.no_overfull

theorem SafeFixedCoreRun.length_le_half_slack {X : Finset V} {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {j : ℕ}
    (p : SafeFixedCoreRun X G H j) (hOdd : Odd X.card)
    (hInd : G.IsIndepSet (↑(Xᶜ) : Set V)) (hNo : ¬G.HasOverfullSubgraph)
    (B : ℕ) (hBudget : ClassTwoMatchingRun.budget G X ≤ G.maxDegree+B) :
    2*j ≤ B := by
  have hX : X.Nonempty := card_pos.mp (by obtain ⟨m,hm⟩ := hOdd; omega)
  have hBook := p.budget_and_maximum hX
  have hHInd := FixedCoreBudgetTransport.independent_of_le G H Xᶜ hInd p.le
  have hCut := MatchingOddDeficiency.cut_eq_complementary_degree_sum H X hHInd
  have hLower := (no_overfull_iff_odd_cut_deficit H).mp (p.no_overfull hNo) X hOdd
  rw [hCut] at hLower
  have hLower' : H.maxDegree ≤ ClassTwoMatchingRun.budget H X := by
    simpa only [ClassTwoMatchingRun.budget,Nat.add_comm] using hLower
  omega

theorem SafeFixedCoreRun.uniform_robust_source {X : Finset V} {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {j : ℕ}
    (p : SafeFixedCoreRun X G H j) (hOdd : Odd X.card)
    (hInd : G.IsIndepSet (↑(Xᶜ) : Set V)) (hNo : ¬G.HasOverfullSubgraph)
    (B : ℕ) (hBudget : ClassTwoMatchingRun.budget G X ≤ G.maxDegree+B)
    (r t : ℕ) (hRob : IsRobustAt (G.induce (X : Set V)) r t) (ν τ : ℝ)
    (hν : ν*(Fintype.card V:ℝ) ≤ ((r-(B/2+Xᶜ.card):ℕ):ℝ))
    (hτ : ((t+Xᶜ.card:ℕ):ℝ) ≤ τ*(Fintype.card V:ℝ)) :
    IsRealRobust H ν τ := by
  have hLength := p.length_le_half_slack hOdd hInd hNo B hBudget
  have hCore := p.robust_core r t hRob
  have hSource := robust_of_ordinary_core H X (r-j) t hCore
  apply isRealRobust_of_integer H (r-j-Xᶜ.card) (t+Xᶜ.card) ν τ hSource _ hτ
  exact hν.trans (by exact_mod_cast (show r-(B/2+Xᶜ.card) ≤ r-j-Xᶜ.card by omega))

end OverfullWork.CMSMatchingRemoval
