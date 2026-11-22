module

public import OverfullWork.PaperCleanStepContinuation

@[expose] public section


/-! # Telescoping actual fixed-core class-two matching/cleanup rounds

Runs contain actual matchings and actual cleanup deletion runs. No
transition oracle or criticality is an input. The telescoping identities
hold for every such run; no theorem that arbitrarily many admissible
rounds exist, or that every residue is no-overfull, is asserted.
-/
namespace OverfullWork.ClassTwoMatchingRun
open SimpleGraph Finset OddCutDeficit ClassTwoCleanupRound
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

def budget (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : ℕ :=
  deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)

inductive Run (X : Finset V) (G : SimpleGraph V) : SimpleGraph V→ℕ→Prop
  | refl : Run X G G 0
  | step {H : SimpleGraph V} {j : ℕ} [DecidableRel H.Adj]
      (run : Run X G H j) (round : CleanRound H X) :
      Run X G round.graph (j+1)

theorem Run.le {G H : SimpleGraph V} {X : Finset V} {j : ℕ} (p : Run X G H j) : H≤G := by
  induction p with
  | refl => exact le_rfl
  | step p s ih => exact (s.le_residue.trans sdiff_le).trans ih

theorem Run.maximum {G H : SimpleGraph V} [DecidableRel G.Adj] [dH : DecidableRel H.Adj]
    {X : Finset V} {j : ℕ} (p : Run X G H j) : H.maxDegree+j=G.maxDegree := by
  revert dH
  induction p with
  | refl =>
    intro dH
    simp only [Nat.add_zero,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card]
  | @step H j dStep p s ih =>
    intro dEnd
    have hI:=@ih dStep
    have hMax:=s.maximum
    have hPos:=s.anchor_nonmaximum
    simp only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] at hMax hPos hI ⊢
    omega

theorem Run.budget_identity {G H : SimpleGraph V} [DecidableRel G.Adj] [dH : DecidableRel H.Adj]
    {X : Finset V} {j : ℕ} (p : Run X G H j) : budget H X+3*j=budget G X := by
  revert dH
  induction p with
  | refl =>
    intro dH
    simp only [Nat.mul_zero,Nat.add_zero,budget,deficitMass,SimpleGraph.maxDegree,
      ←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
  | @step H j dStep p s ih =>
    intro dEnd
    have hI:=@ih dStep
    have hDrop:=s.budget_drop_three
    simp only [budget,deficitMass,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] at hDrop hI ⊢
    omega

/-- This is an identity of the actual numerical slack, including its
possible negative values. It does not assume final no-overfullness. -/
theorem Run.slack {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {X : Finset V} {j : ℕ} (p : Run X G H j) :
    (budget H X:ℤ)-(H.maxDegree:ℤ)=
      (budget G X:ℤ)-(G.maxDegree:ℤ)-2*(j:ℤ) := by
  have hMax:=p.maximum
  have hBudget:=p.budget_identity
  omega

theorem Run.length_le_budget {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {X : Finset V} {j : ℕ} (p : Run X G H j) : 3*j≤budget G X := by
  have hh:=p.budget_identity
  omega

end OverfullWork.ClassTwoMatchingRun
