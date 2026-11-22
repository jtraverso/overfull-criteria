module

public import OverfullWork.NormalizedMaximumCoreStep

@[expose] public section


/-! The all-maximum geometry is an advancing case, not a terminal alternative. -/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
set_option maxHeartbeats 32000000

def ReducedTerminal {B : ℕ} (s : State V B K) : Prop :=
  (∀ x ∈ s.cut.set, (∑ y ∈ s.cut.setᶜ, s.graph.degree y) ≤ s.graph.degree x) ∨
  ∃ x ∈ s.cut.set, (∀ v ∈ s.cut.set, s.graph.degree x ≤ s.graph.degree v) ∧
    s.graph.degree x < (∑ y ∈ s.cut.setᶜ, s.graph.degree y) ∧
    ∃ v ∈ s.cut.set, v ≠ x ∧ s.graph.degree v ≤ s.graph.maxDegree-s.graph.degree x ∧
      s.graph.IsIndepSet (↑(insert x s.cut.setᶜ):Set V)

inductive AdvancingStep {B : ℕ} (s : State V B K) where
  | ordinary (step : Step s) : AdvancingStep s
  | allMaximum (step : MaximumCoreStep s) : AdvancingStep s

def AdvancingStep.next {B : ℕ} {s : State V B K} : AdvancingStep s → State V (B-2) K
  | .ordinary step => step.next
  | .allMaximum step => step.next

theorem AdvancingStep.budget_positive {B : ℕ} {s : State V B K} (p : AdvancingStep s) : 2 ≤ B := by
  cases p with
  | ordinary p => exact p.budget_parameter_positive
  | allMaximum p => exact p.budget_parameter_positive

theorem AdvancingStep.le {B : ℕ} {s : State V B K} (p : AdvancingStep s) : p.next.graph ≤ s.graph := by
  cases p with
  | ordinary p => exact p.le
  | allMaximum p => exact p.le

theorem AdvancingStep.maximum {B : ℕ} {s : State V B K} (p : AdvancingStep s) :
    p.next.graph.maxDegree+1=s.graph.maxDegree := by
  cases p with
  | ordinary p => exact p.maximum
  | allMaximum p => exact p.maximum

theorem AdvancingStep.margins {B : ℕ} {s : State V B K} (p : AdvancingStep s) (hM : Margins s) :
    Margins p.next := by
  cases p with
  | ordinary p => exact p.margins hM
  | allMaximum p => exact p.margins hM

theorem reduced_terminal_or_step {B : ℕ} (s : State V B K) (hM : Margins s) :
    ReducedTerminal s ∨ Nonempty (AdvancingStep s) := by
  rcases terminal_or_step s hM with hTerminal|hStep
  · rcases hTerminal with hSmall|hMaximum|hLow
    · exact Or.inl (Or.inl hSmall)
    · obtain ⟨p⟩ := exists_maximum_core_step s hM hMaximum.1 hMaximum.2
      exact Or.inr ⟨.allMaximum p⟩
    · exact Or.inl (Or.inr hLow)
  · obtain ⟨p⟩ := hStep
    exact Or.inr ⟨.ordinary p⟩

inductive ReducedRun : {B C : ℕ} → State V B K → State V C K → ℕ → Prop
  | refl {B : ℕ} (s : State V B K) : ReducedRun s s 0
  | step {B C : ℕ} {s : State V B K} {t : State V C K} {j : ℕ}
      (run : ReducedRun s t j) (move : AdvancingStep t) : ReducedRun s move.next (j+1)

theorem ReducedRun.single {B : ℕ} {s : State V B K} (p : AdvancingStep s) : ReducedRun s p.next 1 :=
  .step (.refl s) p

theorem ReducedRun.trans {B C D : ℕ} {s : State V B K} {t : State V C K} {u : State V D K}
    {j k : ℕ} (p : ReducedRun s t j) (q : ReducedRun t u k) : ReducedRun s u (j+k) := by
  induction q with
  | refl => simpa only [Nat.add_zero] using p
  | step q a ih => simpa only [Nat.add_assoc] using ReducedRun.step (ih p) a

theorem ReducedRun.le {B C : ℕ} {s : State V B K} {t : State V C K} {j : ℕ}
    (p : ReducedRun s t j) : t.graph ≤ s.graph := by
  induction p with
  | refl => exact le_rfl
  | step p a ih => exact a.le.trans ih

theorem ReducedRun.maximum {B C : ℕ} {s : State V B K} {t : State V C K} {j : ℕ}
    (p : ReducedRun s t j) : t.graph.maxDegree+j=s.graph.maxDegree := by
  induction p with
  | refl => simp
  | step p a ih => have hh := a.maximum;omega

theorem ReducedRun.budget_parameter {B C : ℕ} {s : State V B K} {t : State V C K} {j : ℕ}
    (p : ReducedRun s t j) : C+2*j=B := by
  induction p with
  | refl => omega
  | step p a ih => have hh := a.budget_positive;omega

theorem ReducedRun.margins {B C : ℕ} {s : State V B K} {t : State V C K} {j : ℕ}
    (p : ReducedRun s t j) (hM : Margins s) : Margins t := by
  induction p with
  | refl => exact hM
  | step p a ih => exact a.margins (ih hM)

theorem reduced_terminates (B : ℕ) (s : State V B K) (hM : Margins s) :
    ∃ C : ℕ, ∃ t : State V C K, ∃ j : ℕ, ReducedRun s t j ∧ ReducedTerminal t := by
  induction B using Nat.strong_induction_on with
  | h B ih =>
    rcases reduced_terminal_or_step s hM with hTerminal|hStep
    · exact ⟨B,s,0,.refl s,hTerminal⟩
    · obtain ⟨p⟩ := hStep
      have hLt : B-2 < B := by have hh := p.budget_positive;omega
      obtain ⟨C,t,j,hRun,hTerminal⟩ := ih (B-2) hLt p.next (p.margins hM)
      exact ⟨C,t,1+j,(ReducedRun.single p).trans hRun,hTerminal⟩

theorem exists_reduced_terminal_run {B : ℕ} (s : State V B K) (hM : Margins s) :
    ∃ C : ℕ, ∃ t : State V C K, ∃ j : ℕ,
      ReducedRun s t j ∧ ReducedTerminal t ∧ Margins t ∧
      C+2*j=B ∧ t.graph.maxDegree+j=s.graph.maxDegree ∧ t.graph ≤ s.graph := by
  obtain ⟨C,t,j,hRun,hTerminal⟩ := reduced_terminates B s hM
  exact ⟨C,t,j,hRun,hTerminal,hRun.margins hM,hRun.budget_parameter,hRun.maximum,hRun.le⟩

end OverfullWork.NormalizedClassTwoStep
