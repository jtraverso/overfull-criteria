module

public import OverfullWork.NormalizedClassTwoStep

@[expose] public section


/-! # Termination of the normalized safe class-two reduction

Every step contains its actual matching/cleanup and an actual jointly
normalized target. All states retain class two and no-overfullness.
Induction on the nonnegative budget parameter constructs a terminal
state; the number of completed matching rounds is at most B/2.
The core may vary under joint normalization, so fixed-core CMS history
is not claimed.
-/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
set_option maxHeartbeats 10000000

inductive Run : {B C : ℕ}→State V B K→State V C K→ℕ→Prop
  | refl {B : ℕ} (s : State V B K) : Run s s 0
  | step {B C : ℕ} {s : State V B K} {t : State V C K} {j : ℕ}
      (run : Run s t j) (transition : Step t) : Run s transition.next (j+1)

theorem Run.single {B : ℕ} {s : State V B K} (p : Step s) : Run s p.next 1 :=
  Run.step (Run.refl s) p

theorem Run.trans {B C D : ℕ} {s : State V B K} {t : State V C K} {u : State V D K}
    {j k : ℕ} (p : Run s t j) (q : Run t u k) : Run s u (j+k) := by
  induction q with
  | refl => simpa only [Nat.add_zero] using p
  | step q a ih => simpa only [Nat.add_assoc] using Run.step (ih p) a

theorem Run.le {B C : ℕ} {s : State V B K} {t : State V C K} {j : ℕ} (p : Run s t j) :
    t.graph≤s.graph := by
  induction p with
  | refl => exact le_rfl
  | step p a ih => exact a.le.trans ih

theorem Run.maximum {B C : ℕ} {s : State V B K} {t : State V C K} {j : ℕ} (p : Run s t j) :
    t.graph.maxDegree+j=s.graph.maxDegree := by
  induction p with
  | refl => simp
  | step p a ih => have hh:=a.maximum;omega

theorem Run.budget_parameter {B C : ℕ} {s : State V B K} {t : State V C K} {j : ℕ} (p : Run s t j) :
    C+2*j=B := by
  induction p with
  | refl => omega
  | step p a ih => have hh:=a.budget_parameter_positive;omega

theorem Run.length_le_half_budget {B C : ℕ} {s : State V B K} {t : State V C K}
    {j : ℕ} (p : Run s t j) : 2*j≤B := by have hh:=p.budget_parameter;omega

theorem Run.margins {B C : ℕ} {s : State V B K} {t : State V C K} {j : ℕ}
    (p : Run s t j) (hM : Margins s) : Margins t := by
  induction p with
  | refl => exact hM
  | step p a ih => exact a.margins (ih hM)

theorem terminates (B : ℕ) (s : State V B K) (hM : Margins s) :
    ∃C : ℕ,∃t : State V C K,∃j : ℕ,Run s t j ∧ Terminal t := by
  induction B using Nat.strong_induction_on with
  | h B ih =>
    rcases terminal_or_step s hM with hTerminal|hStep
    · exact ⟨B,s,0,Run.refl s,hTerminal⟩
    · obtain ⟨p⟩:=hStep
      have hLt:B-2<B:=by have hh:=p.budget_parameter_positive;omega
      obtain ⟨C,t,j,hRun,hTerminal⟩:=ih (B-2) hLt p.next (p.margins hM)
      exact ⟨C,t,1+j,(Run.single p).trans hRun,hTerminal⟩

/-- Terminal existence and length bounds are constructed, rather than
being implications conditional on an assumed admissible run. -/
theorem exists_terminal_run {B : ℕ} (s : State V B K) (hM : Margins s) :
    ∃C : ℕ,∃t : State V C K,∃j : ℕ,Run s t j ∧ Terminal t ∧ Margins t ∧
      C+2*j=B ∧ t.graph.maxDegree+j=s.graph.maxDegree ∧ t.graph≤s.graph := by
  obtain ⟨C,t,j,hRun,hTerminal⟩:=terminates B s hM
  exact ⟨C,t,j,hRun,hTerminal,hRun.margins hM,hRun.budget_parameter,hRun.maximum,hRun.le⟩

end OverfullWork.NormalizedClassTwoStep
