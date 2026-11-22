module

public import OverfullWork.DirectedPrefactorReach
public import Mathlib.GroupTheory.Perm.Cycle.Basic

@[expose] public section


/-! Local path invariants for the extensions in Lo–Patel Theorem 5.3.
The forward trace starts at the origin. The backward trace starts at
the terminus. These traces agree until an endpoint of a changed arc. -/
namespace OverfullWork.DirectedPrefactor
open Function Finset
open scoped Classical
variable {V : Type*} {D : Digraph V} {x : V}

private theorem iterate_agrees {f g : V → V} (v : V) (k : ℕ)
    (h : ∀ i < k, g (f^[i] v)=f (f^[i] v)) :
    ∀ i ≤ k, g^[i] v=f^[i] v := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    rw [iterate_succ_apply',iterate_succ_apply',ih (by omega)]
    exact h i (by omega)

theorem successor_extend_same (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (ha : D.Adj (terminus F) z) (v : V)
    (hOld : v ≠ terminus F) (hNew : v ≠ F.successor.symm z) :
    (extend F z hz ha).successor v=F.successor v := by
  classical
  change Equiv.swap x z (F.successor v)=F.successor v
  rw [Equiv.swap_apply_of_ne_of_ne]
  · intro h
    exact hOld (F.successor.symm_apply_eq.mpr h.symm).symm
  · intro h
    exact hNew (F.successor.symm_apply_eq.mpr h.symm).symm

theorem extend_preserves_prefix (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (ha : D.Adj (terminus F) z) (k : ℕ)
    (hOld : ∀ i < k, (F.successor : V → V)^[i] x ≠ terminus F)
    (hNew : ∀ i < k, (F.successor : V → V)^[i] x ≠ F.successor.symm z) :
    ∀ i ≤ k, ((extend F z hz ha).successor : V → V)^[i] x =
      (F.successor : V → V)^[i] x :=
  iterate_agrees x k fun i hi => successor_extend_same F z hz ha _ (hOld i hi) (hNew i hi)

theorem extend_preserves_backward_trace (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (ha : D.Adj (terminus F) z) (k : ℕ)
    (hOrig : ∀ i < k, (F.successor.symm : V → V)^[i] (terminus F) ≠ x)
    (hCut : ∀ i < k, (F.successor.symm : V → V)^[i] (terminus F) ≠ z) :
    ∀ i ≤ k, ((extend F z hz ha).successor.symm : V → V)^[i] (terminus F) =
      (F.successor.symm : V → V)^[i] (terminus F) :=
  iterate_agrees (terminus F) k fun i hi =>
    predecessor_extend_same F z hz ha _ (hOrig i hi) (hCut i hi)

/-- Cycles avoiding the two altered outgoing arcs have exactly the same
forward traversal in the old and new permutations. -/
theorem extend_preserves_disjoint_cycle (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (ha : D.Adj (terminus F) z) (v : V)
    (hOld : ¬F.successor.SameCycle v (terminus F))
    (hNew : ¬F.successor.SameCycle v (F.successor.symm z)) :
    ∀ i : ℕ, ((extend F z hz ha).successor : V → V)^[i] v =
      (F.successor : V → V)^[i] v := by
  intro i
  apply iterate_agrees v i _ i le_rfl
  intro j hj
  apply successor_extend_same F z hz ha
  · intro h
    have hc : F.successor.SameCycle v ((F.successor ^ j) v) :=
      Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
    exact hOld (by simpa only [Equiv.Perm.coe_pow,h] using hc)
  · intro h
    have hc : F.successor.SameCycle v ((F.successor ^ j) v) :=
      Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
    exact hNew (by simpa only [Equiv.Perm.coe_pow,h] using hc)

theorem protected_prefix_survives {B : Prefactor D x → Finset V} {F₀ F : Prefactor D x}
    {steps : ℕ} (hReach : Reach B F₀ steps F) (k : ℕ)
    (hOpen : ∀ i < k,(F₀.successor : V → V)^[i] x ≠ terminus F₀)
    (hProtect : ∀ G : Prefactor D x,∀ i < k,(G.successor : V → V)^[i] x ∈ B G) :
    (∀ i ≤ k,(F.successor : V → V)^[i] x=(F₀.successor : V → V)^[i] x) ∧
      ∀ i < k,(F.successor : V → V)^[i] x ≠ terminus F := by
  induction hReach with
  | zero => exact ⟨fun _ _ => rfl,hOpen⟩
  | keep _ ih => exact ih
  | @step _ G _ z hz ha hAvoid ih =>
    have hNew : ∀ i < k,(G.successor : V → V)^[i] x ≠ G.successor.symm z := by
      intro i hi he
      exact hAvoid (he ▸ hProtect G i hi)
    have hEq := extend_preserves_prefix G z hz ha k ih.2 hNew
    refine ⟨fun i hi => (hEq i hi).trans (ih.1 i hi),?_⟩
    intro i hi
    rw [hEq i hi.le,terminus_extend]
    exact hNew i hi

end OverfullWork.DirectedPrefactor
