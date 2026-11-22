module

public import OverfullWork.KuhnOsthusSpanningSwitchCopies
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section


/-! The two orderings of the perfect matchings in Claim 1 of
Kühn–Osthus Lemma 10.3. The second ordering advances one position
around the same list of paths. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*}

def cycleAbsorberSwitchSlot (m : ℕ) : Fin m × Fin 2 ≃ Fin (2*m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))

theorem cycleAbsorberSwitchSlot_val {m : ℕ} (i : Fin m) (j : Fin 2) :
    (cycleAbsorberSwitchSlot m (i,j)).val = 2*i.val+j.val := by
  change j.val+2*i.val = 2*i.val+j.val
  omega

theorem cycleAbsorberSwitchSlot_next {m : ℕ} (i : Fin m) :
    finRotate (2*m) (cycleAbsorberSwitchSlot m (i,0)) = cycleAbsorberSwitchSlot m (i,1) := by
  have : NeZero (2*m) := ⟨by have := i.isLt; omega⟩
  have hOne : (1 : Fin (2*m)).val = 1 := by
    have hSize : 1 < 2*m := by have := i.isLt; omega
    exact Nat.mod_eq_of_lt hSize
  apply Fin.ext
  rw [finRotate_apply,Fin.add_def,cycleAbsorberSwitchSlot_val,cycleAbsorberSwitchSlot_val,hOne]
  simp only [Fin.val_zero,Fin.val_one,add_zero]
  rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]

/-- One of the two spanning families of switches. The chosen
matching uses the corresponding source and target of each slot. -/
structure OrderedSwitchCopies (G : Digraph V) (A B : Finset V) (m : ℕ)
    (order : Fin m × Fin 2 ≃ Fin (2*m)) where
  copies : Fin m × Fin 4 ↪ V
  source : Fin (2*m) ≃ A
  target : Fin (2*m) ≃ B
  source_zero : ∀ i, (source (order (i,0))).val = copies (i,0)
  source_one : ∀ i, (source (order (i,1))).val = copies (i,1)
  target_zero : ∀ i, (target (order (i,0))).val = copies (i,2)
  target_one : ∀ i, (target (order (i,1))).val = copies (i,3)
  cross : ∀ i (a b : Fin 2), G.Adj (source (order (i,a))) (target (order (i,b)))

theorem OrderedSwitchCopies.matching {G : Digraph V} {A B : Finset V} {m : ℕ}
    {order : Fin m × Fin 2 ≃ Fin (2*m)}
    (C : OrderedSwitchCopies G A B m order) (j : Fin (2*m)) :
    G.Adj (C.source j) (C.target j) := by
  obtain ⟨⟨i,a⟩,rfl⟩ := order.surjective j
  exact C.cross i a a

/-- Put the two edges of each selected matching in consecutive
positions of the indicated ordering. -/
noncomputable def OrderedSwitchCopies.of_spanning {G : Digraph V} {A B : Finset V} {m : ℕ}
    (order : Fin m × Fin 2 ≃ Fin (2*m)) (f : Fin m × Fin 4 ↪ V)
    (hPart : ∀ i, f (i,0) ∈ A ∧ f (i,1) ∈ A ∧ f (i,2) ∈ B ∧ f (i,3) ∈ B)
    (hEdges : ∀ i, G.Adj (f (i,0)) (f (i,2)) ∧ G.Adj (f (i,0)) (f (i,3)) ∧
      G.Adj (f (i,1)) (f (i,2)) ∧ G.Adj (f (i,1)) (f (i,3)))
    (hA : ∀ v ∈ A, ∃ i, f (i,0) = v ∨ f (i,1) = v)
    (hB : ∀ v ∈ B, ∃ i, f (i,2) = v ∨ f (i,3) = v) :
    OrderedSwitchCopies G A B m order := by
  let toA (p : Fin m × Fin 2) : A :=
    ⟨f (p.1,p.2.castLE (by decide)),by
      rcases p with ⟨i,a⟩
      fin_cases a
      · exact (hPart i).1
      · exact (hPart i).2.1⟩
  let toB (p : Fin m × Fin 2) : B :=
    ⟨f (p.1,p.2.natAdd 2),by
      rcases p with ⟨i,a⟩
      fin_cases a
      · exact (hPart i).2.2.1
      · exact (hPart i).2.2.2⟩
  have ha : Bijective toA := by
    refine ⟨?_,?_⟩
    · rintro ⟨i,a⟩ ⟨j,b⟩ he
      have hp := f.injective (congrArg (fun z : A => z.val) he)
      exact Prod.ext (congrArg (fun p : Fin m × Fin 4 => p.1) hp) (Fin.ext (congrArg (fun p : Fin m × Fin 4 => p.2.val) hp))
    · intro v
      obtain ⟨i,hi | hi⟩ := hA v.val v.prop
      · exact ⟨(i,0),Subtype.ext hi⟩
      · exact ⟨(i,1),Subtype.ext hi⟩
  have hb : Bijective toB := by
    refine ⟨?_,?_⟩
    · rintro ⟨i,a⟩ ⟨j,b⟩ he
      have hp := f.injective (congrArg (fun z : B => z.val) he)
      refine Prod.ext (congrArg (fun p : Fin m × Fin 4 => p.1) hp) (Fin.ext ?_)
      have hh := congrArg (fun p : Fin m × Fin 4 => p.2.val) hp
      change 2+a.val = 2+b.val at hh
      exact Nat.add_left_cancel hh
    · intro v
      obtain ⟨i,hi | hi⟩ := hB v.val v.prop
      · exact ⟨(i,0),Subtype.ext hi⟩
      · exact ⟨(i,1),Subtype.ext hi⟩
  let s := order.symm.trans (Equiv.ofBijective toA ha)
  let t := order.symm.trans (Equiv.ofBijective toB hb)
  refine ⟨f,s,t,?_,?_,?_,?_,?_⟩
  · intro i
    simp only [s,Equiv.trans_apply,Equiv.symm_apply_apply]
    rfl
  · intro i
    simp only [s,Equiv.trans_apply,Equiv.symm_apply_apply]
    rfl
  · intro i
    simp only [t,Equiv.trans_apply,Equiv.symm_apply_apply]
    rfl
  · intro i
    simp only [t,Equiv.trans_apply,Equiv.symm_apply_apply]
    rfl
  · intro i a b
    simp only [s,t,Equiv.trans_apply,Equiv.symm_apply_apply]
    fin_cases a <;> fin_cases b
    · exact (hEdges i).1
    · exact (hEdges i).2.1
    · exact (hEdges i).2.2.1
    · exact (hEdges i).2.2.2

end OverfullWork.DirectedRobustExpansion
