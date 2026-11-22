module

public import OverfullWork.HamiltonBlockAssembly
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section


/-! Account for the whole regular residue after removing a Hamilton
packing, and assemble a decomposition when the residue is covered. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

theorem matchingUnion_exact_semidegrees {k : ℕ} (P : Fin k → Equiv.Perm V)
    (hDis : ∀ i j, i ≠ j → ∀ v, P i v ≠ P j v) (v : V) :
    inDegree (matchingUnion P) v = k ∧ outDegree (matchingUnion P) v = k := by
  have hIn : Function.Injective (fun i => (P i).symm v) := by
    intro i j h
    by_contra hn
    exact hDis i j hn ((P i).symm v) ((P i).apply_symm_apply v |>.trans
      ((congrArg (P j) h).trans ((P j).apply_symm_apply v)).symm)
  have hOut : Function.Injective (fun i => P i v) := fun i j he => by
    by_contra hn
    exact hDis i j hn v he
  let A := (univ : Finset (Fin k)).image (fun i => (P i).symm v)
  let B := (univ : Finset (Fin k)).image (fun i => P i v)
  have hi : inDegree (matchingUnion P) v = A.card := by
    unfold inDegree inNeighbours
    congr 1
    ext w
    simp [A,matchingUnion,← Equiv.eq_symm_apply,eq_comm (a := w)]
  have ho : outDegree (matchingUnion P) v = B.card := by
    unfold outDegree
    congr 1
    ext w
    letI : DecidablePred (fun w => (matchingUnion P).Adj v w) := Classical.decPred _
    rw [mem_filter]
    simp [B,matchingUnion]
  rw [hi,ho]
  simp only [A,B,card_image_of_injective _ hIn,card_image_of_injective _ hOut,card_univ,Fintype.card_fin,
    and_self]

theorem regular_residue_of_spanning_pack (D : Digraph V) (r : ℕ) {k : ℕ}
    (P : Fin k → Equiv.Perm V) (hReg : ∀ v, inDegree D v = r ∧ outDegree D v = r)
    (hAdj : ∀ i v, D.Adj v (P i v))
    (hDis : ∀ i j, i ≠ j → ∀ v, P i v ≠ P j v) (v : V) :
    inDegree (D \ matchingUnion P) v = r-k ∧ outDegree (D \ matchingUnion P) v = r-k := by
  have hLe : matchingUnion P ≤ D := by rintro x y ⟨i,rfl⟩; exact hAdj i x
  obtain ⟨hi,ho⟩ := matchingUnion_exact_semidegrees P hDis v
  obtain ⟨hPayI,hPayO⟩ := residual_semidegrees D (matchingUnion P) hLe v
  rw [hi,(hReg v).1] at hPayI
  rw [ho,(hReg v).2] at hPayO
  omega

noncomputable def hamilton_decomposition_of_pack_and_residue (D : Digraph V) (r : ℕ) {k : ℕ}
    (hk : k ≤ r) (P : Fin k → Equiv.Perm V) (Q : Fin (r-k) → Equiv.Perm V)
    (hr : ∀ v, outDegree D v = r)
    (hAdj : ∀ i v, D.Adj v (P i v))
    (hRes : ∀ i v, (D \ matchingUnion P).Adj v (Q i v))
    (hPDis : ∀ i j, i ≠ j → ∀ v, P i v ≠ P j v)
    (hQDis : ∀ i j, i ≠ j → ∀ v, Q i v ≠ Q j v)
    (hP : ∀ i, HasSpanningCycle (fun x y => P i x = y))
    (hQ : ∀ i, HasSpanningCycle (fun x y => Q i x = y)) :
    DirectedHamiltonDecomposition D r := by
  let e : (Fin k ⊕ Fin (r-k)) ≃ Fin r :=
    finSumFinEquiv.trans (finCongr (by omega))
  let F : Fin r → Equiv.Perm V := fun j => Sum.elim P Q (e.symm j)
  apply hamilton_decomposition_of_full_pack D r F hr
  · intro j v
    cases h : e.symm j with
    | inl i => simpa [F,h] using hAdj i v
    | inr i => simpa [F,h] using (hRes i v).1
  · intro i j hij v he
    have hn : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    cases hi : e.symm i with
    | inl a =>
      cases hj : e.symm j with
      | inl b =>
        exact hPDis a b (fun e => hn (hi.trans ((congrArg Sum.inl e).trans hj.symm))) v
          (by simpa [F,hi,hj] using he)
      | inr b => exact (hRes b v).2 ⟨a,by simpa [F,hi,hj] using he⟩
    | inr a =>
      cases hj : e.symm j with
      | inl b => exact (hRes a v).2 ⟨b,by simpa [F,hi,hj] using he.symm⟩
      | inr b =>
        exact hQDis a b (fun e => hn (hi.trans ((congrArg Sum.inr e).trans hj.symm))) v
          (by simpa [F,hi,hj] using he)
  · intro j
    cases h : e.symm j with
    | inl i => simpa [F,h] using hP i
    | inr i => simpa [F,h] using hQ i

end OverfullWork.DirectedRobustExpansion
