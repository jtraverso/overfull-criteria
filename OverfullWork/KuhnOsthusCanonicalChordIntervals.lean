module

public import OverfullWork.KuhnOsthusResidueAssignment
public import OverfullWork.KuhnOsthusWindingIntervalGeometry

@[expose] public section


/-! The two canonical interval partitions in Kühn–Osthus Lemma 9.7
are nested. Every larger interval contains the same number of
smaller half-open intervals. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V S : Type*} [Fintype V] [Fintype S]

/-- Label the canonical half-open intervals of sizes `u*v` and
`v` in the same coordinates, and count the smaller intervals by
their larger owner. -/
theorem canonical_chord_interval_labels (g u v : ℕ) :
    let split : Fin ((g*u)*v) ≃ Fin (g*u) × Fin v := finProdFinEquiv.symm
    let sub : Fin (g*u) ≃ Fin g × Fin u := finProdFinEquiv.symm
    let owner (i : Fin (g*u)) := (sub i).1
    let coarse (j : Fin ((g*u)*v)) := owner (split j).1
    (∀ i j, coarse (intervalPosition i j) = owner i) ∧
    (∀ j, (coarse j).val = j.val/(u*v)) ∧
    ∀ a, (finiteSatisfying (fun i => owner i = a)).card = u := by
  intro split sub owner coarse
  refine ⟨fun i j => congrArg (fun p => owner p.1) (split.apply_symm_apply (i,j)),?_,?_⟩
  · intro j
    change j.val/v/u = j.val/(u*v)
    rw [Nat.div_div_eq_div_mul,Nat.mul_comm v u]
  · intro a
    have hCard : (finiteSatisfying (fun i => owner i = a)).card = (univ : Finset (Fin u)).card := by
      apply card_bij (fun i _ => (sub i).2)
      · exact fun _ _ => mem_univ _
      · intro i hi j hj he
        apply sub.injective
        exact Prod.ext (((mem_finiteSatisfying (p := fun i => owner i = a)).mp hi).trans
          ((mem_finiteSatisfying (p := fun i => owner i = a)).mp hj).symm) he
      · intro x _
        refine ⟨sub.symm (a,x),mem_finiteSatisfying.mpr ?_,?_⟩
        · exact congrArg Prod.fst (sub.apply_symm_apply (a,x))
        · exact congrArg Prod.snd (sub.apply_symm_apply (a,x))
    simpa only [card_univ,Fintype.card_fin] using hCard

/-- Instantiate the interval assignment for the canonical nested
partitions. The coarse tags in the matching partition are obtained
from the actual cluster of a vertex. -/
theorem assign_canonical_chord_exceptional_systems {g u v n t c cap : ℕ}
    [NeZero g] [NeZero n] (H : Digraph V) (cluster : V → Fin ((g*u)*v))
    (cell : Fin (g*u) × S → Finset V) (Q : Fin (g*u) × (S × Fin t) → Finset V)
    (hLarge : 802 ≤ g) (hn : 200 ≤ n) (ht : 300*t ≤ n) (hN : n = c*g.choose 2)
    (index : Fin n ≃ Fin (g*u) × (S × Fin t))
    (hOwn : ∀ j x, x ∈ cell j →
      ((finProdFinEquiv.symm (cluster x) : Fin (g*u) × Fin v)).1 = j.1)
    (hDis : ∀ i j, i ≠ j → Disjoint (cell i) (cell j))
    (hQ : ∀ e, Q e ⊆ cell (e.1,e.2.1) ∪ cell (finRotate (g*u) e.1,e.2.1)) :
    let split : Fin ((g*u)*v) ≃ Fin (g*u) × Fin v := finProdFinEquiv.symm
    let sub : Fin (g*u) ≃ Fin g × Fin u := finProdFinEquiv.symm
    let kind (x : V) := (sub (split (cluster x)).1).1
    ∀ P : OrderedResidueMatchings H kind n c cap 10,
    let F (i : Fin n) := finiteSatisfying (IncidentTo (P.matching i))
    ∃ assign : Fin n ≃ Fin (g*u) × (S × Fin t), (∀ i, Disjoint (F i) (Q (assign i))) ∧
      ∀ i j, residueCyclicClose 10 i j →
        Disjoint (F i ∪ Q (assign i)) (F j ∪ Q (assign j)) := by
  intro split sub kind P F
  let A (j : Fin (g*u)) := finiteSatisfying (fun x => (split (cluster x)).1 = j)
  let owner (j : Fin (g*u)) := (sub j).1
  have hA (j : Fin (g*u)) (x : V) (hx : x ∈ A j) : kind x = owner j :=
    congrArg owner ((mem_finiteSatisfying (p := fun x => (split (cluster x)).1 = j)).mp hx)
  have hFibre (j : Fin g) : (finiteSatisfying (fun i => owner i = j)).card ≤ u :=
    ((canonical_chord_interval_labels g u v).2.2 j).le
  have hCell (j : Fin (g*u) × S) : cell j ⊆ A j.1 := fun x hx => mem_finiteSatisfying.mpr (hOwn j x hx)
  have hCoarse : 200*g ≤ g.choose 2 := by
    have h := residue_spacing_ten_bound hLarge
    omega
  exact assign_exceptional_systems_to_ordered_residue P (finRotate (g*u)) A owner cell Q index u hn hN
    hCoarse (Nat.mul_le_mul_right u (by omega)) ht hA hFibre hCell hDis hQ

end OverfullWork.DirectedRobustExpansion
