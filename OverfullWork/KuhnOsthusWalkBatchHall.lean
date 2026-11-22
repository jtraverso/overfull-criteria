module

public import OverfullWork.KuhnOsthusCompatibleOrdering
public import OverfullWork.DenseHall

@[expose] public section


/-! The auxiliary graph in Kühn–Osthus Lemma 9.5 after (9.13).
The slots demand exact loads and every arc of the batch is used.
The prescribed ordinary footprints are disjoint within the batch. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {I E V : Type*} [Fintype I] [Fintype E]

private theorem card_slots_touching_vertex (H : I → Finset V) (w : I → ℕ) (a : ℕ)
    (hDis : ∀ i j, i ≠ j → Disjoint (H i) (H j)) (hW : ∀ i, w i ≤ a) (v : V) :
    (finiteSatisfying (fun p : Σ i, Fin (w i) => v ∈ H p.1)).card ≤ a := by
  let B := finiteSatisfying (fun i => v ∈ H i)
  have hB : B.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hne
    exact disjoint_left.mp (hDis i j hne)
      ((mem_finiteSatisfying (p := fun i => v ∈ H i)).mp hi)
      ((mem_finiteSatisfying (p := fun i => v ∈ H i)).mp hj)
  have hEq : finiteSatisfying (fun p : Σ i, Fin (w i) => v ∈ H p.1) =
      B.sigma (fun i => (univ : Finset (Fin (w i)))) := by
    ext p
    simp [B]
  rw [hEq,card_sigma]
  calc
    _ ≤ ∑ _ ∈ B,a := by
      apply sum_le_sum
      intro i _
      simpa only [card_univ,Fintype.card_fin] using hW i
    _ = B.card*a := by simp
    _ ≤ a := by simpa only [one_mul] using Nat.mul_le_mul_right a hB

private theorem filter_univ_eq_satisfying {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    (univ : Finset A).filter p = finiteSatisfying p := by
  ext x
  simp

private theorem remaining_slots {B : Type*} [Fintype B] (b : B → Prop) (n a : ℕ)
    (hB : Fintype.card B = n) (hBad : (finiteSatisfying b).card ≤ a) :
    n-a ≤ (finiteSatisfying (fun x => ¬ b x)).card := by
  have he : finiteSatisfying (fun x => ¬ b x) = (finiteSatisfying b)ᶜ := by
    ext x
    simp
  rw [he,card_compl,hB]
  omega

/-- Hall's two half-degree bounds, measured by the cardinalities
of the forbidden sets on the two sides. -/
private theorem exists_matching_of_forbidden_half {P : Type*} [Fintype P]
    (bad : P → E → Prop) (n a : ℕ) (hP : Fintype.card P = n) (hE : Fintype.card E = n)
    (ha : 2*a ≤ n)
    (hRow : ∀ p, (finiteSatisfying (bad p)).card ≤ a)
    (hCol : ∀ e, (finiteSatisfying (fun p => bad p e)).card ≤ a) :
    ∃ f : P ≃ E, ∀ p, ¬ bad p (f p) := by
  apply OverfullWork.DenseHall.exists_matching (fun p e => ¬ bad p e) (n-a)
    (hP.trans hE.symm) (by omega)
  · intro p
    rw [filter_univ_eq_satisfying]
    exact remaining_slots (bad p) n a hE (hRow p)
  · intro e
    rw [filter_univ_eq_satisfying]
    exact remaining_slots (fun p : P => bad p e) n a hP (hCol e)

/-- Assign all arcs in a matching-sized batch to precisely the
required slots. The endpoint ranges in the two cells are separately
injective, and the slot weights bound how many assignments each
endpoint can forbid. -/
theorem exists_walk_batch_arc_assignment (src dst : E → V)
    (H : I → Finset V) (w : I → ℕ) (A B : Finset V)
    (hs : Function.Injective src) (ht : Function.Injective dst)
    (hSrc : ∀ e, src e ∈ A) (hDst : ∀ e, dst e ∈ B)
    (hDis : ∀ i j, i ≠ j → Disjoint (H i) (H j))
    (s t a : ℕ) (hW : ∀ i, w i ≤ t)
    (hMeet : ∀ i, (H i ∩ A).card + (H i ∩ B).card ≤ s)
    (hTotal : ∑ i, w i = Fintype.card E)
    (hSize : 2*a ≤ Fintype.card E) (hS : s ≤ a) (hT : 2*t ≤ a) :
    ∃ assign : (Σ i, Fin (w i)) ≃ E,
      ∀ p, src (assign p) ∉ H p.1 ∧ dst (assign p) ∉ H p.1 := by
  let P := Σ i, Fin (w i)
  let bad (p : P) (e : E) := src e ∈ H p.1 ∨ dst e ∈ H p.1
  have hCard : Fintype.card P = Fintype.card E := by
    simpa only [P,Fintype.card_sigma,Fintype.card_fin] using hTotal
  have hRow (p : P) : (finiteSatisfying (bad p)).card ≤ a := by
    let L := finiteSatisfying (fun e => src e ∈ H p.1)
    let R := finiteSatisfying (fun e => dst e ∈ H p.1)
    have hU : finiteSatisfying (bad p) = L ∪ R := by
      ext e
      simp [bad,L,R]
    have hL : L.card ≤ (H p.1 ∩ A).card := card_le_card_of_injOn src
      (fun e he => mem_inter.mpr ⟨(mem_finiteSatisfying (p := fun e => src e ∈ H p.1)).mp he,hSrc e⟩)
      hs.injOn
    have hR : R.card ≤ (H p.1 ∩ B).card := card_le_card_of_injOn dst
      (fun e he => mem_inter.mpr ⟨(mem_finiteSatisfying (p := fun e => dst e ∈ H p.1)).mp he,hDst e⟩)
      ht.injOn
    rw [hU]
    exact (card_union_le _ _).trans ((Nat.add_le_add hL hR).trans ((hMeet p.1).trans hS))
  have hCol (e : E) : (finiteSatisfying (fun p => bad p e)).card ≤ a := by
    let L := finiteSatisfying (fun p : P => src e ∈ H p.1)
    let R := finiteSatisfying (fun p : P => dst e ∈ H p.1)
    have hU : finiteSatisfying (fun p => bad p e) = L ∪ R := by
      ext p
      simp [bad,L,R]
    rw [hU]
    have hL := card_slots_touching_vertex H w t hDis hW (src e)
    have hR := card_slots_touching_vertex H w t hDis hW (dst e)
    exact (card_union_le _ _).trans ((Nat.add_le_add hL hR).trans (by omega))
  obtain ⟨f,hf⟩ := exists_matching_of_forbidden_half bad _ a hCard rfl hSize hRow hCol
  exact ⟨f,fun p => not_or.mp (hf p)⟩

end OverfullWork.DirectedRobustExpansion
