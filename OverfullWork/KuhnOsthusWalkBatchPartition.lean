module

public import OverfullWork.KuhnOsthusWalkBatchHall
public import OverfullWork.KuhnOsthusWalkMatchOrdering

@[expose] public section


/-! Realize the exact loads of one fine pair in Lemma 9.5. The
prefix sums divide the edge order into consecutive matching windows.
The equivalence from Hall exhausts each window and avoids the
prescribed systems. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*}

/-- Integer positions of a batch are bounded by the corresponding
multiples of the smallest and largest batch sizes. -/
theorem walk_batch_position_bounds {b : ℕ} (load : Fin b → ℕ) (lo hi : ℕ)
    (hLo : ∀ i, lo ≤ load i) (hHi : ∀ i, load i ≤ hi)
    (a : Fin b) (j : Fin (load a)) :
    lo*a.val ≤ (finSigmaFinEquiv ⟨a,j⟩ : Fin (∑ i,load i)).val ∧
      (finSigmaFinEquiv ⟨a,j⟩ : Fin (∑ i,load i)).val < hi*(a.val+1) := by
  have hlo : lo*a.val ≤ ∑ i : Fin a.val,load (Fin.castLE a.isLt.le i) := by
    simpa [Nat.mul_comm] using
      (sum_le_sum (s := (univ : Finset (Fin a.val))) (fun i _ => hLo (Fin.castLE a.isLt.le i)))
  have hhi : (∑ i : Fin a.val,load (Fin.castLE a.isLt.le i)) ≤ hi*a.val := by
    simpa [Nat.mul_comm] using
      (sum_le_sum (s := (univ : Finset (Fin a.val))) (fun i _ => hHi (Fin.castLE a.isLt.le i)))
  rw [finSigmaFinEquiv_apply]
  dsimp only
  have hj := j.isLt.trans_le (hHi a)
  rw [Nat.mul_add,Nat.mul_one]
  omega

/-- For each fine successor pair, distribute all physical positions
to slots in batches of ten. Each matching uses exactly its prescribed
load and each arc position is consumed once. The two maps list the
sources and targets of the ordered physical reserve. -/
theorem exists_walk_pair_batch_partition {b : ℕ} (w : Fin b → Fin 10 → ℕ)
    (H : Fin b → Fin 10 → Finset V) (A B : Finset V) (s width : ℕ)
    (hLo : ∀ a i, 11*s ≤ w a i) (hHi : ∀ a i, w a i ≤ 13*s) (hWidth : 130*s ≤ width)
    (hDis : ∀ a i j, i ≠ j → Disjoint (H a i) (H a j))
    (hMeet : ∀ a i, (H a i ∩ A).card + (H a i ∩ B).card ≤ 2*s)
    (src dst : Fin (∑ a,∑ i, w a i) → V)
    (hSrc : ∀ p, src p ∈ A) (hDst : ∀ p, dst p ∈ B)
    (hWindow : ∀ p q, p.val < q.val → q.val < p.val+width →
      src p ≠ src q ∧ dst p ≠ dst q) :
    let load (a : Fin b) := ∑ i, w a i
    ∃ piece : ∀ a : Fin b, (Σ i : Fin 10, Fin (w a i)) ≃ Fin (load a),
      ∃ placement : (Σ a : Fin b, Σ i : Fin 10, Fin (w a i)) ≃ Fin (∑ a,load a),
        (∀ a i, placement ⟨a,i⟩ = finSigmaFinEquiv ⟨a,piece a i⟩) ∧
        (∀ a, Function.Injective (fun i => src (finSigmaFinEquiv ⟨a,i⟩)) ∧
          Function.Injective (fun i => dst (finSigmaFinEquiv ⟨a,i⟩))) ∧
        ∀ a i (j : Fin (w a i)), src (placement ⟨a,i,j⟩) ∉ H a i ∧
          dst (placement ⟨a,i,j⟩) ∉ H a i := by
  intro load
  have hLow (a : Fin b) : 110*s ≤ load a := by
    have h := sum_le_sum (s := (univ : Finset (Fin 10))) (fun i _ => hLo a i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at h
    change 110*s ≤ ∑ i, w a i
    nlinarith only [h]
  have hUp (a : Fin b) : load a ≤ 130*s := by
    have h := sum_le_sum (s := (univ : Finset (Fin 10))) (fun i _ => hHi a i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at h
    change (∑ i, w a i) ≤ 130*s
    nlinarith only [h]
  let pos (a : Fin b) (i : Fin (load a)) : Fin (∑ a,load a) := finSigmaFinEquiv ⟨a,i⟩
  have hOrd (a : Fin b) (i j : Fin (load a)) (h : i.val < j.val) :
      (pos a i).val < (pos a j).val ∧ (pos a j).val < (pos a i).val+width := by
    dsimp only [pos]
    rw [finSigmaFinEquiv_apply,finSigmaFinEquiv_apply]
    dsimp only
    have hj := j.isLt
    have hu := hUp a
    omega
  have hInj (a : Fin b) {f : Fin (∑ a,load a) → V}
      (hf : ∀ p q, p.val < q.val → q.val < p.val+width → f p ≠ f q) :
      Function.Injective (fun i => f (pos a i)) := by
    intro i j he
    by_contra hn
    rcases lt_or_gt_of_ne (fun hh : i.val = j.val => hn (Fin.ext hh)) with hh | hh
    · exact hf _ _ (hOrd a i j hh).1 (hOrd a i j hh).2 he
    · exact hf _ _ (hOrd a j i hh).1 (hOrd a j i hh).2 he.symm
  have hBatch (a : Fin b) : ∃ piece : (Σ i : Fin 10, Fin (w a i)) ≃ Fin (load a),
      ∀ p, src (pos a (piece p)) ∉ H a p.1 ∧ dst (pos a (piece p)) ∉ H a p.1 := by
    apply exists_walk_batch_arc_assignment (fun j => src (pos a j)) (fun j => dst (pos a j))
      (H a) (w a) A B (hInj a (fun p q hp hq => (hWindow p q hp hq).1))
      (hInj a (fun p q hp hq => (hWindow p q hp hq).2)) (fun j => hSrc (pos a j))
      (fun j => hDst (pos a j)) (hDis a) (2*s) (13*s) (26*s) (hHi a) (hMeet a)
    · exact (Fintype.card_fin _).symm
    · rw [Fintype.card_fin]
      have hh := hLow a
      omega
    · omega
    · omega
  choose piece hPiece using hBatch
  let place := (Equiv.sigmaCongrRight piece).trans finSigmaFinEquiv
  exact ⟨piece,place,fun _ _ => rfl,
    fun a => ⟨hInj a (fun p q hp hq => (hWindow p q hp hq).1),
      hInj a (fun p q hp hq => (hWindow p q hp hq).2)⟩,
    fun a i j => hPiece a ⟨i,j⟩⟩

end OverfullWork.DirectedRobustExpansion
