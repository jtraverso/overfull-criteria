module

public import OverfullWork.DenseHall

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Each removal loses one neighbor per row and column. Repeated use
of the dense Hall theorem therefore supplies the edge-disjoint candidate
matchings for the bipartite case of Barber–Kühn–Lo–Osthus–Taylor. -/
theorem exists_disjoint_perfect_matching_candidates (r : A → B → Prop) (d k : ℕ)
    (heq : Fintype.card A = Fintype.card B) (hsize : Fintype.card B ≤ 2*d)
    (hA : ∀ a, d+k ≤ (univ.filter (r a)).card)
    (hB : ∀ b, d+k ≤ (univ.filter (fun a => r a b)).card) :
    ∃ f : Fin (k+1) → (A ≃ B), (∀ i a, r a (f i a)) ∧
      ∀ i j, i ≠ j → ∀ a, f i a ≠ f j a := by
  induction k generalizing r with
  | zero =>
    obtain ⟨f,hf⟩ := DenseHall.exists_matching r d heq hsize
      (by simpa only [Nat.add_zero] using hA) (by simpa only [Nat.add_zero] using hB)
    exact ⟨fun _ => f,fun _ => hf,fun i j hne => (hne (Fin.ext (by omega))).elim⟩
  | succ k ih =>
    obtain ⟨f,hf⟩ := DenseHall.exists_matching r d heq hsize
      (fun a => (Nat.le_add_right _ _).trans (hA a))
      (fun b => (Nat.le_add_right _ _).trans (hB b))
    let r' (a : A) (b : B) := r a b ∧ f a ≠ b
    let _ : DecidableRel r' := fun _ _ => Classical.propDecidable _
    have ha (a : A) : d+k ≤ (univ.filter (r' a)).card := by
      have hSet : univ.filter (r' a) = (univ.filter (r a)).erase (f a) := by
        ext b
        simp only [r',mem_filter,mem_erase,mem_univ,true_and]
        constructor
        · rintro ⟨hr,hne⟩; exact ⟨hne.symm,hr⟩
        · rintro ⟨hne,hr⟩; exact ⟨hr,hne.symm⟩
      rw [hSet,card_erase_of_mem (mem_filter.mpr ⟨mem_univ _,hf a⟩)]
      have h := hA a
      omega
    have hb (b : B) : d+k ≤ (univ.filter (fun a => r' a b)).card := by
      have hSet : univ.filter (fun a => r' a b) =
          (univ.filter (fun a => r a b)).erase (f.symm b) := by
        ext a
        have hEq : f a = b ↔ a = f.symm b := f.eq_symm_apply.symm
        simp only [r',mem_filter,mem_erase,mem_univ,true_and,ne_eq,hEq]
        tauto
      have hf' : r (f.symm b) b := by simpa only [Equiv.apply_symm_apply] using hf (f.symm b)
      have hMem : f.symm b ∈ univ.filter (fun a => r a b) :=
        mem_filter.mpr ⟨mem_univ _,hf'⟩
      rw [hSet,card_erase_of_mem hMem]
      have h := hB b
      omega
    obtain ⟨g,hg,hDisjoint⟩ := ih r' ha hb
    refine ⟨Fin.cons f g,?_,?_⟩
    · intro i
      refine Fin.cases hf (fun i a => ?_) i
      simpa only [Fin.cons_succ] using (hg i a).1
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases (fun hj => (hj rfl).elim) (fun j _ a => ?_) j
        simpa only [Fin.cons_zero,Fin.cons_succ] using (hg j a).2
      · intro j
        refine Fin.cases (fun _ a => ?_) (fun j hij a => ?_) j
        · simpa only [Fin.cons_zero,Fin.cons_succ] using (hg i a).2.symm
        · simpa only [Fin.cons_succ] using hDisjoint i j (fun h => hij (congrArg Fin.succ h)) a

/-- The options hitting a set inject into that set when the candidate
neighbors of the fixed vertex are distinct. -/
theorem candidate_hit_count_le {I X : Type*} [Fintype I] (f : I → X)
    (hf : Function.Injective f) (S : Finset X) :
    ((univ : Finset I).filter (fun i => f i ∈ S)).card ≤ S.card := by
  let emb : I ↪ X := ⟨f,hf⟩
  rw [← card_map emb]
  apply card_le_card
  intro v hv
  obtain ⟨i,hi,rfl⟩ := mem_map.mp hv
  exact (mem_filter.mp hi).2

/-- Distinct choices also give distinct neighbors on the opposite side. -/
theorem matching_candidate_inverse_injective {I : Type*} (f : I → (A ≃ B))
    (h : ∀ i j, i ≠ j → ∀ a, f i a ≠ f j a) (b : B) :
    Function.Injective (fun i => (f i).symm b) := by
  intro i j heq
  change (f i).symm b = (f j).symm b at heq
  by_contra hij
  apply h i j hij ((f i).symm b)
  change f i ((f i).symm b) = f j ((f i).symm b)
  rw [Equiv.apply_symm_apply,heq,Equiv.apply_symm_apply]

end OverfullWork.ChenShan
