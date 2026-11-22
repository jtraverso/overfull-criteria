module

public import OverfullWork.KuhnOsthusSubclusterWalk
public import OverfullWork.KuhnOsthusCompatibleOrdering

@[expose] public section


/-! Put the positions of a spanning cycle in ordinary cyclic
coordinates, including the last-to-first transition. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {W I : Type*} [Fintype W] [Fintype I]

private theorem finCongr_finRotate {a b : ℕ} (h : a = b) (i : Fin a) :
    finCongr h (finRotate a i) = finRotate b (finCongr h i) := by
  subst b
  rfl

/-- Number the vertices of a spanning cycle in their cyclic order. -/
theorem exists_fin_cyclic_order {R : W → W → Prop} (h : HasSpanningCycle R) :
    ∃ order : Fin (Fintype.card W) ≃ W,
      ∀ i, R (order i) (order (finRotate _ i)) := by
  obtain ⟨T,x,hN,hAll,hHead,hChain⟩ := h
  cases T with
  | nil => simp at hHead
  | cons a L =>
    have hax : a = x := by simpa using hHead
    subst x
    let T := a :: L
    let e : Fin (L.length+1) ≃ W := Equiv.ofBijective (fun i => T[i.val]'(by simpa [T] using i.isLt))
      ⟨by
        intro i j he
        apply Fin.ext
        exact congrArg Fin.val ((List.nodup_iff_injective_get.mp hN) he),
       by
        intro v
        obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (hAll v)
        exact ⟨⟨i,hi⟩,he⟩⟩
    have hSize : L.length+1 = Fintype.card W := by
      simpa only [Fintype.card_fin] using Fintype.card_congr e
    have hStep (i : Fin (L.length+1)) : R (e i) (e (finRotate _ i)) := by
      have hi : i.val+1 < (T++[a]).length := by
        simp only [List.length_append,T,List.length_cons]
        have := i.isLt
        omega
      have hs := (List.isChain_iff_getElem.mp hChain) i.val hi
      change R ((T++[a])[i.val]'(by simp [T])) ((T++[a])[i.val+1]'hi) at hs
      rw [List.getElem_append_left (show i.val < T.length from i.isLt)] at hs
      change R (T[i.val]'(i.isLt))
        (T[(finRotate (L.length+1) i).val]'((finRotate (L.length+1) i).isLt))
      by_cases hLast : i = Fin.last L.length
      · subst i
        rw [finRotate_last]
        rw [List.getElem_append_right (show T.length ≤ (Fin.last L.length).val+1 from le_rfl)] at hs
        simpa only [T,Fin.val_last,Fin.val_zero,List.length_cons,Nat.sub_self,List.getElem_cons_zero] using hs
      · have hv : (finRotate _ i).val = i.val+1 := coe_finRotate_of_ne_last hLast
        rw [List.getElem_append_left (show i.val+1 < T.length by
          change i.val+1 < L.length+1
          rw [←hv]
          exact (finRotate _ i).isLt)] at hs
        simpa only [hv] using hs
    refine ⟨(finCongr hSize.symm).trans e,?_⟩
    intro i
    simp only [Equiv.trans_apply,finCongr_finRotate]
    exact hStep _

/-- A numbered universal walk projects to the prescribed coarse
arcs and visits each coarse vertex exactly once for every factor. -/
theorem exists_indexed_universal_walk {L : ℕ} (F : Fin L → Equiv.Perm I)
    (hWalk : HasSpanningCycle (fun e f : (Σ _ : Fin L, I) => F e.1 e.2 = f.2)) :
    let q := L*Fintype.card I
    ∃ order : Fin q ≃ Fin L × I,
      (∀ i, (order (finRotate q i)).2 = F (order i).1 (order i).2) ∧
      ∀ x, (finiteSatisfying (fun i => (order i).2 = x)).card = L := by
  intro q
  obtain ⟨e,he⟩ := exists_fin_cyclic_order hWalk
  let t := Equiv.sigmaEquivProd (Fin L) I
  have ht : Fintype.card (Σ _ : Fin L, I) = q := by
    simpa only [q,Fintype.card_prod,Fintype.card_fin] using Fintype.card_congr t
  have hStep (i : Fin q) :
      F ((finCongr ht.symm).trans (e.trans t) i).1 ((finCongr ht.symm).trans (e.trans t) i).2 =
      ((finCongr ht.symm).trans (e.trans t) (finRotate q i)).2 := by
    simp only [Equiv.trans_apply,finCongr_finRotate]
    exact he (finCongr ht.symm i)
  let order : Fin q ≃ Fin L × I := (finCongr ht.symm).trans (e.trans t)
  refine ⟨order,fun i => (hStep i).symm,?_⟩
  intro x
  have hCard : (finiteSatisfying (fun i => (order i).2 = x)).card =
      (univ : Finset (Fin L)).card := by
    apply card_bij (fun i _ => (order i).1)
    · exact fun _ _ => mem_univ _
    · intro i hi j hj he'
      apply order.injective
      refine Prod.ext he' ?_
      exact ((mem_finiteSatisfying (p := fun i => (order i).2 = x)).mp hi).trans
        ((mem_finiteSatisfying (p := fun i => (order i).2 = x)).mp hj).symm
    · intro a _
      refine ⟨order.symm (a,x),mem_finiteSatisfying.mpr ?_,?_⟩
      · exact congrArg Prod.snd (order.apply_symm_apply (a,x))
      · exact congrArg Prod.fst (order.apply_symm_apply (a,x))
  simpa only [card_univ,Fintype.card_fin] using hCard

end OverfullWork.DirectedRobustExpansion
