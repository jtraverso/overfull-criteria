module

public import OverfullWork.DirectedRungCycle
public import OverfullWork.DirectedDisjointShortPaths
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section


/-! The connector step of Lo–Patel Theorem 4.11. Disjoint prescribed
rungs can all be embedded in a single directed cycle. -/
namespace OverfullWork.DirectedRungCycle

open Finset DirectedRobustExpansion DirectedRobustShortPaths DirectedListRoutes
open scoped Classical
variable {V : Type*} [Fintype V]

theorem rotate_order {m : ℕ} {R : Fin (m+1) → Fin (m+1) → Prop}
    (h : ∀ i, R i (finRotate (m+1) i)) :
    (List.ofFn (id : Fin (m+1) → Fin (m+1)) ++ [0]).IsChain R := by
  have hWord : List.ofFn (Fin.snoc (id : Fin (m+1) → Fin (m+1)) 0) =
      List.ofFn (id : Fin (m+1) → Fin (m+1)) ++ [0] := by
    simpa [List.concat_eq_append] using List.ofFn_succ' (Fin.snoc (id : Fin (m+1) → Fin (m+1)) 0)
  rw [← hWord, List.isChain_ofFn]
  · intro i hi
    have hilt : i < m+1 := by omega
    let j : Fin (m+1) := ⟨i, hilt⟩
    have hfirst : (⟨i, by omega⟩ : Fin (m+2)) = j.castSucc := rfl
    rw [hfirst, Fin.snoc_castSucc]
    by_cases hl : j = Fin.last m
    · have hh : (⟨i+1, hi⟩ : Fin (m+2)) = Fin.last (m+1) := by
        apply Fin.ext
        have he := congrArg Fin.val hl
        simpa [j] using congrArg Nat.succ he
      rw [hh, Fin.snoc_last, hl]
      simpa only [finRotate_last, id_eq] using h (Fin.last m)
    · have hnext : (finRotate (m+1) j).val = i+1 :=
        coe_finRotate_of_ne_last hl
      have he : (⟨i+1, hi⟩ : Fin (m+2)) = (finRotate (m+1) j).castSucc := Fin.ext hnext.symm
      rw [he, Fin.snoc_castSucc]
      exact h j

/-- Join all rung ends to the subsequent starts, reserving `M`
throughout. The returned cyclic order is the natural order on the
rungs. The upper bound includes the reserved set and every connector. -/
theorem exists_embedded_rung_cycle (D : Digraph V) {m r r' t L : ℕ}
    (hRobust : IsRobustAt D r t) (hr' : 0 < r') (hL : Fintype.card V/r'+4 ≤ L)
    (a b : Fin (m+1) → V) (body : Fin (m+1) → List V) (M : Finset V)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j, a i ≠ b j)
    (hSimple : ∀ i, (a i :: (body i ++ [b i])).Nodup)
    (hDisj : ∀ i j, i ≠ j → List.Disjoint (a i :: (body i ++ [b i])) (a j :: (body j ++ [b j])))
    (hMarks : ∀ i w, w ∈ a i :: (body i ++ [b i]) → w ∈ M)
    (hBudget : M.card+(m+1)*L+r' ≤ r)
    (hIn : ∀ v, t ≤ inDegree D v)
    (hOut : ∀ v, t+M.card+(m+1)*L ≤ outDegree D v) :
    ∃ link : Fin (m+1) → List V,
      ((List.ofFn (id : Fin (m+1) → Fin (m+1))) ++ [0]).IsChain
        (fun i j => Route D (b i) (a j) (link i ++ [a j])) ∧
      (word a b link body (List.ofFn id)).Nodup ∧
      (word a b link body (List.ofFn id)).length ≤ M.card+(m+1)*L := by
  classical
  let e := finRotate (m+1)
  obtain ⟨paths, hPaths, hLinks⟩ := exists_disjoint_short_paths D hRobust hr' hL M b
    (a ∘ e) hb (ha.comp e.injective) (fun i j => (hab (e j) i).symm)
    (fun i => ⟨hMarks i _ (by simp), hMarks (e i) _ (by simp [Function.comp_apply])⟩)
    hIn univ ∅ (by simp) (by simpa using hBudget) (by simpa using hOut)
  let link := fun i => (paths i).dropLast
  have hTail : ∀ i, link i ++ [a (e i)] = paths i := by
    intro i
    have hp := (hPaths i (mem_univ i)).1.2
    cases h : paths i with
    | nil =>
      have hEq : b i = a (e i) := by simpa [h, Function.comp_apply] using hp
      exact False.elim (hab _ _ hEq.symm)
    | cons v vs =>
      change (paths i).dropLast ++ [a (e i)] = v :: vs
      rw [h]
      apply List.dropLast_append_getLast?
      simpa [h, Function.comp_apply] using hp
  have hR : ∀ i, Route D (b i) (a (e i)) (link i ++ [a (e i)]) := by
    intro i
    rw [hTail]
    exact (hPaths i (mem_univ i)).1
  have hSub : ∀ i, List.Sublist (link i) (b i :: paths i) :=
    fun i => (List.dropLast_sublist _).trans (List.sublist_cons_self _ _)
  have hAvoid : ∀ i w, w ∈ link i → w ∉ M := by
    intro i w hw hwM
    have hC := (hPaths i (mem_univ i)).2.2.2 w ((hSub i).subset hw) |>.2 hwM
    have hN := (hPaths i (mem_univ i)).2.1
    change w = b i ∨ w = a (e i) at hC
    rcases hC with hEq|hEq
    · subst w
      exact (List.nodup_cons.mp hN).1 ((List.dropLast_sublist _).subset hw)
    · subst w
      rw [← hTail i] at hN
      change ((b i :: link i) ++ [a (e i)]).Nodup at hN
      exact (List.nodup_append.mp hN).2.2 _ (List.mem_cons_of_mem _ hw) _ (by simp) rfl
  have hLinkSimple : ∀ i, (link i).Nodup :=
    fun i => ((hPaths i (mem_univ i)).2.1).sublist (hSub i)
  have hLinkDisj : ∀ i j, i ≠ j → List.Disjoint (link i) (link j) := by
    intro i j hij w hi hj
    exact hLinks i (mem_univ _) j (mem_univ _) hij ((hSub i).subset hi) ((hSub j).subset hj)
  let order := List.ofFn (id : Fin (m+1) → Fin (m+1))
  have hOrder : order.Nodup := List.nodup_ofFn.mpr Function.injective_id
  let rung := fun i => a i :: (body i ++ [b i])
  have hWord : (word a b link body order).Perm (order.flatMap rung ++ order.flatMap link) := by
    have hBlock : block a b link body = fun i => rung i ++ link i := by
      funext i
      simp [block, rung, List.append_assoc]
    rw [word, hBlock]
    exact (List.flatMap_append_perm order rung link).symm
  have hRungSimple : (order.flatMap rung).Nodup :=
    List.nodup_flatMap.mpr ⟨fun i _ => hSimple i, hOrder.imp (fun h => hDisj _ _ h)⟩
  have hLinksSimple : (order.flatMap link).Nodup :=
    List.nodup_flatMap.mpr ⟨fun i _ => hLinkSimple i, hOrder.imp (fun h => hLinkDisj _ _ h)⟩
  have hWordSimple : (word a b link body order).Nodup := by
    apply hWord.nodup_iff.mpr
    refine List.nodup_append.mpr ⟨hRungSimple, hLinksSimple, ?_⟩
    intro w hw z hz he
    subst z
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hw
    obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hz
    exact hAvoid j w hj (hMarks i w hi)
  refine ⟨link, rotate_order hR, hWordSimple, ?_⟩
  let C := (univ : Finset (Fin (m+1))).biUnion (fun i => (link i).toFinset)
  have hCeil : C.card ≤ (m+1)*L := by
    apply card_biUnion_le.trans
    have hEach : ∀ i, (link i).toFinset.card ≤ L :=
      fun i => (List.toFinset_card_le _).trans ((hSub i).length_le.trans (hPaths i (mem_univ i)).2.2.1)
    simpa using (sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin (m+1)))) => hEach i) :
      (∑ i : Fin (m+1), (link i).toFinset.card) ≤ ∑ _i : Fin (m+1), L)
  have hSubset : (word a b link body order).toFinset ⊆ M ∪ C := by
    intro w hw
    rcases List.mem_append.mp (hWord.mem_iff.mp (List.mem_toFinset.mp hw)) with hw|hw
    · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hw
      exact mem_union_left _ (hMarks i w hi)
    · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hw
      exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, List.mem_toFinset.mpr hi⟩)
  have hCard := (card_le_card hSubset).trans
    ((card_union_le M C).trans (Nat.add_le_add_left hCeil _))
  simpa only [List.toFinset_card_of_nodup hWordSimple] using hCard

end OverfullWork.DirectedRungCycle
