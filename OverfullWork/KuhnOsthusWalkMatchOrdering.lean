module

public import OverfullWork.KuhnOsthusWalkCut
public import Mathlib.Logic.Equiv.Set

@[expose] public section


/-! Consecutive perfect matchings in one quarter in Kühn–Osthus
Lemma 9.5. The prefix of each matching avoids the tail of the
previous one on both sides of the pair. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {A B : Type*} [Fintype A]

private theorem exists_enumeration_with_prefix (S : Finset A) (m w : ℕ)
    (hm : Fintype.card A = m) (hS : S.card = w) :
    ∃ enum : Fin m ≃ A, ∀ j, j.val < w → enum j ∈ S := by
  have hw : w ≤ m := hS ▸ hm ▸ card_le_univ S
  let l : Fin w ≃ {x // x ∈ S} :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe S).trans hS)).symm
  let r : Fin (m-w) ≃ {x // x ∉ S} := (Fintype.equivFinOfCardEq (by
    have hEquiv : {x // x ∉ S} ≃ ↥Sᶜ :=
      Equiv.subtypeEquivRight (fun x => (mem_compl (s := S) (a := x)).symm)
    rw [Fintype.card_congr hEquiv,Fintype.card_coe,card_compl,hm,hS])).symm
  let e : Fin w ⊕ Fin (m-w) ≃ Fin m :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hw))
  let enum := e.symm.trans ((l.sumCongr r).trans (Equiv.sumCompl (fun x => x ∈ S)))
  refine ⟨enum,?_⟩
  intro j hj
  let i : Fin w := ⟨j.val,hj⟩
  have he : e (Sum.inl i) = j := by
    apply Fin.ext
    change (finSumFinEquiv (Sum.inl i : Fin w ⊕ Fin (m-w))).val = j.val
    rw [finSumFinEquiv_apply_left]
    rfl
  have ht : e.symm j = Sum.inl i := e.symm_apply_eq.mpr he.symm
  change (Equiv.sumCompl (fun x => x ∈ S)) ((l.sumCongr r) (e.symm j)) ∈ S
  rw [ht]
  exact (l i).prop

private theorem exists_next_matching_enumeration (m w : ℕ) (hA : Fintype.card A = m)
    (hRoom : 3*w ≤ m) (p : Fin m ≃ A) (M N : A ≃ B) :
    ∃ q : Fin m ≃ A, ∀ i j, m-w ≤ i.val → j.val < w →
      p i ≠ q j ∧ M (p i) ≠ N (q j) := by
  let atTail (k : Fin w) : Fin m := ⟨m-w+k.val,by have := k.isLt; omega⟩
  let T := (univ : Finset (Fin w)).image (fun k => p (atTail k))
  let X := T ∪ T.image (fun a => N.symm (M a))
  have hT : T.card ≤ w := card_image_le.trans (by simp)
  have hX : X.card ≤ 2*w := by
    have hIm := card_image_le (s := T) (f := fun a => N.symm (M a))
    exact (card_union_le _ _).trans (by omega)
  have hGood : w ≤ Xᶜ.card := by rw [card_compl,hA]; omega
  obtain ⟨S,hSub,hSize⟩ := exists_subset_card_eq hGood
  obtain ⟨q,hq⟩ := exists_enumeration_with_prefix S m w hA hSize
  refine ⟨q,?_⟩
  intro i j hi hj
  let k : Fin w := ⟨i.val-(m-w),by have := i.isLt; omega⟩
  have hEq : atTail k = i := Fin.ext (by
    change m-w+(i.val-(m-w)) = i.val
    omega)
  have hIn : p i ∈ T := mem_image.mpr ⟨k,mem_univ _,congrArg p hEq⟩
  have hNot : q j ∉ X := mem_compl.mp (hSub (hq j hj))
  constructor
  · intro he
    exact hNot (mem_union_left _ (he ▸ hIn))
  · intro he
    exact hNot (mem_union_right _ (mem_image.mpr ⟨p i,hIn,N.symm_apply_eq.mpr he⟩))

/-- Inside a quarter, enumerate the perfect matchings one after
another so that the last window of each matching and the first
window of the next matching have disjoint endpoints. -/
theorem exists_walk_match_enumerations (m w : ℕ) (hA : Fintype.card A = m)
    (hRoom : 3*w ≤ m) {k : ℕ} (M : Fin k → A ≃ B) :
    ∃ enum : Fin k → Fin m ≃ A,
      ∀ a b, a.val+1 = b.val → ∀ i j, m-w ≤ i.val → j.val < w →
        enum a i ≠ enum b j ∧ M a (enum a i) ≠ M b (enum b j) := by
  classical
  induction k with
  | zero => exact ⟨Fin.elim0,fun a => a.elim0⟩
  | succ k ih =>
    obtain ⟨L,hL⟩ := ih (fun j : Fin k => M j.castSucc)
    have chooseLast : ∃ q : Fin m ≃ A, ∀ a : Fin k, a.val+1 = k →
        ∀ i j, m-w ≤ i.val → j.val < w →
          L a i ≠ q j ∧ M a.castSucc (L a i) ≠ M (Fin.last k) (q j) := by
      by_cases hk : k = 0
      · subst k
        exact ⟨(Fintype.equivFinOfCardEq hA).symm,fun a => a.elim0⟩
      · let a : Fin k := ⟨k-1,by omega⟩
        obtain ⟨q,hq⟩ := exists_next_matching_enumeration m w hA hRoom (L a)
          (M a.castSucc) (M (Fin.last k))
        refine ⟨q,fun i hi => ?_⟩
        have he : i = a := Fin.ext (by change i.val = k-1; omega)
        subst i
        exact hq
    obtain ⟨q,hq⟩ := chooseLast
    refine ⟨Fin.snoc L q,?_⟩
    intro a b
    refine Fin.lastCases (fun h => ?_) (fun b h => ?_) b
    · revert h
      refine Fin.lastCases (fun h => ?_) (fun a h => ?_) a
      · exfalso
        exact Nat.succ_ne_self k h
      · simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hq a h
    · revert h
      refine Fin.lastCases (fun h => ?_) (fun a h => ?_) a
      · exfalso
        have hb := b.isLt
        change k+1 = b.val at h
        omega
      · simpa only [Fin.snoc_castSucc] using hL a b h

/-- The contiguous ordering of all perfect matchings in a quarter
has no repeated source or target in any window of length at most
the prescribed width. -/
theorem exists_walk_quarter_ordering (m w : ℕ) (hA : Fintype.card A = m)
    (hRoom : 3*w ≤ m) {k : ℕ} (M : Fin k → A ≃ B) :
    ∃ order : Fin (k*m) ≃ Fin k × A,
      ∀ p q, p.val < q.val → q.val < p.val+w →
        (order p).2 ≠ (order q).2 ∧
          M (order p).1 (order p).2 ≠ M (order q).1 (order q).2 := by
  obtain ⟨enum,hEnum⟩ := exists_walk_match_enumerations m w hA hRoom M
  let e : Fin (k*m) ≃ Fin k × Fin m := finProdFinEquiv.symm
  let order := e.trans (Equiv.prodCongrRight enum)
  have hVal (p : Fin (k*m)) : p.val = (e p).2.val+m*(e p).1.val := by
    exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply p).symm
  refine ⟨order,?_⟩
  intro p q hpq hq
  let a := (e p).1
  let b := (e q).1
  let i := (e p).2
  let j := (e q).2
  have hpVal : p.val = i.val+m*a.val := hVal p
  have hqVal : q.val = j.val+m*b.val := hVal q
  change enum a i ≠ enum b j ∧ M a (enum a i) ≠ M b (enum b j)
  by_cases he : a = b
  · have hNe : i ≠ j := by
      intro h
      rw [he,h] at hpVal
      omega
    rw [← he]
    have hNe' : i ≠ (e q).2 := hNe
    exact ⟨fun h => hNe' ((enum a).injective h),
      fun h => hNe' ((enum a).injective ((M a).injective h))⟩
  · have ha : a.val < b.val := by
      by_contra! hn
      have hne : a.val ≠ b.val := fun h => he (Fin.ext h)
      have hh : b.val+1 ≤ a.val := by omega
      have hm := Nat.mul_le_mul_left m hh
      rw [Nat.mul_add,Nat.mul_one] at hm
      have := j.isLt
      omega
    have hab : a.val+1 = b.val := by
      by_contra! hn
      have hb : a.val+2 ≤ b.val := by omega
      have hm := Nat.mul_le_mul_left m hb
      rw [Nat.mul_add,Nat.mul_two] at hm
      have := i.isLt
      omega
    have hEl : j.val+m < i.val+w := by
      rw [←hab,Nat.mul_add,Nat.mul_one] at hqVal
      omega
    have hi : m-w ≤ i.val := by omega
    have hj : j.val < w := by have := i.isLt; omega
    exact hEnum a b hab i j hi hj

end OverfullWork.DirectedRobustExpansion
