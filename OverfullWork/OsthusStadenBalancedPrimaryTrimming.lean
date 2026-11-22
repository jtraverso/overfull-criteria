module

public import OverfullWork.OsthusStadenRequestSplit

@[expose] public section


/-! Distribute the optional deletions of §5.3 while retaining the
occurrence budget needed in Claim 5.4. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

set_option maxHeartbeats 1050000 in
/-- Enlarge each set of mandatory deletions to a prescribed size. The
additional removals can be spread so that no vertex is used more than
cap times. The total-capacity inequality leaves enough choices at
each step even when the mandatory sets are different. -/
theorem exists_balanced_required_deletions
    {T W : Type*} [Fintype T] [Fintype W] (required : T → Finset W) (count cap : ℕ)
    (hCount : count ≤ Fintype.card W) (hCap : 0 < cap)
    (hRequired : ∀ t, (required t).card ≤ count)
    (hRoom : Fintype.card T*count ≤ cap*(Fintype.card W-count)) :
    ∃ removed : T → Finset W,
      (∀ t, required t ⊆ removed t ∧ (removed t).card = count) ∧
      (∀ x, ((univ : Finset T).filter (fun t => x ∈ removed t \ required t)).card ≤ cap) ∧
      ∀ x, ((univ : Finset T).filter (fun t => x ∈ removed t)).card ≤
        ((univ : Finset T).filter (fun t => x ∈ required t)).card+cap := by
  have hConstruct (S : Finset T) :
      ∃ fill : T → Finset W,
        (∀ t ∈ S, Disjoint (fill t) (required t) ∧ (fill t).card = count-(required t).card) ∧
        ∀ x : W, (S.filter (fun t => x ∈ fill t)).card ≤ cap := by
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => ∅,by simp,by simp⟩
    | @insert t S ht ih =>
      obtain ⟨fill,hFill,hLoad⟩ := ih
      let load (x : W) := (S.filter (fun q => x ∈ fill q)).card
      let saturated := (univ : Finset W).filter (fun x => cap ≤ load x)
      have hCountSum : ∑ x : W, load x = ∑ q ∈ S,(fill q).card := by
        dsimp only [load]
        simp only [card_filter]
        rw [sum_comm]
        exact sum_congr rfl (fun q _ => by rw [←card_filter,filter_mem_eq_inter,univ_inter])
      have hSat : saturated.card ≤ Fintype.card W-count := by
        have hLo : cap*saturated.card ≤ ∑ x ∈ saturated, load x := by
          calc
            cap*saturated.card = ∑ _ ∈ saturated, cap := by simp [Nat.mul_comm]
            _ ≤ _ := sum_le_sum (fun _ hx => (mem_filter.mp hx).2)
        have hLS : (∑ x ∈ saturated,load x) ≤ ∑ x : W,load x :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
        have hMax : (∑ q ∈ S,(fill q).card) ≤ S.card*count := by
          calc
            (∑ q ∈ S,(fill q).card) ≤ ∑ _ ∈ S, count :=
              sum_le_sum (fun q hq => ((hFill q hq).2).le.trans (Nat.sub_le _ _))
            _ = S.card*count := by simp
        have h := hLo.trans (hLS.trans (hCountSum.trans_le
          (hMax.trans ((Nat.mul_le_mul_right _ (card_le_univ S)).trans hRoom))))
        exact Nat.le_of_mul_le_mul_left h hCap
      let free := (required t ∪ saturated)ᶜ
      have hFree : count-(required t).card ≤ free.card := by
        have hUnion := card_union_le (required t) saturated
        unfold free
        rw [card_compl]
        omega
      obtain ⟨extra,hExtra,hSize⟩ := exists_subset_card_eq hFree
      have hExtraDis : Disjoint extra (required t) :=
        disjoint_left.mpr (fun x hx hx' => (mem_compl.mp (hExtra hx)) (mem_union_left _ hx'))
      have hUnsat (x : W) (hx : x ∈ extra) : load x < cap :=
        lt_of_not_ge fun hc => (mem_compl.mp (hExtra hx)) (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hc⟩))
      let fill' (q : T) := if q = t then extra else fill q
      refine ⟨fill',?_,?_⟩
      · intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · simpa only [fill',if_pos rfl] using ⟨hExtraDis,hSize⟩
        · have hne : q ≠ t := fun he => ht (he ▸ hq)
          simpa only [fill',if_neg hne] using hFill q hq
      · intro x
        by_cases hx : x ∈ extra
        · have he : ((insert t S).filter (fun q => x ∈ fill' q)) =
              insert t (S.filter (fun q => x ∈ fill q)) := by
              ext q
              by_cases hq : q = t
              · subst q
                simp [fill',hx]
              · simp [fill',hq]
          rw [he,card_insert_of_notMem (fun h => ht (mem_filter.mp h).1)]
          exact Nat.succ_le_of_lt (hUnsat x hx)
        · have he : ((insert t S).filter (fun q => x ∈ fill' q)) = S.filter (fun q => x ∈ fill q) := by
              ext q
              by_cases hq : q = t
              · subst q
                simp [fill',hx,ht]
              · simp [fill',hq]
          rw [he]
          exact hLoad x
  obtain ⟨fill,hFill,hLoad⟩ := hConstruct univ
  let removed (t : T) := required t ∪ fill t
  have hDiff (t : T) : removed t \ required t = fill t := by
    ext x
    simp only [removed,mem_sdiff,mem_union]
    by_cases hx : x ∈ required t
    · have hy : x ∉ fill t := fun h => disjoint_left.mp (hFill t (mem_univ _)).1 h hx
      simp [hx,hy]
    · simp [hx]
  refine ⟨removed,?_,fun x => by simpa only [hDiff] using hLoad x,?_⟩
  · intro t
    refine ⟨subset_union_left,?_⟩
    dsimp only [removed]
    rw [card_union_of_disjoint (hFill t (mem_univ _)).1.symm,(hFill t (mem_univ _)).2]
    have := hRequired t
    omega
  · intro x
    have he : ((univ : Finset T).filter (fun t => x ∈ removed t)) =
        (univ.filter (fun t => x ∈ required t)) ∪ (univ.filter (fun t => x ∈ fill t)) := by
      ext t
      simp only [removed,mem_filter,mem_univ,true_and,mem_union]
    rw [he]
    exact (card_union_le _ _).trans (Nat.add_le_add_left (hLoad x) _)

end OverfullWork.DirectedRobustExpansion
