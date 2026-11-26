module

public import OverfullWork.ChenShanMatchingPackingEdges

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*}

def matchingHit (W : Finset V) (v : V) (M : Finset (V × V)) : Prop :=
  v ∈ W ∧ ∃ w ∈ W, (v,w) ∈ M

noncomputable def matchingLoad (q i : ℕ) (W : Finset V) (M : ℕ → Finset (V × V))
    (v : V) : ℕ :=
  ((range q).filter (fun j => j ≠ i ∧ matchingHit W v (M j))).card

theorem matchingLoad_update {q k i : ℕ} (hk : k < q)
    (W : Finset V) (M : ℕ → Finset (V × V)) (hM : M k = ∅)
    (N : Finset (V × V)) (v : V) :
    matchingLoad q i W (Function.update M k N) v =
      matchingLoad q i W M v + (if k ≠ i ∧ matchingHit W v N then 1 else 0) := by
  let S := (range q).filter (fun j => j ≠ i ∧ matchingHit W v (M j))
  have hNot : k ∉ S := by
    intro h
    have hh := (mem_filter.mp h).2.2.2
    simp [hM] at hh
  have hSet : (range q).filter (fun j => j ≠ i ∧ matchingHit W v (Function.update M k N j)) =
      if k ≠ i ∧ matchingHit W v N then insert k S else S := by
    ext j
    by_cases hj : j = k
    · subst j
      simp only [mem_filter,mem_range,hk,true_and,Function.update_self]
      split_ifs <;> simp_all
    · simp only [Function.update_of_ne hj,S,mem_filter,mem_range]
      split_ifs <;> simp [hj]
  unfold matchingLoad
  change ((range q).filter _).card = S.card + _
  rw [hSet]
  split_ifs <;> simp [card_insert_of_notMem hNot]

/-- At most one previously chosen edge is lost per contributing
matching when testing the degree of v into a specified shore. -/
theorem card_deleted_neighbors_le_load {q k : ℕ} (hk : k ≤ q)
    (W P : Finset V) (hPW : P ⊆ W) (v : V) (hv : v ∈ W)
    (M : ℕ → Finset (V × V))
    (hUnique : ∀ j < k, ∀ a b, (v,a) ∈ M j → (v,b) ∈ M j → a = b) :
    (P.filter (fun a => ∃ j < k, (v,a) ∈ M j)).card ≤ matchingLoad q k W M v := by
  let J := (range q).filter (fun j => j ≠ k ∧ matchingHit W v (M j))
  let N (j : ℕ) := P.filter (fun a => j < k ∧ (v,a) ∈ M j)
  have hSub : P.filter (fun a => ∃ j < k, (v,a) ∈ M j) ⊆ J.biUnion N := by
    intro a ha
    obtain ⟨ha,j,hj,hja⟩ := mem_filter.mp ha
    exact mem_biUnion.mpr ⟨j,mem_filter.mpr
      ⟨mem_range.mpr (hj.trans_le hk),hj.ne, hv, a,hPW ha,hja⟩,
      mem_filter.mpr ⟨ha,hj,hja⟩⟩
  have hOne (j : ℕ) : (N j).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    have hA := (mem_filter.mp ha).2
    have hB := (mem_filter.mp hb).2
    exact hUnique j hA.1 a b hA.2 hB.2
  calc
    _ ≤ (J.biUnion N).card := card_le_card hSub
    _ ≤ ∑ j ∈ J, (N j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ J, 1 := sum_le_sum (fun j _ => hOne j)
    _ = _ := by simp [matchingLoad,J]

/-- Restricting a relation by the deleted edges drops its degree by
at most the number of deleted neighbors on the relevant shore. -/
theorem card_residual_neighbors {P : Finset V} (E D : V → Prop)
    [DecidablePred E] [DecidablePred D]
    (d k loss : ℕ) (hDeg : d+k+loss ≤ (P.filter E).card)
    (hLoss : (P.filter D).card ≤ loss) :
    d+k ≤ (P.filter (fun a => E a ∧ ¬ D a)).card := by
  have hSub : P.filter E ⊆ (P.filter (fun a => E a ∧ ¬ D a)) ∪ (P.filter D) := by
    intro a ha
    obtain ⟨ha,hE⟩ := mem_filter.mp ha
    by_cases h : D a
    · exact mem_union_right _ (mem_filter.mpr ⟨ha,h⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨ha,hE,h⟩)
  have hCard := (card_le_card hSub).trans (card_union_le _ _)
  omega

end OverfullWork.ChenShan
