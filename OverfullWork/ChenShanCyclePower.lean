module

public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! The cycle powers used in Chen–Shan, Lemma 3.23. -/

namespace OverfullWork.ChenShan

open SimpleGraph Finset

/-- The graph with jumps of at most `r` in either direction on the cyclic order. -/
def auxiliaryCyclePower (n r : ℕ) [NeZero n] : SimpleGraph (Fin n) :=
  circulantGraph {x : Fin n | 0 < x.val ∧ x.val ≤ r}

instance (n r : ℕ) [NeZero n] : DecidableRel (auxiliaryCyclePower n r).Adj := by
  unfold auxiliaryCyclePower
  infer_instance

/-- In the nonwrapping part of the cyclic order, any two distinct vertices
at distance at most the radius are adjacent. -/
theorem auxiliaryCyclePower_adj_of_sub_le {n r : ℕ} [NeZero n] {v w : Fin n}
    (hvw : v < w) (hDist : w.val - v.val ≤ r) :
    (auxiliaryCyclePower n r).Adj v w := by
  rw [auxiliaryCyclePower, circulantGraph_adj]
  refine ⟨ne_of_lt hvw, Or.inr ?_⟩
  change 0 < (w - v).val ∧ (w - v).val ≤ r
  rw [Fin.sub_val_of_le hvw.le]
  exact ⟨Nat.sub_pos_of_lt hvw, hDist⟩

/-- If the positive and negative jumps do not overlap, the degree is twice
the radius. -/
theorem auxiliaryCyclePower_degree {n r : ℕ} [NeZero n] (h : 2 * r < n) (v : Fin n) :
    (auxiliaryCyclePower n r).degree v = 2 * r := by
  let jump : Fin r ↪ Fin n :=
    ⟨fun i => ⟨i.val + 1, by have := i.isLt; omega⟩,
      fun i j hij => Fin.ext (by have he := congrArg Fin.val hij; change i.val + 1 = j.val + 1 at he; omega)⟩
  let positive := (univ : Finset (Fin r)).map jump
  let negative := positive.map (Equiv.neg (Fin n)).toEmbedding
  have hPos (x : Fin n) : x ∈ positive ↔ 0 < x.val ∧ x.val ≤ r := by
    rw [mem_map]
    constructor
    · rintro ⟨i, _, rfl⟩
      change 0 < i.val + 1 ∧ i.val + 1 ≤ r
      exact ⟨by omega, i.isLt⟩
    · intro hx
      refine ⟨⟨x.val - 1, by omega⟩, mem_univ _, Fin.ext ?_⟩
      change x.val - 1 + 1 = x.val
      omega
  have hNeg (x : Fin n) : x ∈ negative ↔ -x ∈ positive := by
    simp only [negative, mem_map, Equiv.toEmbedding_apply, Equiv.neg_apply]
    exact ⟨fun ⟨y, hy, hyx⟩ => by rwa [← hyx, neg_neg],
      fun hx => ⟨-x, hx, neg_neg x⟩⟩
  have hDisjoint : Disjoint positive negative := by
    rw [Finset.disjoint_left]
    intro x hx hnx
    have hp := (hPos x).mp hx
    have hn := (hPos (-x)).mp ((hNeg x).mp hnx)
    have hAdd : (x + -x).val = x.val + (-x).val := by
      rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
    simp only [add_neg_cancel, Fin.val_zero] at hAdd
    omega
  let translate := (Equiv.addRight v).toEmbedding
  have hNeighbors :
      (auxiliaryCyclePower n r).neighborFinset v = (positive ∪ negative).map translate := by
    have hAdj (w : Fin n) : (auxiliaryCyclePower n r).Adj v w ↔ w - v ∈ positive ∪ negative := by
      simp only [auxiliaryCyclePower, circulantGraph_adj, Set.mem_ofPred_eq, mem_union, hNeg, hPos, neg_sub]
      constructor
      · intro hw
        exact hw.2.symm
      · intro hw
        refine ⟨?_, hw.symm⟩
        rintro rfl
        simp only [sub_self, Fin.val_zero, lt_self_iff_false, false_and, or_self] at hw
    ext w
    rw [mem_neighborFinset, hAdj, mem_map]
    change w - v ∈ positive ∪ negative ↔ ∃ x ∈ positive ∪ negative, x + v = w
    exact ⟨fun hw => ⟨w - v, hw, sub_add_cancel w v⟩,
      fun ⟨x, hx, hw⟩ => by simpa only [← hw, add_sub_cancel_right]⟩
  rw [← card_neighborFinset_eq_degree, hNeighbors, card_map, card_union_of_disjoint hDisjoint]
  simp [positive, negative, two_mul]


/-- On an even number of vertices, adding the antipodal matching realizes
the next odd regular degree and preserves all edges of the cycle power. -/
theorem exists_odd_regular_extension (m r : ℕ) (hm : 0 < m) [NeZero (2 * m)]
    (hr : r < m) :
    ∃ H : SimpleGraph (Fin (2 * m)), ∃ _ : DecidableRel H.Adj,
      auxiliaryCyclePower (2 * m) r ≤ H ∧ ∀ v, H.degree v = 2 * r + 1 := by
  let d : Fin (2 * m) := ⟨m, by omega⟩
  have hd : d ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change m = 0 at hv
    omega
  have hdd : d + d = 0 := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_zero]
    change (m + m) % (2 * m) = 0
    rw [← two_mul, Nat.mod_self]
  have hnd : -d = d := by
    have := congrArg (fun x => -d + x) hdd
    simpa only [← add_assoc, neg_add_cancel, zero_add, add_zero] using this.symm
  let P : SimpleGraph (Fin (2 * m)) := circulantGraph {d}
  let C := auxiliaryCyclePower (2 * m) r
  have hP (v w : Fin (2 * m)) : P.Adj v w ↔ w = v + d := by
    simp only [P, circulantGraph_adj, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, h | h⟩
      · have hs : w - v = d := by rw [← neg_sub, h, hnd]
        exact (sub_eq_iff_eq_add.mp hs).trans (add_comm _ _)
      · exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    · rintro rfl
      refine ⟨?_, Or.inr (add_sub_cancel_left _ _)⟩
      intro he
      exact hd ((add_eq_left.mp he.symm))
  have hOne (v : Fin (2 * m)) : P.degree v = 1 := by
    rw [degree_eq_one_iff_existsUnique_adj]
    exact ⟨v + d, (hP _ _).mpr rfl, fun w hw => (hP _ _).mp hw⟩
  have hDis : Disjoint C P := by
    rw [SimpleGraph.disjoint_left]
    intro v w hw hp
    have he := (hP v w).mp hp
    have hsub : w - v = d := by rw [he, add_sub_cancel_left]
    have hrev : v - w = d := by rw [← neg_sub, hsub, hnd]
    change (circulantGraph {x : Fin (2 * m) | 0 < x.val ∧ x.val ≤ r}).Adj v w at hw
    rw [circulantGraph_adj] at hw
    have hh := hw.2
    rw [hsub, hrev, or_self] at hh
    exact (Nat.not_le_of_lt hr) hh.2
  let inst : DecidableRel (C ⊔ P).Adj := fun x y =>
    inferInstanceAs (Decidable (C.Adj x y ∨ P.Adj x y))
  refine ⟨C ⊔ P, inst, le_sup_left, fun v => ?_⟩
  have hUnion := neighborFinset_sup_of_disjoint (v := v) hDis
  have hCount := congrArg Finset.card hUnion
  rw [card_disjUnion] at hCount
  simp only [card_neighborFinset_eq_degree] at hCount
  have hC : C.degree v = 2 * r := auxiliaryCyclePower_degree (by omega) v
  rw [hCount, hC, hOne]

end OverfullWork.ChenShan
