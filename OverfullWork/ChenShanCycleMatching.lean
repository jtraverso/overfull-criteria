module

public import OverfullWork.ChenShanCyclePower
public import OverfullWork.MaximumMatchingPeeling
public import Mathlib.Data.ZMod.Defs

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset

/-- Pair consecutive vertices in the initial segment of length `2 * k`. -/
def initialCycleMatching (n k : ℕ) : SimpleGraph (Fin n) where
  Adj v w := (v.val < 2 * k ∧ v.val % 2 = 0 ∧ w.val = v.val + 1) ∨
    (w.val < 2 * k ∧ w.val % 2 = 0 ∧ v.val = w.val + 1)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun v h => by rcases h with h | h <;> omega⟩

instance (n k : ℕ) : DecidableRel (initialCycleMatching n k).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- The matching changes exactly the first `2 * k` degrees by one. -/
theorem initialCycleMatching_degree {n k : ℕ} (hk : 2 * k ≤ n) (v : Fin n) :
    (initialCycleMatching n k).degree v = if v.val < 2 * k then 1 else 0 := by
  by_cases hv : v.val < 2 * k
  · rw [ite_eq_left hv, degree_eq_one_iff_existsUnique_adj]
    by_cases hp : v.val % 2 = 0
    · let w : Fin n := ⟨v.val + 1, by omega⟩
      refine ⟨w, Or.inl ⟨hv, hp, rfl⟩, ?_⟩
      intro u hu
      apply Fin.ext
      change u.val = v.val + 1
      change (_ ∨ _) at hu
      rcases hu with h | h
      · exact h.2.2
      · omega
    · let w : Fin n := ⟨v.val - 1, by have := v.isLt; omega⟩
      refine ⟨w, Or.inr ?_, ?_⟩
      · change v.val - 1 < 2 * k ∧ (v.val - 1) % 2 = 0 ∧ v.val = v.val - 1 + 1
        omega
      · intro u hu
        apply Fin.ext
        change u.val = v.val - 1
        change (_ ∨ _) at hu
        rcases hu with h | h <;> omega
  · rw [ite_eq_right hv, degree_eq_zero_iff_notMem_support, mem_support]
    rintro ⟨w, hw⟩
    change (_ ∨ _) at hw
    rcases hw with h | h <;> omega

/-- Every edge of the matching lies in the original cycle and hence in
each positive-radius cycle power. -/
theorem initialCycleMatching_le_cyclePower {n k r : ℕ} [NeZero n] (hr : 0 < r) :
    initialCycleMatching n k ≤ auxiliaryCyclePower n r := by
  intro v w h
  change (_ ∨ _) at h
  rcases h with h | h
  · exact auxiliaryCyclePower_adj_of_sub_le (show v.val < w.val by omega) (by omega)
  · exact (auxiliaryCyclePower_adj_of_sub_le (show w.val < v.val by omega) (by omega)).symm


/-- Removing the initial matching lowers the degree of its vertices by
one. It also deletes at most one edge of the cycle power at any vertex. -/
theorem degree_and_loss_after_initial_matching {n k r : ℕ} [NeZero n]
    (hk : 2 * k ≤ n) (hr : 0 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hBase : auxiliaryCyclePower n r ≤ G) :
    (∀ v, (G \ initialCycleMatching n k).degree v + (if v.val < 2 * k then 1 else 0) =
      G.degree v) ∧
    (∀ v, ((univ : Finset (Fin n)).filter (fun w =>
      (auxiliaryCyclePower n r).Adj v w ∧ ¬ (G \ initialCycleMatching n k).Adj v w)).card ≤ 1) := by
  let M := initialCycleMatching n k
  have hM : M ≤ G := (initialCycleMatching_le_cyclePower hr).trans hBase
  constructor
  · intro v
    have h := MaximumMatching.degree_sdiff_add_of_le G M hM v
    rwa [initialCycleMatching_degree hk] at h
  · intro v
    have hs : (univ : Finset (Fin n)).filter (fun w =>
        (auxiliaryCyclePower n r).Adj v w ∧ ¬ (G \ M).Adj v w) ⊆ M.neighborFinset v := by
      intro w hw
      obtain ⟨_, hc, hDel⟩ := mem_filter.mp hw
      exact (mem_neighborFinset M v w).mpr (by
        by_contra hm
        exact hDel ⟨hBase hc, hm⟩)
    have hCard := card_le_card hs
    rw [card_neighborFinset_eq_degree, initialCycleMatching_degree hk] at hCard
    exact hCard.trans (by split <;> omega)


/-- At odd order `2 * m + 1`, multiplication by `m` cyclically
relabels consecutive edges as edges at distance `m`. -/
theorem exists_initial_matching_in_odd_complement {m k r : ℕ} (hm : 0 < m)
    (hr : r < m) :
    ∃ e : Fin (2 * m + 1) ≃ Fin (2 * m + 1),
      Disjoint (auxiliaryCyclePower (2 * m + 1) r)
        ((initialCycleMatching (2 * m + 1) k).map e.toEmbedding) := by
  let N := 2 * m + 1
  let d : Fin N := ⟨m, by omega⟩
  have hOne : (1 : Fin N).val = 1 := by
    change 1 % N = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hCycle : d + d + 1 = 0 := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_add, hOne, Fin.val_zero]
    change ((m + m) % N + 1) % N = 0
    rw [Nat.mod_eq_of_lt (show m + m < N by omega)]
    have he : m + m + 1 = N := by omega
    rw [he, Nat.mod_self]
  let _ : CommRing (Fin N) := Fin.instCommRing N
  have hInverse : d * (-2 : Fin N) = 1 := by linear_combination -hCycle
  let e : Fin N ≃ Fin N :=
    { toFun := fun x => d * x
      invFun := fun x => -2 * x
      left_inv := fun x => by
        change -2 * (d * x) = x
        rw [← mul_assoc, mul_comm (-2 : Fin N) d, hInverse, one_mul]
      right_inv := fun x => by
        change d * (-2 * x) = x
        rw [← mul_assoc, hInverse, one_mul] }
  have hNegD : (-d).val = m + 1 := by
    rw [Fin.val_neg]
    have hd : d ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      change m = 0 at hv
      omega
    rw [ite_eq_right hd]
    change N - m = m + 1
    omega
  have hDiff (x y : Fin N) (hxy : y.val = x.val + 1) : e y - e x = d := by
    have hsub : y - x = 1 := by
      apply Fin.ext
      have hle : x ≤ y := by change x.val ≤ y.val; omega
      rw [Fin.sub_val_of_le hle, hOne, hxy, Nat.add_sub_cancel_left]
    change d * y - d * x = d
    rw [← mul_sub, hsub, mul_one]
  refine ⟨e, SimpleGraph.disjoint_left.mpr ?_⟩
  intro v w hC hM
  obtain ⟨x, y, hxy, hx, hy⟩ := (map_adj _ _ _ _).mp hM
  change e x = v at hx
  change e y = w at hy
  have hSupport (u z : Fin N) (hu : z - u = d) :
      ¬ (auxiliaryCyclePower N r).Adj u z := by
    intro h
    rw [auxiliaryCyclePower, circulantGraph_adj] at h
    have hrev : u - z = -d := by rw [← neg_sub, hu]
    have hh := h.2
    rw [hu, hrev] at hh
    change (0 < (-d).val ∧ (-d).val ≤ r) ∨ (0 < m ∧ m ≤ r) at hh
    rw [hNegD] at hh
    omega
  change (_ ∨ _) at hxy
  rcases hxy with hxy | hyx
  · exact hSupport v w (by rw [← hx, ← hy, hDiff x y hxy.2.2]) hC
  · exact hSupport w v (by rw [← hx, ← hy, hDiff y x hyx.2.2]) hC.symm


/-- On odd order, raising the degree on an even number of vertices
preserves the base cycle power. The equivalence records which vertices
have their degree raised. -/
theorem exists_odd_order_degree_extension {m k r : ℕ} (hm : 0 < m)
    (hk : 2 * k ≤ 2 * m + 1) (hr : r < m) :
    ∃ H : SimpleGraph (Fin (2 * m + 1)), ∃ _ : DecidableRel H.Adj,
      ∃ e : Fin (2 * m + 1) ≃ Fin (2 * m + 1),
        auxiliaryCyclePower (2 * m + 1) r ≤ H ∧
          ∀ v, H.degree (e v) = 2 * r + (if v.val < 2 * k then 1 else 0) := by
  classical
  obtain ⟨e, he⟩ := exists_initial_matching_in_odd_complement (k := k) hm hr
  let C := auxiliaryCyclePower (2 * m + 1) r
  let M := initialCycleMatching (2 * m + 1) k
  let P := M.map e.toEmbedding
  let _ : DecidableRel P.Adj := Classical.decRel _
  let inst : DecidableRel (C ⊔ P).Adj := fun x y =>
    inferInstanceAs (Decidable (C.Adj x y ∨ P.Adj x y))
  refine ⟨C ⊔ P, inst, e, le_sup_left, fun v => ?_⟩
  have hUnion := neighborFinset_sup_of_disjoint (v := e v) he
  have hCount := congrArg Finset.card hUnion
  rw [card_disjUnion] at hCount
  simp only [card_neighborFinset_eq_degree] at hCount
  have hC : C.degree (e v) = 2 * r := auxiliaryCyclePower_degree (by omega) (e v)
  have hP : P.degree (e v) = M.degree v := M.degree_map_apply e.toEmbedding v
  rw [hCount, hC, hP, initialCycleMatching_degree hk]

end OverfullWork.ChenShan
