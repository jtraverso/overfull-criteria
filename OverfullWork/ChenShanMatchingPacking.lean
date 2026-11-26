module

public import OverfullWork.ChenShanAdaptiveMatchingSchedule
public import OverfullWork.ChenShanMatchingPackingLoad

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real
open scoped Classical

variable {V : Type*} [Fintype V]

/-- The bipartite random-greedy argument via conditional expectation.
The initial exponential bound pays for all monitored vertex loads. -/
theorem exists_matching_packing_of_exponential_bound
    (E : V → V → Prop) (X Y : ℕ → Finset V) (q : ℕ)
    (d : ℕ → ℕ) (kCand loss : ℕ) (α p cap budget : ℝ)
    (hα : 0 < α) (hp : 0 ≤ p) (hCap : cap ≤ loss)
    (hSize : ∀ i < q, (X i).card = (Y i).card)
    (hShore : ∀ i < q, Disjoint (X i) (Y i))
    (hHalf : ∀ i < q, (Y i).card ≤ 2*d i)
    (hLeft : ∀ i < q, ∀ a ∈ X i,
      d i+kCand+loss ≤ ((Y i).filter (E a)).card)
    (hRight : ∀ i < q, ∀ b ∈ Y i,
      d i+kCand+loss ≤ ((X i).filter (fun a => E a b)).card)
    (hOverlap : ∀ i < q, ∀ j < q, i ≠ j →
      (((X i ∪ Y i) ∩ (X j ∪ Y j)).card : ℝ) ≤ p*(kCand+1))
    (hOccur : ∀ v, (((range q).filter (fun j => v ∈ X j ∪ Y j)).card : ℝ) ≤ budget)
    (hPotential : (q : ℝ) * Fintype.card V * exp (p*(exp α-1)*budget-α*cap) < 1) :
    ∃ M : ℕ → Finset (V × V),
      (∀ i < q, ∃ f : ↥(X i) ≃ ↥(Y i),
        M i = matchingArcs f ∧ ∀ a : X i, E a (f a)) ∧
      ∀ i < q, ∀ j < q, i ≠ j → Disjoint (M i) (M j) := by
  let W i := X i ∪ Y i
  let valid (k : ℕ) (M : ℕ → Finset (V × V)) : Prop :=
    (∀ i < k, ∃ f : ↥(X i) ≃ ↥(Y i),
      M i = matchingArcs f ∧ ∀ a : X i, E a (f a)) ∧
    (∀ i ≥ k, M i = ∅) ∧
    ∀ i < k, ∀ j < k, i ≠ j → Disjoint (M i) (M j)
  let active (k : ℕ) (t : Fin q × V) :=
    k ≠ t.1.val ∧ t.2 ∈ W t.1.val ∧ t.2 ∈ W k
  let _ : DecidableRel active := fun _ _ => Classical.propDecidable _
  let load (M : ℕ → Finset (V × V)) (t : Fin q × V) :=
    matchingLoad q t.1.val (W t.1.val) M t.2
  let M₀ : ℕ → Finset (V × V) := fun _ => ∅
  let β := p*(exp α-1)
  have hβ : 0 ≤ β := mul_nonneg hp (sub_nonneg.mpr (one_le_exp_iff.mpr hα.le))
  have hValid : valid 0 M₀ := by simp [valid,M₀]
  have hInit :
      (∑ t, exp (α*load M₀ t + β*remainingHits active 0 q t - α*cap)) < 1 := by
    have hLoad₀ (t : Fin q × V) : load M₀ t = 0 := by
      simp [load,matchingLoad,matchingHit,M₀]
    refine lt_of_le_of_lt ?_ hPotential
    calc
      _ ≤ ∑ _t : Fin q × V, exp (β*budget - α*cap) := by
        apply sum_le_sum
        intro t _
        apply exp_le_exp.mpr
        have hRem : (remainingHits active 0 q t : ℝ) ≤ budget := by
          apply le_trans _ (hOccur t.2)
          exact_mod_cast (show remainingHits active 0 q t ≤
              ((range q).filter (fun j => t.2 ∈ W j)).card by
            apply card_le_card
            intro j hj
            have h := mem_filter.mp hj
            exact mem_filter.mpr ⟨mem_range.mpr (mem_Ico.mp h.1).2,h.2.2.2⟩)
        simp only [hLoad₀,Nat.cast_zero,mul_zero,zero_add]
        exact sub_le_sub_right (mul_le_mul_of_nonneg_left hRem hβ) _
      _ = _ := by simp [Fintype.card_prod,Nat.cast_mul,nsmul_eq_mul,β]
  have schedule := exists_adaptive_matching_schedule (C := Fin (kCand+1))
    q M₀ valid active load α p cap hα hp hValid hInit
  obtain ⟨M,hM,_⟩ := schedule (by
    intro k hk M hM hLoad
    have hOldSymm (j : ℕ) (hj : j < k) {a b : V} (hab : (a,b) ∈ M j) :
        (b,a) ∈ M j := by
      obtain ⟨f,hf,_⟩ := hM.1 j hj
      rw [hf] at hab ⊢
      exact matchingArcs_symm f hab
    have hOldUnique (v : V) (j : ℕ) (hj : j < k) {a b : V}
        (ha : (v,a) ∈ M j) (hb : (v,b) ∈ M j) : a = b := by
      obtain ⟨f,hf,_⟩ := hM.1 j hj
      rw [hf] at ha hb
      exact matchingArcs_unique_neighbor (hShore j (hj.trans hk)) f ha hb
    have hLoss (P : Finset V) (hP : P ⊆ W k) (v : V) (hv : v ∈ W k) :
        (P.filter (fun a => ∃ j < k, (v,a) ∈ M j)).card ≤ loss := by
      have hh := card_deleted_neighbors_le_load hk.le (W k) P hP v hv M
        (fun j hj _ _ => hOldUnique v j hj)
      have hL : (matchingLoad q k (W k) M v : ℝ) < cap := hLoad (⟨k,hk⟩,v)
      exact hh.trans (by exact_mod_cast (hL.le.trans hCap))
    let R (a b : V) := E a b ∧ ¬∃ j < k, (a,b) ∈ M j
    let _ : DecidableRel R := fun _ _ => Classical.propDecidable _
    have hL (a : X k) : d k + kCand ≤ (univ.filter (fun b : Y k => R a b)).card := by
      rw [DenseHall.subtype_filter_card (Y k) (R a)]
      have h := card_residual_neighbors (E a) (fun z => ∃ j < k, (a.1,z) ∈ M j)
        (d k) kCand loss (hLeft k hk a a.2)
        (hLoss (Y k) (fun _ hz => mem_union_right _ hz) a (mem_union_left _ a.2))
      convert h using 2
      ext z
      simp only [mem_filter,R]
    have hR (b : Y k) : d k + kCand ≤ (univ.filter (fun a : X k => R a b)).card := by
      rw [DenseHall.subtype_filter_card (X k) (fun a => R a b)]
      have hEq : (X k).filter (fun a => ∃ j < k, (a,b.1) ∈ M j) =
          (X k).filter (fun a => ∃ j < k, (b.1,a) ∈ M j) := by
        ext a
        simp only [mem_filter]
        constructor <;> rintro ⟨ha,j,hj,h⟩ <;> exact ⟨ha,j,hj,hOldSymm j hj h⟩
      have h := card_residual_neighbors (fun z => E z b) (fun z => ∃ j < k, (z,b.1) ∈ M j)
        (d k) kCand loss (hRight k hk b b.2)
        (by rw [hEq]; exact hLoss (X k) (fun _ hz => mem_union_left _ hz) b (mem_union_right _ b.2))
      convert h using 2
      ext z
      simp only [mem_filter,R]
    obtain ⟨f,hf,hfDis⟩ := exists_disjoint_perfect_matching_candidates
      (fun (a : X k) (b : Y k) => R a b) (d k) kCand
      (by simpa only [Fintype.card_coe] using hSize k hk)
      (by simpa only [Fintype.card_coe] using hHalf k hk) hL hR
    let next (c : Fin (kCand+1)) := Function.update M k (matchingArcs (f c))
    let hit (t : Fin q × V) (c : Fin (kCand+1)) :=
      ∃ v ∈ W t.1.val, (t.2,v) ∈ matchingArcs (f c)
    let _ : DecidableRel hit := fun _ _ => Classical.propDecidable _
    refine ⟨next,hit,?_,?_,?_⟩
    · intro c
      have hAvoid (j : ℕ) (hj : j < k) : Disjoint (matchingArcs (f c)) (M j) := by
        apply disjoint_left.mpr
        rintro ⟨a,b⟩ ha hb
        obtain ⟨x,he|he⟩ := (mem_matchingArcs (f c) a b).mp ha
        · have he' : (x.1,(f c x).1) ∈ M j := by simpa only [he.1,he.2] using hb
          exact (hf c x).2 ⟨j,hj,he'⟩
        · have he' : ((f c x).1,x.1) ∈ M j := by simpa only [he.1,he.2] using hb
          exact (hf c x).2 ⟨j,hj,hOldSymm j hj he'⟩
      refine ⟨?_,?_,?_⟩
      · intro i hi
        by_cases he : i = k
        · subst i
          exact ⟨f c,Function.update_self _ _ _,fun a => (hf c a).1⟩
        · simpa only [next,Function.update_of_ne he] using hM.1 i (by omega)
      · intro i hi
        have he : i ≠ k := by omega
        simpa only [next,Function.update_of_ne he] using hM.2.1 i (by omega)
      · intro i hi j hj hne
        by_cases he : i = k
        · subst i
          have hne' : j ≠ k := hne.symm
          simpa only [next,Function.update_self,Function.update_of_ne hne'] using hAvoid j (by omega)
        · by_cases he' : j = k
          · subst j
            simpa only [next,Function.update_self,Function.update_of_ne he] using (hAvoid i (by omega)).symm
          · simpa only [next,Function.update_of_ne he,Function.update_of_ne he'] using
              hM.2.2 i (by omega) j (by omega) hne
    · intro t ht
      have hh := matchingArcs_candidate_hit_count (hShore k hk) f hfDis (W t.1.val) t.2
      have hc : (univ.filter (hit t)).card ≤ (W t.1.val ∩ W k).card := by
        convert hh using 2
        ext c
        simp only [mem_filter,hit]
      have hcount : ((univ.filter (hit t)).card : ℝ) ≤
          ((W t.1.val ∩ W k).card : ℝ) := by exact_mod_cast hc
      simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
        hcount.trans (hOverlap t.1.val t.1.isLt k hk ht.1.symm)
    · intro t c
      change matchingLoad q t.1.val (W t.1.val) (Function.update M k _) t.2 = _
      rw [matchingLoad_update hk _ _ (hM.2.1 k le_rfl)]
      have hh : (k ≠ t.1.val ∧ matchingHit (W t.1.val) t.2 (matchingArcs (f c))) ↔
          active k t ∧ hit t c := by
        constructor
        · rintro ⟨hne,ht,v,hv,he⟩
          exact ⟨⟨hne,ht,(matchingArcs_vertices _ he).1⟩,v,hv,he⟩
        · rintro ⟨⟨hne,ht,_⟩,v,hv,he⟩
          exact ⟨hne,ht,v,hv,he⟩
      rw [if_congr hh rfl rfl])
  exact ⟨M,hM.1,hM.2.2⟩

end OverfullWork.ChenShan
