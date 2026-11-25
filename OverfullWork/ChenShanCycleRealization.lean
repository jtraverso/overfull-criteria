module

public import OverfullWork.ChenShanCycleBlocks
public import OverfullWork.ChenShanCycleMatching
public import OverfullWork.KLOSPartitionRestriction

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset KLOS PrunedCore RobustExpansion
open scoped Classical

private theorem exists_regular_cycle_supergraph (n d : ℕ) [NeZero n] (hd : d < n)
    (hParity : (n * d) % 2 = 0) :
    ∃ H : SimpleGraph (Fin n), ∃ _ : DecidableRel H.Adj,
      auxiliaryCyclePower n (d / 2) ≤ H ∧ ∀ v, H.degree v = d := by
  by_cases he : d % 2 = 0
  · refine ⟨auxiliaryCyclePower n (d / 2), inferInstance, le_rfl, fun v => ?_⟩
    rw [auxiliaryCyclePower_degree (by omega)]
    omega
  · have hn : n % 2 = 0 := by
      have hp : d % 2 = 1 := by omega
      rwa [Nat.mul_mod n d, hp, Nat.mul_one, Nat.mod_mod] at hParity
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hm : 0 < m := by omega
    obtain ⟨H, hD, hLe, hReg⟩ := exists_odd_regular_extension m (d / 2) hm (by omega)
    exact ⟨H, hD, hLe, fun v => (hReg v).trans (by omega)⟩

private theorem card_initial_fin_segment (n j : ℕ) (hj : j ≤ n) :
    ((univ : Finset (Fin n)).filter (fun v => v.val < j)).card = j := by
  have hRange (x : ℕ) (hx : x ∈ range j) : x < n := (mem_range.mp hx).trans_le hj
  have hEq : (univ : Finset (Fin n)).filter (fun v => v.val < j) =
      (range j).attachFin hRange := by
    ext v
    simp
  rw [hEq, card_attachFin, card_range]

/-- Realize the prescribed number of high degrees, with a base cycle
power of radius at least `(d - 1) / 2` and at most one lost edge per vertex. -/
theorem exists_cycle_degree_multiset (n d j : ℕ) [NeZero n]
    (hd : 2 ≤ d) (hDn : d < n) (hj : j ≤ n) (hHigh : j ≠ 0 → d + 1 < n)
    (hParity : (n * d + j) % 2 = 0) :
    ∃ r : ℕ, d ≤ 2 * r + 1 ∧ ∃ H : SimpleGraph (Fin n), ∃ _ : DecidableRel H.Adj,
      (∀ v, d ≤ H.degree v ∧ H.degree v ≤ d + 1) ∧
      ((univ : Finset (Fin n)).filter (fun v => H.degree v = d + 1)).card = j ∧
      (∀ v, ((univ : Finset (Fin n)).filter
        (fun w => (auxiliaryCyclePower n r).Adj v w ∧ ¬ H.Adj v w)).card ≤ 1) := by
  classical
  have hNoLoss (r : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
      (hLe : auxiliaryCyclePower n r ≤ H) (v : Fin n) :
      ((univ : Finset (Fin n)).filter
        (fun w => (auxiliaryCyclePower n r).Adj v w ∧ ¬ H.Adj v w)).card ≤ 1 := by
    have hEmpty : ¬ ((univ : Finset (Fin n)).filter
        (fun w => (auxiliaryCyclePower n r).Adj v w ∧ ¬ H.Adj v w)).Nonempty := by
      rintro ⟨w, hw⟩
      exact (mem_filter.mp hw).2.2 (hLe (mem_filter.mp hw).2.1)
    simp [not_nonempty_iff_eq_empty.mp hEmpty]
  by_cases h0 : j = 0
  · subst j
    obtain ⟨H, hD, hLe, hReg⟩ := exists_regular_cycle_supergraph n d hDn (by simpa using hParity)
    refine ⟨d / 2, by omega, H, hD, fun v => ⟨le_of_eq (hReg v).symm, by rw [hReg]; omega⟩,
      ?_, hNoLoss _ H hLe⟩
    simp [hReg]
  by_cases hTop : (n * (d + 1)) % 2 = 0
  · have hEvenLow : (n - j) % 2 = 0 := by
      rw [Nat.mul_add, Nat.mul_one] at hTop
      omega
    let k := (n - j) / 2
    let r := (d + 1) / 2
    have hk : 2 * k = n - j := by omega
    obtain ⟨G, hD, hLe, hReg⟩ := exists_regular_cycle_supergraph n (d + 1) (hHigh h0) hTop
    let H := G \ initialCycleMatching n k
    obtain ⟨hDegree, hLoss⟩ := degree_and_loss_after_initial_matching
      (n := n) (k := k) (r := r) (by omega) (by omega) G hLe
    refine ⟨r, by omega, H, inferInstance, ?_, ?_, hLoss⟩
    · intro v
      have h := hDegree v
      change H.degree v + (if v.val < 2 * k then 1 else 0) = G.degree v at h
      rw [hReg] at h
      split at h <;> omega
    · have hPred (v : Fin n) : H.degree v = d + 1 ↔ ¬ v.val < 2 * k := by
        have h := hDegree v
        change H.degree v + (if v.val < 2 * k then 1 else 0) = G.degree v at h
        rw [hReg] at h
        split at h <;> omega
      have hEq : (univ : Finset (Fin n)).filter (fun v => H.degree v = d + 1) =
          ((univ : Finset (Fin n)).filter (fun v => v.val < 2 * k))ᶜ := by
        ext v
        simp [hPred]
      rw [hEq, card_compl, Fintype.card_fin, card_initial_fin_segment n (2*k) (by omega), hk]
      omega
  · have hOddN : n % 2 = 1 := by
      by_contra hn
      have hz : n % 2 = 0 := by omega
      exact hTop (by rw [Nat.mul_mod n (d + 1), hz, Nat.zero_mul, Nat.zero_mod])
    have hEvenD : d % 2 = 0 := by
      by_contra hd'
      have hz : (d + 1) % 2 = 0 := by omega
      exact hTop (by rw [Nat.mul_mod n (d + 1), hz, Nat.mul_zero, Nat.zero_mod])
    have hEvenJ : j % 2 = 0 := by
      rw [Nat.add_mod, Nat.mul_mod n d, hEvenD, Nat.mul_zero, Nat.zero_mod, Nat.zero_add,
        Nat.mod_mod] at hParity
      exact hParity
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    let r := d / 2
    let k := j / 2
    have hk : 2 * k = j := by omega
    obtain ⟨H, hD, e, hLe, hDegree⟩ :=
      exists_odd_order_degree_extension (m := m) (k := k) (r := r)
        (by omega) (by omega) (by have := hHigh h0; omega)
    have hTwoR : 2 * r = d := by omega
    refine ⟨r, by omega, H, hD, ?_, ?_, hNoLoss _ H hLe⟩
    · intro v
      obtain ⟨u, rfl⟩ := e.surjective v
      rw [hDegree, hTwoR]
      split <;> omega
    · have hEq :
          (univ : Finset (Fin (2 * m + 1))).filter (fun v => H.degree v = d + 1) =
            ((univ : Finset (Fin (2 * m + 1))).filter (fun u => u.val < j)).map e.toEmbedding := by
        ext v
        obtain ⟨u, rfl⟩ := e.surjective v
        simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply]
        simp only [e.injective.eq_iff, exists_eq_right]
        rw [hDegree, hTwoR, hk]
        split <;> omega
      rw [hEq, card_map, card_initial_fin_segment _ _ hj]


/-- Chen–Shan, Lemma 3.23. A dense almost constant degree sequence with
even sum and degrees below the order has a robust simple realization
on the given labeled vertices. -/
theorem exists_robust_graph_with_prescribed_degrees
    (δ τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ N : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V],
      N ≤ Fintype.card V → ∀ degrees : V → ℕ,
      (∀ v, δ * (Fintype.card V : ℝ) ≤ (degrees v : ℝ)) →
      (∀ v, degrees v < Fintype.card V) →
      (∀ v w, degrees v ≤ degrees w + 1) →
      (∑ v, degrees v) % 2 = 0 →
      ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
        (∀ v, G.degree v = degrees v) ∧ ExpandsInside G ν τ univ := by
  classical
  obtain ⟨ν, hν, N, hN⟩ := exists_robust_cycle_power_parameters δ τ hδ hτ
  refine ⟨ν, hν, max N ⌈3 / δ⌉₊, ?_⟩
  intro V _ _ hn degrees hLower hUpper hAlmost hParity
  let n := Fintype.card V
  have hLarge : 3 ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp
    ((Nat.le_ceil (3 / δ)).trans (by
      have h := (le_max_right N ⌈3 / δ⌉₊).trans hn
      exact_mod_cast h))
  have hnPos : 0 < n := by
    by_contra! h
    have he : n = 0 := by omega
    norm_num [he] at hLarge
  have _ : NeZero n := ⟨by omega⟩
  obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp hnPos
  let D := (univ : Finset V).image degrees
  have hD : D.Nonempty := ⟨degrees v₀, mem_image_of_mem degrees (mem_univ _)⟩
  let d := D.min' hD
  obtain ⟨u, _, hu⟩ := mem_image.mp (min'_mem D hD)
  change degrees u = d at hu
  have hDu (v : V) : d ≤ degrees v ∧ degrees v ≤ d + 1 :=
    ⟨min'_le D _ (mem_image_of_mem degrees (mem_univ _)), hu ▸ hAlmost v u⟩
  have hdLow : δ * (n : ℝ) ≤ (d : ℝ) := by simpa only [hu] using hLower u
  have hdThree : 3 ≤ d := by
    have hh : 3 ≤ (d : ℝ) := by linarith only [hLarge, hdLow]
    exact_mod_cast hh
  let A := (univ : Finset V).filter (fun v => degrees v = d + 1)
  let j := A.card
  have hSum : (∑ v, degrees v) = n * d + j := by
    calc
      _ = ∑ v : V, (d + if degrees v = d + 1 then 1 else 0) := by
        apply sum_congr rfl
        intro v _
        obtain ⟨h1, h2⟩ := hDu v
        split <;> omega
      _ = _ := by rw [sum_add_distrib, sum_boole]; simp [n, j, A]
  rw [hSum] at hParity
  have hj : j ≤ n := card_le_univ A
  have hHigh : j ≠ 0 → d + 1 < n := by
    intro h
    obtain ⟨v, hv⟩ := card_pos.mp (Nat.pos_of_ne_zero h)
    exact (mem_filter.mp hv).2 ▸ hUpper v
  obtain ⟨r, hr, H, hH, hDegrees, hCard, hLoss⟩ := exists_cycle_degree_multiset n d j
    (by omega) (hu ▸ hUpper u) hj hHigh hParity
  have hrLower : δ * (n : ℝ) ≤ 3 * (r : ℝ) := by
    have h1 : (d : ℝ) ≤ 2 * (r : ℝ) + 1 := by exact_mod_cast hr
    have h2 : 3 ≤ (d : ℝ) := by exact_mod_cast hdThree
    linarith only [h1, h2, hdLow]
  have hExpand := hN n r ((le_max_left _ _).trans hn) hrLower H hLoss
  let p (v : V) : Prop := degrees v = d + 1
  let q (v : Fin n) : Prop := H.degree v = d + 1
  have hHighCard : Fintype.card {v // p v} = Fintype.card {v // q v} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact hCard.symm
  have hLowCard : Fintype.card {v // ¬ p v} = Fintype.card {v // ¬ q v} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hHighCard, Fintype.card_fin]
  let eHigh := Fintype.equivOfCardEq hHighCard
  let eLow := Fintype.equivOfCardEq hLowCard
  let e : V ≃ Fin n := (Equiv.sumCompl p).symm.trans
    ((Equiv.sumCongr eHigh eLow).trans (Equiv.sumCompl q))
  have hEquiv (v : V) : p v ↔ q (e v) := by
    by_cases hp : p v
    · have he : e v = (eHigh ⟨v, hp⟩).val := by
        simp [e, Equiv.sumCompl_symm_apply_of_pos hp]
      rw [he]
      exact ⟨fun _ => (eHigh ⟨v, hp⟩).property, fun _ => hp⟩
    · have he : e v = (eLow ⟨v, hp⟩).val := by
        simp [e, Equiv.sumCompl_symm_apply_of_neg hp]
      rw [he]
      exact ⟨fun h => (hp h).elim, fun h => ((eLow ⟨v, hp⟩).property h).elim⟩
  let G := H.comap e
  let hG : DecidableRel G.Adj := Classical.decRel _
  refine ⟨G, hG, ?_, ?_⟩
  · intro v
    have hh := (SimpleGraph.Iso.comap e H).degree_eq v
    change H.degree (e v) = G.degree v at hh
    have h1 := hDu v
    have h2 := hDegrees (e v)
    have h3 := hEquiv v
    change degrees v = d + 1 ↔ H.degree (e v) = d + 1 at h3
    rw [← hh]
    omega
  · exact expandsInside_of_induced_map G H e.toEmbedding (fun _ _ => Iff.rfl) ν τ univ
      (by simpa only [map_univ_equiv] using hExpand)

end OverfullWork.ChenShan
