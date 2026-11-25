module

public import OverfullWork.ChenShanCycleRealization
public import OverfullWork.ChenShanBalancedAuxiliary

@[expose] public section

namespace OverfullWork.ChenShan

/-- The least order at least both `n` and `k + 1` that has the parity of `n`. -/
def auxiliaryOrder (n k : ℕ) : ℕ :=
  max n (k + 1) + if (max n (k + 1)) % 2 = n % 2 then 0 else 1

theorem auxiliaryOrder_spec (n k : ℕ) :
    n ≤ auxiliaryOrder n k ∧ k < auxiliaryOrder n k ∧
      (auxiliaryOrder n k) % 2 = n % 2 ∧ auxiliaryOrder n k ≤ max n (k + 1) + 1 ∧
      (∀ m, n ≤ m → k < m → m % 2 = n % 2 → auxiliaryOrder n k ≤ m) := by
  have hn := le_max_left n (k + 1)
  have hk := le_max_right n (k + 1)
  unfold auxiliaryOrder
  split <;> refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  all_goals
    intro m hnm hkm hp
    have hm := max_le hnm (show k + 1 ≤ m by omega)
    omega

/-- The deficit budget in Lemma 3.24 can be taken to be `α / 16`
once `α n ≥ 16`. The auxiliary degree remains at least `7k / 8`
and at least `α m / 4`. -/
theorem auxiliaryOrder_deficit_budget (n k s : ℕ) (α : ℝ) (hα : 0 < α)
    (hn : 2 ≤ n) (hLarge : 16 ≤ α * (n : ℝ))
    (hkLo : α * (n : ℝ) ≤ (k : ℝ)) (hkHi : k ≤ 2 * n)
    (hs : (s : ℝ) ≤ (α / 16) * (n : ℝ) ^ 2) :
    let m := auxiliaryOrder n k
    let b := ⌈(s : ℝ) / (m : ℝ)⌉₊
    m ≤ 3 * n ∧ s ≤ b * m ∧ (b : ℝ) ≤ (k : ℝ) / 8 ∧
      α * (m : ℝ) / 4 ≤ (k : ℝ) - (b : ℝ) := by
  dsimp only
  let m := auxiliaryOrder n k
  let b := ⌈(s : ℝ) / (m : ℝ)⌉₊
  change m ≤ 3 * n ∧ s ≤ b * m ∧ (b : ℝ) ≤ (k : ℝ) / 8 ∧
    α * (m : ℝ) / 4 ≤ (k : ℝ) - (b : ℝ)
  obtain ⟨hmn, _, _, hmU, _⟩ := auxiliaryOrder_spec n k
  have hmThree : m ≤ 3 * n := by
    have hm := max_le (show n ≤ 2 * n + 1 by omega) (show k + 1 ≤ 2 * n + 1 by omega)
    change m ≤ _ at hmU
    omega
  have hmPos : 0 < (m : ℝ) := by
    have h : 0 < m := by omega
    exact_mod_cast h
  have hmNR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmn
  have hMean : (s : ℝ) / (m : ℝ) ≤ (α / 16) * (n : ℝ) := by
    apply (div_le_iff₀ hmPos).mpr
    have h := mul_le_mul_of_nonneg_left hmNR (show 0 ≤ (α / 16) * (n : ℝ) by positivity)
    nlinarith only [h, hs]
  have hCeil : (b : ℝ) < (s : ℝ) / (m : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hBudget : s ≤ b * m := by
    have h : (s : ℝ) ≤ (b : ℝ) * (m : ℝ) :=
      (div_le_iff₀ hmPos).mp (Nat.le_ceil _)
    exact_mod_cast h
  have hb : (b : ℝ) ≤ (k : ℝ) / 8 := by linarith only [hCeil, hMean, hLarge, hkLo]
  have hmR : (m : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hmThree
  have hScale := mul_le_mul_of_nonneg_left hmR hα.le
  refine ⟨hmThree, hBudget, hb, ?_⟩
  nlinarith only [hScale, hb, hkLo, hLarge]


open Finset SimpleGraph KLOS PrunedCore RobustExpansion
open scoped Classical in
/-- The two new parts in the completion: the simple bipartite attachment
and a simple robust graph on the new vertices with the remaining degrees. -/
theorem exists_robust_auxiliary_attachment (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ N : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V],
      ∀ k : ℕ, ∀ d : V → ℕ,
      let n := Fintype.card V
      N ≤ n → α * (n : ℝ) ≤ (k : ℝ) → k ≤ 2 * n → (∀ v, d v ≤ k) →
      let s := ∑ v, d v
      (s : ℝ) ≤ (α / 16) * (n : ℝ) ^ 2 → s % 2 = (n * k) % 2 →
      let m := auxiliaryOrder n k
      let b := ⌈(s : ℝ) / (m : ℝ)⌉₊
      ∃ f : V → Finset (Fin m), ∃ H : SimpleGraph (Fin m), ∃ _ : DecidableRel H.Adj,
        (∀ v, (f v).card = d v) ∧
        (∀ w, ((univ : Finset V).filter (fun v => d v = 1 ∧ w ∈ f v)).card ≤ 1) ∧
        (∀ w, (auxiliaryCrossGraph f).degree (.inr w) + H.degree w = k) ∧
        (∀ w, k - b ≤ H.degree w) ∧ ExpandsInside H ν τ univ := by
  obtain ⟨ν, hν, N, hN⟩ := exists_robust_graph_with_prescribed_degrees (α / 4) τ (by positivity) hτ
  refine ⟨ν, hν, max (max N 2) ⌈16 / α⌉₊, ?_⟩
  intro V _ _ k d n hn hkLo hkHi hD s hs hParity m b
  obtain ⟨hmn, hkm, hmp, _, _⟩ := auxiliaryOrder_spec n k
  change n ≤ m at hmn
  change k < m at hkm
  change m % 2 = n % 2 at hmp
  have hnTwo : 2 ≤ n := (le_max_right N 2).trans ((le_max_left _ _).trans hn)
  have hNn : N ≤ n := (le_max_left N 2).trans ((le_max_left _ _).trans hn)
  have hCeil : ⌈16 / α⌉₊ ≤ n := (le_max_right _ _).trans hn
  have hnLarge : 16 ≤ α * (n : ℝ) := by
    have h := (div_le_iff₀ hα).mp ((Nat.le_ceil (16 / α)).trans
      (show (↑⌈16 / α⌉₊ : ℝ) ≤ (n : ℝ) by exact_mod_cast hCeil))
    rwa [mul_comm] at h
  obtain ⟨_, hbSum, hbK, hbLower⟩ :=
    auxiliaryOrder_deficit_budget n k s α hα hnTwo hnLarge hkLo hkHi hs
  have hNonempty : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨f, hRows, hBalance, hOne⟩ := exists_balanced_auxiliary_neighbours
    (W := Fin m) d (fun v => by simpa only [Fintype.card_fin] using (hD v).trans hkm.le)
    (by
      rw [Fintype.card_fin]
      exact (card_le_univ _).trans hmn)
  let c (w : Fin m) := ((univ : Finset V).filter (fun v => w ∈ f v)).card
  have hc (w : Fin m) : c w ≤ b :=
    auxiliary_degree_le_of_balance f d b hRows hBalance
      (by simpa only [Fintype.card_fin] using hbSum) w
  have hb : b ≤ k := by
    have hh : (b : ℝ) ≤ (k : ℝ) := by
      have hk : 0 ≤ (k : ℝ) := by positivity
      linarith only [hbK, hk]
    exact_mod_cast hh
  have hcK (w : Fin m) : c w ≤ k := (hc w).trans hb
  have hSum : ∑ w : Fin m, c w = s := by
    unfold c
    simp only [card_filter]
    rw [sum_comm]
    change ∑ v : V, (∑ w : Fin m, if w ∈ f v then 1 else 0) = ∑ v : V, d v
    apply sum_congr rfl
    intro v _
    rw [sum_boole, show ((univ : Finset (Fin m)).filter (fun z => z ∈ f v)) = f v by ext z; simp]
    exact hRows v
  have hSumDegree : (∑ w : Fin m, (k - c w)) + s = m * k := by
    rw [← hSum, ← sum_add_distrib]
    simp [Nat.sub_add_cancel (hcK _)]
  have hmParity : (m * k) % 2 = (n * k) % 2 := by
    rw [Nat.mul_mod m k, Nat.mul_mod n k, hmp]
  have hNewParity : (∑ w : Fin m, (k - c w)) % 2 = 0 := by omega
  obtain ⟨H, hH, hDeg, hExp⟩ := hN (V := Fin m)
    (by simpa only [Fintype.card_fin] using hNn.trans hmn) (fun w => k - c w)
    (fun w => by
      rw [Fintype.card_fin, Nat.cast_sub (hcK w)]
      have hcw : (c w : ℝ) ≤ (b : ℝ) := by exact_mod_cast hc w
      nlinarith only [hbLower, hcw])
    (fun w => by rw [Fintype.card_fin]; exact (Nat.sub_le _ _).trans_lt hkm)
    (fun w z => by have h := hBalance z w; change c z ≤ c w + 1 at h; omega) hNewParity
  refine ⟨f, H, hH, hRows, ?_, ?_, ?_, hExp⟩
  · intro w
    simpa only [filter_filter] using hOne w
  · intro w
    rw [auxiliaryCrossGraph_degree_right, hDeg]
    change c w + (k - c w) = k
    exact (Nat.add_comm _ _).trans (Nat.sub_add_cancel (hcK w))
  · intro w
    rw [hDeg]
    exact Nat.sub_le_sub_left (hc w) k

end OverfullWork.ChenShan
