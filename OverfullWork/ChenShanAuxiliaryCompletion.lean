module

public import OverfullWork.SparseDeficitCore
public import OverfullWork.KLOSRobustComponents

@[expose] public section

/-! Deficit estimates for the auxiliary completion in Chen–Shan,
Lemma 3.24 and the proof of Theorem 2.2. -/
namespace OverfullWork.ChenShan

open SimpleGraph Finset SparseDeficitCore OddCutDeficit KLOS PrunedCore
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The total deficit used in the first step of the proof of Theorem 2.2. -/
theorem totalDeficit_le_core_error (Z : Finset V) (k a : ℕ)
    (hCore : ∀ v ∉ Z, k - G.degree v ≤ a) :
    totalDeficit G k ≤ a * Fintype.card V + k * Z.card := by
  unfold totalDeficit
  rw [← sum_add_sum_compl Z (fun v => k - G.degree v)]
  have hZ : (∑ v ∈ Z, (k - G.degree v)) ≤ k * Z.card := by
    calc
      _ ≤ ∑ _ ∈ Z, k := sum_le_sum fun _ _ => Nat.sub_le _ _
      _ = _ := by simp [Nat.mul_comm]
  have hU : (∑ v ∈ Zᶜ, (k - G.degree v)) ≤ a * Fintype.card V := by
    calc
      _ ≤ ∑ _ ∈ Zᶜ, a := sum_le_sum fun v hv => hCore v (mem_compl.mp hv)
      _ = a * Zᶜ.card := by simp [Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ (card_le_univ _)
  omega

omit [DecidableEq V] in
/-- When a new vertex has at most one neighbor of deficiency one, its
neighbors on the original shore cost at least two units of deficit each,
with an allowance of one unit. -/
theorem single_auxiliary_vertex_deficit (S T : Finset V) (k : ℕ)
    (hSub : T ⊆ S) (hPositive : ∀ v ∈ T, 0 < k - G.degree v)
    (hOne : (T.filter fun v => k - G.degree v = 1).card ≤ 1) :
    2 * T.card ≤ (∑ v ∈ S, (k - G.degree v)) + 1 := by
  let δ (v : V) := k - G.degree v
  have hSum : 2 * T.card ≤ ∑ v ∈ T, (δ v + if δ v = 1 then 1 else 0) := by
    calc
      _ = ∑ _ ∈ T, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro v hv
        have h := hPositive v hv
        change 0 < δ v at h
        by_cases hEq : δ v = 1
        · simp [hEq]
        · simp only [ite_eq_right hEq, add_zero]
          omega
  rw [sum_add_distrib] at hSum
  have hMark : (∑ v ∈ T, if δ v = 1 then (1 : ℕ) else 0) ≤ 1 := by
    change (T.filter fun v => δ v = 1).card ≤ 1 at hOne
    rw [← sum_filter]
    simpa using hOne
  have hPart : (∑ v ∈ T, δ v) ≤ ∑ v ∈ S, δ v :=
    sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => Nat.zero_le _)
  change 2 * T.card ≤ (∑ v ∈ S, δ v) + 1
  omega

/-- The one-new-vertex case of the odd-set check in Lemma 3.24. Every
new edge at this vertex is simple, and `T` lists its neighbors in the
even original shore `S`. -/
theorem single_auxiliary_vertex_not_overfull (S T : Finset V) (k : ℕ)
    (hDegree : ∀ v, G.degree v ≤ k) (hS : Even S.card)
    (hSub : T ⊆ S) (hPositive : ∀ v ∈ T, 0 < k - G.degree v)
    (hOne : (T.filter fun v => k - G.degree v = 1).card ≤ 1) :
    internalEdges G S + T.card ≤ k * (S.card / 2) := by
  obtain ⟨j, hj⟩ := hS
  have hj' : S.card = 2 * j := by omega
  have hHalf : S.card / 2 = j := by omega
  have hCut := internal_cut_deficit_identity G k hDegree S
  rw [hj', Nat.mul_left_comm k 2 j] at hCut
  unfold deficitMass at hCut
  have hDeficit := single_auxiliary_vertex_deficit G S T k hSub hPositive hOne
  rw [hHalf]
  omega

/-- The large-cut claim on the auxiliary core in Lemma 3.24. The
smaller shore contains at least two vertices. Below the robust range
we use the minimum degree, and within the range we count robust
neighbors outside the shore. -/
theorem auxiliary_core_cut_large (k : ℕ) {ν τ : ℝ}
    (hk : 0 < k) (hν : 0 < ν) (hτ : τ ≤ 1 / 2)
    (hMin : 7 * (k : ℝ) / 8 ≤ G.minDegree)
    (hScale : τ * (Fintype.card V : ℝ) ≤ (k : ℝ) / 8)
    (hOrder : (k : ℝ) < (ν * (Fintype.card V : ℝ)) ^ 2)
    (hExpand : ExpandsInside G ν τ univ)
    (S : Finset V) (hTwo : 2 ≤ S.card) (hHalf : 2 * S.card ≤ Fintype.card V) :
    k < cutEdges G S := by
  let n := (Fintype.card V : ℝ)
  let s := (S.card : ℝ)
  have hn : 0 ≤ n := by positivity
  have hs : 0 ≤ s := by positivity
  have hTwoR : 2 ≤ s := by dsimp only [s]; exact_mod_cast hTwo
  have hHalfR : 2 * s ≤ n := by dsimp only [s, n]; exact_mod_cast hHalf
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  suffices h : (k : ℝ) < cutEdges G S by exact_mod_cast h
  by_cases hS : s < τ * n
  · have hShort : s ≤ (k : ℝ) / 8 := hS.le.trans hScale
    have hDeg : (G.minDegree : ℝ) * s ≤ incidences G S S + cutEdges G S := by
      have hMass := incidences_add_compl G S S
      rw [incidences_compl_self] at hMass
      have hh : G.minDegree * S.card ≤ ∑ v ∈ S, G.degree v := by
        calc
          _ = ∑ _ ∈ S, G.minDegree := by simp [Nat.mul_comm]
          _ ≤ _ := sum_le_sum (fun v _ => G.minDegree_le_degree v)
      have hNat := hh.trans_eq hMass.symm
      dsimp only [s]
      exact_mod_cast hNat
    have hInside : (incidences G S S : ℝ) ≤ s * s := by
      dsimp only [s]
      exact_mod_cast incidences_le_card_mul G S S
    have hRate : 3 * (k : ℝ) / 4 ≤ (G.minDegree : ℝ) - s := by
      linarith only [hMin, hShort]
    have hCost := mul_le_mul_of_nonneg_right hRate hs
    have hFloor := mul_le_mul_of_nonneg_left hTwoR (by positivity : 0 ≤ 3 * (k : ℝ) / 4)
    nlinarith only [hDeg, hInside, hCost, hFloor, hkR]
  · let R := robustNeighbourhoodIn G ν univ S
    let R₀ := R \ S
    have hUpper : s ≤ (1 - τ) * n := by
      have h := mul_le_mul_of_nonneg_right hτ hn
      nlinarith only [hHalfR, h]
    have hExp : s + ν * n ≤ R.card := by
      simpa only [card_univ] using hExpand S (subset_univ _) (by simpa only [card_univ] using le_of_not_gt hS)
        (by simpa only [card_univ] using hUpper)
    have hCount : (R.card : ℝ) ≤ (R₀.card : ℝ) + s := by
      dsimp only [R₀, s]
      exact_mod_cast (card_le_card_sdiff_add_card (s := R) (t := S))
    have hThreshold : ν * n ≤ (R₀.card : ℝ) := by linarith only [hCount, hExp]
    have hMass : (ν * n) * (R₀.card : ℝ) ≤ incidences G S R₀ := by
      unfold incidences
      push_cast
      calc
        _ = ∑ _ ∈ R₀, ν * n := by simp [mul_comm]
        _ ≤ _ := sum_le_sum fun v hv => (mem_filter.mp (mem_sdiff.mp hv).1).2
    have hCut : (incidences G S R₀ : ℝ) ≤ cutEdges G S := by
      rw [← incidences_compl_self]
      exact_mod_cast incidences_mono G (Subset.rfl : S ⊆ S)
        (fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2)
    have hMul := mul_le_mul_of_nonneg_left hThreshold (mul_nonneg hν.le hn)
    change (k : ℝ) < (ν * n) ^ 2 at hOrder
    nlinarith only [hCut, hMass, hMul, hOrder]

end OverfullWork.ChenShan
