module

public import OverfullWork.ChenShanAuxiliaryRobustCore
public import OverfullWork.ChenShanCyclePower
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset KLOS PrunedCore RobustExpansion
open scoped Classical

/-- Consecutive blocks whose sizes are the quotient or the quotient plus one.
The vertices in the same or consecutive blocks lie within twice the larger size. -/
theorem exists_consecutive_cycle_blocks (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    ∃ f : Fin n → Fin m,
      (∀ i, n / m ≤ (assignmentPart f i).card ∧ (assignmentPart f i).card ≤ n / m + 1) ∧
      ∀ v w, (f w = f v ∨ (pathGraph m).Adj (f w) (f v)) →
        w.val - v.val ≤ 2 * (n / m + 1) ∧ v.val - w.val ≤ 2 * (n / m + 1) := by
  let q := n / m
  let s := n % m
  let b (i : ℕ) := i * q + min i s
  have hq : 0 < q := Nat.div_pos hmn hm
  have hs : s < m := Nat.mod_lt n hm
  have hZero : b 0 = 0 := by simp [b]
  have hEnd : b m = n := by
    simp only [b, min_eq_right hs.le]
    exact Nat.div_add_mod n m
  have hStep (i : ℕ) : b i + q ≤ b (i + 1) ∧ b (i + 1) ≤ b i + q + 1 := by
    change i * q + min i s + q ≤ (i + 1) * q + min (i + 1) s ∧
      (i + 1) * q + min (i + 1) s ≤ i * q + min i s + q + 1
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hMono : StrictMono b := strictMono_nat_of_lt_succ (fun i => by
    have h := (hStep i).1
    omega)
  have hPick (v : Fin n) : ∃ i : Fin m, b i.val ≤ v.val ∧ v.val < b (i.val + 1) := by
    have hEx : ∃ j : ℕ, v.val < b j := ⟨m, by simpa only [hEnd] using v.isLt⟩
    let j := Nat.find hEx
    have hj : v.val < b j := Nat.find_spec hEx
    have hjm : j ≤ m := Nat.find_min' hEx (by simpa only [hEnd] using v.isLt)
    have hjp : 0 < j := by
      by_contra! h
      have he : j = 0 := by omega
      rw [he, hZero] at hj
      omega
    refine ⟨⟨j - 1, by omega⟩, ?_, ?_⟩
    · exact Nat.le_of_not_gt (Nat.find_min hEx (show j - 1 < j by omega))
    · simpa only [Nat.sub_add_cancel hjp] using hj
  let f (v : Fin n) := (hPick v).choose
  have hF (v : Fin n) : b (f v).val ≤ v.val ∧ v.val < b ((f v).val + 1) :=
    (hPick v).choose_spec
  have hFiber (i : Fin m) (v : Fin n) : f v = i ↔ b i.val ≤ v.val ∧ v.val < b (i.val + 1) := by
    constructor
    · intro h
      simpa only [← h] using hF v
    · intro h
      apply Fin.ext
      have hv := hF v
      by_contra he
      rcases lt_or_gt_of_ne he with hlt | hgt
      · have hb := hMono.monotone (show (f v).val + 1 ≤ i.val by omega)
        omega
      · have hb := hMono.monotone (show i.val + 1 ≤ (f v).val by omega)
        omega
  refine ⟨f, ?_, ?_⟩
  · intro i
    let T := Ico (b i.val) (b (i.val + 1))
    have hT (x : ℕ) (hx : x ∈ T) : x < n := by
      have hi := (mem_Ico.mp hx).2
      have hb := hMono.monotone (show i.val + 1 ≤ m by omega)
      exact hi.trans_le (hEnd ▸ hb)
    have hEq : assignmentPart f i = T.attachFin hT := by
      ext v
      simp only [assignmentPart, mem_filter, mem_univ, true_and, mem_attachFin, T, mem_Ico, hFiber]
    rw [hEq, card_attachFin, Nat.card_Ico]
    have hi := hStep i.val
    change q ≤ b (i.val + 1) - b i.val ∧ b (i.val + 1) - b i.val ≤ q + 1
    omega
  · intro v w hNear
    have hv := hF v
    have hw := hF w
    have hIndex : (f w).val ≤ (f v).val + 1 ∧ (f v).val ≤ (f w).val + 1 := by
      rcases hNear with he | ha
      · rw [he]
        omega
      · rw [pathGraph_adj] at ha
        omega
    have hvb := hMono.monotone (show (f v).val + 1 ≤ (f w).val + 2 by omega)
    have hwb := hMono.monotone (show (f w).val + 1 ≤ (f v).val + 2 by omega)
    have hv₀ := (hStep (f v).val).2
    have hv₁ := (hStep ((f v).val + 1)).2
    have hw₀ := (hStep (f w).val).2
    have hw₁ := (hStep ((f w).val + 1)).2
    change b ((f v).val + 2) ≤ b ((f v).val + 1) + q + 1 at hv₁
    change b ((f w).val + 2) ≤ b ((f w).val + 1) + q + 1 at hw₁
    change w.val - v.val ≤ 2 * (q + 1) ∧ v.val - w.val ≤ 2 * (q + 1)
    omega


/-- The robustness part of Lemma 3.23, for any graph containing the
specified power of the cycle except for at most one edge at each vertex. -/
theorem exists_robust_cycle_power_parameters (δ τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ N : ℕ, ∀ n r : ℕ, ∀ [NeZero n], N ≤ n →
      δ * (n : ℝ) ≤ 3 * (r : ℝ) →
      ∀ H : SimpleGraph (Fin n), ∀ [DecidableRel H.Adj],
      (∀ v, ((univ : Finset (Fin n)).filter
        (fun w => (auxiliaryCyclePower n r).Adj v w ∧ ¬ H.Adj v w)).card ≤ 1) →
      ExpandsInside H ν τ univ := by
  let m := ⌈8 / δ⌉₊
  have hmR : 8 / δ ≤ (m : ℝ) := Nat.le_ceil _
  have hm : 0 < m := by
    have hPos := (show 0 < 8 / δ by positivity).trans_le hmR
    exact_mod_cast hPos
  obtain ⟨ν, hν, hντ, N, hN⟩ := exists_auxiliary_block_parameters m hm τ hτ
  refine ⟨ν, hν, max (max N m) ⌈24 / δ⌉₊, ?_⟩
  intro n r _ hn hr H _ hDel
  have hmn : m ≤ n := le_max_right N m |>.trans (le_max_left _ _) |>.trans hn
  have hNn : N ≤ n := le_max_left N m |>.trans (le_max_left _ _) |>.trans hn
  have hCeil : ⌈24 / δ⌉₊ ≤ n := (le_max_right _ _).trans hn
  have hnR : 24 / δ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hCeil)
  have hδn : 24 ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnR
  have hδm : 8 ≤ (m : ℝ) * δ := (div_le_iff₀ hδ).mp hmR
  let q := n / m
  have hq : 1 ≤ q := Nat.div_pos hmn hm
  have hmPos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hqPos : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hDiv : m * q ≤ n := Nat.mul_div_le n m
  have hDivUp : n ≤ m * (q + 1) := by
    have hh := Nat.div_add_mod n m
    have hs := Nat.mod_lt n hm
    change m * q + n % m = n at hh
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hFat : n ≤ (2 * m) * q := by
    calc
      n ≤ m * (q + 1) := hDivUp
      _ ≤ m * (2 * q) := Nat.mul_le_mul_left m (by omega)
      _ = (2 * m) * q := by ring
  have hFatR : (n : ℝ) / (2 * (m : ℝ)) ≤ (q : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh : (n : ℝ) ≤ (2 * (m : ℝ)) * (q : ℝ) := by exact_mod_cast hFat
    simpa only [mul_comm] using hh
  have hRad : 2 * (q + 1) ≤ r := by
    have hDivR : (m : ℝ) * (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hDiv
    have hOne := mul_le_mul_of_nonneg_right hδm hqPos
    have hTwo := mul_le_mul_of_nonneg_right hDivR hδ.le
    have hBound : 2 * ((q : ℝ) + 1) ≤ (r : ℝ) := by
      nlinarith only [hOne, hTwo, hδn, hr]
    exact_mod_cast hBound
  obtain ⟨f, hf, hDist⟩ := exists_consecutive_cycle_blocks n m hm hmn
  obtain ⟨hThreshold, hFind, hSurplus⟩ := hN n hNn
  refine auxiliary_expands_after_one_deletion H (auxiliaryCyclePower n r)
    (pathGraph m) (pathGraph_preconnected m) f ((n : ℝ) / (2 * (m : ℝ))) ν τ hντ
    (by simpa only [Fintype.card_fin] using hThreshold)
    (by simpa only [Fintype.card_fin] using hFind)
    (by simpa only [Fintype.card_fin] using hSurplus) ?_ ?_ hDel
  · intro i
    exact hFatR.trans (by exact_mod_cast (hf i).1)
  · intro v w hNear hne
    obtain ⟨hvw, hwv⟩ := hDist v w hNear
    rcases lt_or_gt_of_ne hne with h | h
    · exact auxiliaryCyclePower_adj_of_sub_le h (hvw.trans hRad)
    · exact (auxiliaryCyclePower_adj_of_sub_le h (hwv.trans hRad)).symm

end OverfullWork.ChenShan
