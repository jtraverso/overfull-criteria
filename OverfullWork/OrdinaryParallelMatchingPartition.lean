module

public import OverfullWork.OrdinaryParallelFactorization

@[expose] public section


/-! Choose actual nonempty parallel matchings and pay their number
and sizes from a per-vertex excess bound. -/
namespace OverfullWork.EvenHamiltonFactorization

open Finset SimpleGraph MultiGraph CanonicalPairTriangle RobustExpansion
open scoped Classical
universe u

/-- Drop the empty equitable colour classes. The copy sum is unchanged. -/
theorem exists_nonempty_parallel_matching_partition
    {V : Type u} [Fintype V] [DecidableEq V] (M : MultiGraph V) (b ℓ m : ℕ)
    (hDeg : ∀ v, M.parallelExcess v ≤ b)
    (hPalette : 3*b/2 ≤ ℓ) (hMass : M.parallelCopies.edgeCount ≤ ℓ*m) :
    ∃ k : ℕ, k ≤ ℓ ∧ ∃ J : Fin k → MultiGraph V,
      sumCopies univ J = M.parallelCopies ∧
      (∀ i v, (J i).degree v ≤ 1) ∧
      ∀ i, 0 < (J i).edgeCount ∧ (J i).edgeCount ≤ m := by
  obtain ⟨C,hSize,hMatching⟩ := M.exists_parallel_copy_matchings b ℓ m hDeg hPalette hMass
  let S := (univ : Finset (Fin ℓ)).filter (fun i => 0 < (C.colourGraph i).edgeCount)
  let e : Fin S.card ≃ S := Fintype.equivOfCardEq (by simp)
  let J := fun i => C.colourGraph (e i).val
  refine ⟨S.card,(card_le_univ S).trans_eq (Fintype.card_fin ℓ),J,?_,
    fun i v => hMatching (e i).val v,fun i => ⟨(mem_filter.mp (e i).property).2,hSize (e i).val⟩⟩
  apply ext_mult
  intro t
  change (∑ i, (C.colourGraph (e i).val).mult t) = M.parallelCopies.mult t
  rw [Fintype.sum_equiv e _ (fun j => (C.colourGraph j.val).mult t) (by intro j; rfl),
    sum_coe_sort S (fun i => (C.colourGraph i).mult t),← C.sum_col]
  apply sum_subset (filter_subset _ _)
  intro j _ hj
  have hZero : (C.colourGraph j).edgeCount = 0 := by simpa [S] using hj
  have h := single_le_sum (f := (C.colourGraph j).mult) (s := univ)
    (fun _ _ => Nat.zero_le _) (mem_univ t)
  change (C.colourGraph j).mult t ≤ (C.colourGraph j).edgeCount at h
  change C.col t j = 0
  exact Nat.eq_zero_of_le_zero (h.trans_eq hZero)

set_option maxHeartbeats 2200000 in
/-- A regular multigraph with robust simple support and sufficiently
small parallel excess has a factorization on sufficiently large even
order. The tolerable excess is chosen before the multigraph. -/
theorem robust_regular_multigraph_colourable_small_parallel_excess
    (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (M : MultiGraph V) (r : ℕ),
        N ≤ Fintype.card V → Even (Fintype.card V) → α*(Fintype.card V:ℝ) ≤ (r:ℝ) →
        M.IsRegularOfDegree r → IsRealRobust M.supportGraph ν τ →
        (∀ v, (M.parallelExcess v:ℝ) ≤ ε*(Fintype.card V:ℝ)) →
        Nonempty (M.EdgeColoring r) := by
  obtain ⟨τ,hτ,hMain⟩ := robust_regular_multigraph_colourable_of_parallel_matchings.{u} α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν
  obtain ⟨μ,hμ,N₀,hN₀⟩ := hMain ν hν
  let paletteRate := min (μ/16) (α/64)
  let ε := min (paletteRate/4) (paletteRate*μ^4/4)
  have hPaletteRate : 0 < paletteRate := lt_min (by positivity) (by positivity)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (max (1/paletteRate) (2/μ^4))
  refine ⟨ε,hε,max N₀ N₁,?_⟩
  intro V _ _ M r hSize hEven hDegree hReg hRob hExcess
  let n := Fintype.card V
  let b := ⌊ε*(n:ℝ)⌋₊
  let ℓ := ⌈paletteRate*(n:ℝ)⌉₊
  let m := ⌊μ^4*(n:ℝ)⌋₊
  have hn := Nat.cast_nonneg (α := ℝ) n
  have hn₁ := hN₁.trans (show (N₁:ℝ) ≤ (n:ℝ) by exact_mod_cast (le_max_right _ _).trans hSize)
  have hPaletteRoom : 1 ≤ paletteRate*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hPaletteRate).mp ((le_max_left _ _).trans hn₁)
  have hμn : 2 ≤ μ^4*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ (pow_pos hμ 4)).mp ((le_max_right _ _).trans hn₁)
  have hℓ : paletteRate*(n:ℝ) ≤ (ℓ:ℝ) := Nat.le_ceil _
  have hℓ' : (ℓ:ℝ) ≤ 2*paletteRate*(n:ℝ) := by
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ paletteRate*(n:ℝ) by positivity)).le
    change (ℓ:ℝ) ≤ _ at hh
    nlinarith only [hh,hPaletteRoom]
  have hm : μ^4*(n:ℝ)/2 ≤ (m:ℝ) := by
    have hh := Nat.lt_floor_add_one (μ^4*(n:ℝ))
    change _ < (m:ℝ)+1 at hh
    linarith only [hh,hμn]
  have hm' : (m:ℝ) ≤ μ^4*(n:ℝ) := Nat.floor_le (by positivity)
  have hb : (b:ℝ) ≤ ε*(n:ℝ) := Nat.floor_le (by positivity)
  have hEx (v : V) : M.parallelExcess v ≤ b := (Nat.le_floor_iff (by positivity)).mpr (hExcess v)
  have hPal : 3*b/2 ≤ ℓ := by
    have hh := mul_le_mul_of_nonneg_right (show ε ≤ paletteRate/4 from min_le_left _ _) hn
    have hThree : 3*b ≤ ℓ := by
      exact_mod_cast (show (3:ℝ)*(b:ℝ) ≤ (ℓ:ℝ) by nlinarith only [hb,hh,hℓ,hPaletteRoom])
    exact (Nat.div_le_self _ _).trans hThree
  have hSum : 2*M.parallelCopies.edgeCount ≤ n*b := by
    rw [←M.parallelCopies.sum_degrees_eq_twice_edgeCount]
    calc
      _ ≤ ∑ _v : V, b := sum_le_sum (fun v _ => by rw [degree_parallelCopies]; exact hEx v)
      _ = n*b := by simp [n]
  have hMass : M.parallelCopies.edgeCount ≤ ℓ*m := by
    have hSumR : 2*(M.parallelCopies.edgeCount:ℝ) ≤ (n:ℝ)*(b:ℝ) := by exact_mod_cast hSum
    have hB' : (b:ℝ) ≤ (paletteRate*μ^4/4)*(n:ℝ) := hb.trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hn)
    have hprod := mul_le_mul hℓ hm (by positivity : 0 ≤ μ^4*(n:ℝ)/2) (Nat.cast_nonneg (α := ℝ) ℓ)
    exact_mod_cast (show (M.parallelCopies.edgeCount:ℝ) ≤ (ℓ:ℝ)*(m:ℝ) by
      nlinarith only [hSumR,mul_le_mul_of_nonneg_left hB' hn,hprod,
        mul_nonneg (mul_nonneg hPaletteRate.le (pow_nonneg hμ.le 4)) (sq_nonneg (n:ℝ))])
  obtain ⟨k,hk,J,hJ,hMatching,hCount⟩ :=
    exists_nonempty_parallel_matching_partition M b ℓ m hEx hPal hMass
  have hkR : (k:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hk
  have hBudget₁ : 2*(k:ℝ) ≤ μ*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (show paletteRate ≤ μ/16 from min_le_left _ _) hn
    nlinarith only [hkR,hℓ',h,mul_nonneg hμ.le hn]
  have hBudget₂ : 8*(k:ℝ) ≤ α*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (show paletteRate ≤ α/64 from min_le_right _ _) hn
    nlinarith only [hkR,hℓ',h,mul_nonneg hα.le hn]
  exact hN₀ M r k J ((le_max_left _ _).trans hSize) hEven hDegree hReg hRob hJ hMatching
    (fun i => ⟨(hCount i).1, (show ((J i).edgeCount:ℝ) ≤ (m:ℝ) by exact_mod_cast (hCount i).2).trans hm'⟩)
    hBudget₁ hBudget₂

end OverfullWork.EvenHamiltonFactorization
