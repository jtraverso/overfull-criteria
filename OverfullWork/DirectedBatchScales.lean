module

public import Mathlib.Analysis.Real.Sqrt
public import OverfullWork.DirectedBatchBlockSchedule

@[expose] public section


/-! A finite scale hierarchy for GGKLO Lemma 7.3(iii).
The next allowance dominates twice the square root of the previous one.
Choosing the scales backwards makes the top allowance independent of
the host and of the number of individual layouts. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset
open scoped BigOperators Classical

private noncomputable def earlierScale (top : ℝ) : ℕ → ℝ
  | 0 => top
  | n+1 => (earlierScale top n/2)^2

private theorem earlierScale_bounds (top : ℝ) (hTop : 0 < top) (hOne : top ≤ 1)
    (n : ℕ) : 0 < earlierScale top n ∧ earlierScale top n ≤ top := by
  induction n with
  | zero => exact ⟨hTop,le_rfl⟩
  | succ n ih =>
    change 0 < (earlierScale top n/2)^2 ∧ (earlierScale top n/2)^2 ≤ top
    refine ⟨pow_pos (div_pos ih.1 (by norm_num)) _,?_⟩
    have hx : earlierScale top n ≤ 1 := ih.2.trans hOne
    have hs : (earlierScale top n/2)^2 ≤ earlierScale top n := by
      nlinarith only [mul_nonneg ih.1.le (sub_nonneg.mpr hx)]
    exact hs.trans ih.2

private theorem linear_cost_le_next (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hSmall : x ≤ 1/(r+1)^2) : (r+1)*x ≤ 2*√x := by
  have hs : (√x)^2 = x := Real.sq_sqrt hx
  have hS : 0 ≤ √x := Real.sqrt_nonneg _
  have hR : 0 < r+1 := by linarith only [hr]
  have hp : (√x)^2 ≤ (1/(r+1))^2 := by
    rw [hs,div_pow,one_pow]
    exact hSmall
  have hq : √x ≤ 1/(r+1) :=
    (sq_le_sq₀ hS (by positivity)).mp hp
  have hMul : (r+1)*√x ≤ 1 := by
    rwa [mul_comm,← le_div_iff₀ hR]
  have he := mul_le_mul_of_nonneg_right hMul hS
  calc
    (r+1)*x = (r+1)*√x*√x := by calc
      (r+1)*x = (r+1)*(√x)^2 := congrArg (fun t : ℝ => (r+1)*t) hs.symm
      _ = _ := by ring
    _ ≤ 1*√x := he
    _ ≤ 2*√x := by linarith only [hS]

/-- Choose all allowances before the graph order. Every prefix budget
is then valid for arbitrary nonnegative stage costs bounded linearly
by the corresponding allowance. -/
theorem exists_batch_scale_schedule (K : ℕ) (top r : ℝ) (hTop : 0 < top) (hr : 0 ≤ r) :
    ∃ scale : ℕ → ℝ,
      (∀ i ≤ K, 0 < scale i ∧ scale i ≤ top) ∧
      (∀ i < K, scale (i+1) = 2*√(scale i)) ∧
      ∀ loss : ℕ → ℝ, (∀ i < K, 0 ≤ loss i ∧ loss i ≤ r*scale i) →
        ∀ m ≤ K, scale 0+(∑ i ∈ range m,loss i) ≤ scale m := by
  let top' := min top (min 1 (1/(r+1)^2))
  have hTop' : 0 < top' := lt_min hTop (lt_min (by norm_num) (by positivity))
  have hTopOne : top' ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hTopBound : top' ≤ 1/(r+1)^2 := (min_le_right _ _).trans (min_le_right _ _)
  let scale (i : ℕ) : ℝ := earlierScale top' (K-i)
  have hScale (i : ℕ) := earlierScale_bounds top' hTop' hTopOne (K-i)
  have hNext (i : ℕ) (hi : i < K) : scale (i+1) = 2*√(scale i) := by
    have he : K-i = (K-(i+1))+1 := by omega
    have hEq : scale i = (scale (i+1)/2)^2 := by
      change earlierScale top' (K-i) = _
      rw [he]
      rfl
    rw [hEq,Real.sqrt_sq (by exact div_nonneg (hScale _).1.le (by norm_num))]
    ring
  refine ⟨scale,fun i _ => ⟨(hScale i).1,(hScale i).2.trans (min_le_left _ _)⟩,hNext,?_⟩
  intro loss hLoss m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    have hi : m < K := by omega
    have hPrev := ih hi.le
    have hStage := (hLoss m hi).2
    have hStep := linear_cost_le_next (scale m) r (hScale m).1.le hr ((hScale m).2.trans hTopBound)
    rw [sum_range_succ,hNext m hi]
    linarith only [hPrev,hStage,hStep]

/-- Equation (7.1) with the integer ceiling costs made explicit.
Summing the charges of a stage pays once for each small batch's ceiling
and in proportion to the total number of processed layouts. -/
theorem sum_cyclic_reserve_cost_le {J : Type*} (S : Finset J) (k : ℕ) (hk : 0 < k)
    (m b cap : J → ℕ) :
    (∑ i ∈ S, ((b i+2*cap i+2*((m i+k-1)/k):ℕ):ℝ)) ≤
      (∑ i ∈ S, ((b i+2*cap i:ℕ):ℝ)) +
      2*((∑ i ∈ S,(m i:ℝ))/(k:ℝ)+(S.card:ℝ)) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have ceilBound (x : ℕ) : (((x+k-1)/k:ℕ):ℝ) ≤ (x:ℝ)/(k:ℝ)+1 := by
    have hh : (((x+k-1)/k:ℕ):ℝ)*(k:ℝ) ≤ (x:ℝ)+(k:ℝ) := by
      exact_mod_cast (Nat.div_mul_le_self (x+k-1) k).trans (Nat.sub_le _ _)
    have h := (le_div_iff₀ hkR).mpr hh
    rw [add_div,div_self hkR.ne'] at h
    exact h
  calc
    _ ≤ ∑ i ∈ S, (((b i+2*cap i:ℕ):ℝ) + 2*((m i:ℝ)/(k:ℝ)+1)) := by
      apply sum_le_sum
      intro i _
      push_cast
      linarith only [ceilBound (m i)]
    _ = _ := by
      rw [sum_add_distrib,← mul_sum,sum_add_distrib]
      simp [div_eq_mul_inv,sum_mul]

/-- A bounded number of stages suffices for any prescribed positive
fraction of the host order per stage. The stage count is chosen before
the host and can be used in the backward scale hierarchy. -/
theorem exists_layout_groups_below_fraction (β : ℝ) (hβ : 0 < β) :
    ∃ k N : ℕ, 0 < k ∧ ∀ {J : Type*} [Fintype J] (n : ℕ), N ≤ n → Fintype.card J ≤ n →
      ∃ group : Fin k → Finset J,
        (∀ i, ((group i).card:ℝ) ≤ β*(n:ℝ)) ∧
        Pairwise (fun i j => Disjoint (group i) (group j)) ∧
        (univ : Finset (Fin k)).biUnion group = (univ : Finset J) := by
  obtain ⟨K,hK⟩ := exists_nat_ge (2/β)
  let k := max 1 K
  have hk : 0 < k := by omega
  have hScale : (2:ℝ) ≤ β*(k:ℝ) := by
    have h := hK.trans (show (K:ℝ) ≤ (k:ℝ) by exact_mod_cast le_max_right 1 K)
    have hp := (div_le_iff₀ hβ).mp h
    linarith only [hp]
  refine ⟨k,k,hk,?_⟩
  intro J _ n hn hJ
  obtain ⟨group,hSize,hDis,hCover⟩ := exists_balanced_layout_groups (J := J) hk
  refine ⟨group,?_,hDis,hCover⟩
  intro i
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hCeil : ((((Fintype.card J+k-1)/k:ℕ)):ℝ) ≤ (n:ℝ)/(k:ℝ)+1 := by
    have hd : ((Fintype.card J+k-1)/k)*k ≤ n+k :=
      (Nat.div_mul_le_self _ _).trans (by omega)
    have hd' : ((((Fintype.card J+k-1)/k:ℕ)):ℝ)*(k:ℝ) ≤ (n:ℝ)+(k:ℝ) := by exact_mod_cast hd
    have hp := (le_div_iff₀ hkR).mpr hd'
    rw [add_div,div_self hkR.ne'] at hp
    exact hp
  have hRate : (n:ℝ)/(k:ℝ) ≤ (β/2)*(n:ℝ) := by
    apply (div_le_iff₀ hkR).mpr
    have h := mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg (α := ℝ) n)
    nlinarith only [h]
  have hOne : (1:ℝ) ≤ (β/2)*(n:ℝ) := by
    have hh : (k:ℝ) ≤ n := by exact_mod_cast hn
    have h := mul_le_mul_of_nonneg_left hh hβ.le
    linarith only [h,hScale]
  exact (show ((group i).card:ℝ) ≤ _ by exact_mod_cast hSize i).trans
    (hCeil.trans (by linarith only [hRate,hOne]))

end OverfullWork.DirectedSpanningConfiguration
