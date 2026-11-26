module

public import OverfullWork.ChenShanNestedSizes
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Filter Real
open scoped Topology BigOperators

/-- The combined bad-event bound over distinct retained orders tends
to zero as their minimum tends to infinity. -/
theorem exists_nested_sampling_budget (C a ε : ℝ)
    (hC : 0 ≤ C) (ha : 0 < a) (hε : 0 < ε) :
    ∃ h : ℕ, ∀ S : Finset ℕ, (∀ n ∈ S, h ≤ n) →
      (∑ n ∈ S, C*(n:ℝ)*exp (-a*n)) < ε := by
  let f (n : ℕ) := C*(n:ℝ)*exp (-a*n)
  have hSum : Summable f := by
    have hh := (summable_pow_mul_exp_neg_nat_mul 1 ha).mul_left C
    simpa only [pow_one,mul_assoc,f] using hh
  have hf (n : ℕ) : 0 ≤ f n := by dsimp only [f]; positivity
  have hNear : Set.Ioi ((∑' k, f k)-ε) ∈ 𝓝 (∑' k, f k) :=
    Ioi_mem_nhds (by linarith only [hε])
  have hEventually :
      ∀ᶠ n in atTop, (∑' k, f k)-ε < ∑ k ∈ range n, f k :=
    hSum.hasSum.tendsto_sum_nat.eventually hNear
  obtain ⟨h,hh⟩ := eventually_atTop.mp hEventually
  refine ⟨h,fun S hS => ?_⟩
  have hDis : Disjoint (range h) S := by
    apply disjoint_left.mpr
    intro n hn hn'
    exact (Nat.not_le_of_gt (mem_range.mp hn)) (hS n hn')
  have hTotal := hSum.sum_le_tsum (range h ∪ S) (fun n _ => hf n)
  rw [sum_union hDis] at hTotal
  linarith only [hTotal,hh h le_rfl]

/-- Strict decrease before the cutoff lets us sum by distinct orders
without grouping the nested levels into intervals. -/
theorem exists_nested_core_with_sampling_budget (ρ C a ε : ℝ)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1/2) (hC : 0 ≤ C) (ha : 0 < a) (hε : 0 < ε) :
    ∃ h : ℕ, 4 ≤ h ∧ ∀ m ≥ h, ∃ l : ℕ,
      (∀ i ≤ l, h ≤ nestedCoreSize ρ m i) ∧
      nestedCoreSize ρ m (l+1) < h ∧ (nestedCoreSize ρ m l : ℝ) < h/ρ ∧
      (∑ i ∈ range (l+1),
        C*(nestedCoreSize ρ m i : ℝ)*exp (-a*nestedCoreSize ρ m i)) < ε := by
  classical
  obtain ⟨h₀,hh₀⟩ := exists_nested_sampling_budget C a ε hC ha hε
  let h := max 4 h₀
  refine ⟨h,le_max_left _ _,fun m hm => ?_⟩
  obtain ⟨l,hKeep,hExit,hTop⟩ :=
    exists_last_nested_core_size ρ hρ hρ₁ m h (le_max_left _ _) hm
  refine ⟨l,hKeep,hExit,hTop,?_⟩
  let s := nestedCoreSize ρ m
  have hs : Antitone s :=
    antitone_nat_of_succ_le (nestedCoreSize_monotone_down ρ (by linarith only [hρ₁]) m)
  have hlt (i j : ℕ) (hi : i ≤ l) (hij : i < j) : s j < s i := by
    have h4 : 4 ≤ s i := (le_max_left 4 h₀).trans (hKeep i hi)
    have h4R : (4:ℝ) ≤ s i := by exact_mod_cast h4
    have hStep := nestedCoreSize_geometric ρ hρ.le hρ₁ m i h4
    change (s (i+1) : ℝ) ≤ (3/4)*s i at hStep
    have hlt : s (i+1) < s i := by
      exact_mod_cast (show (s (i+1):ℝ) < s i by linarith only [hStep,h4R])
    exact (hs (Nat.succ_le_of_lt hij)).trans_lt hlt
  have hInj : Set.InjOn s (range (l+1) : Set ℕ) := by
    intro i hi j hj he
    rcases lt_trichotomy i j with h|h|h
    · exact False.elim ((ne_of_lt (hlt i j (by have := mem_range.mp hi; omega) h)) he.symm)
    · exact h
    · exact False.elim ((ne_of_lt (hlt j i (by have := mem_range.mp hj; omega) h)) he)
  have hSum := hh₀ ((range (l+1)).image s) (by
    intro n hn
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
    exact (le_max_right 4 h₀).trans (hKeep i (by have := mem_range.mp hi; omega)))
  rw [sum_image hInj] at hSum
  exact hSum

end OverfullWork.ChenShan
