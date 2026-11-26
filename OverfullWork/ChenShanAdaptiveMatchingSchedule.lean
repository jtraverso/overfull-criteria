module

public import OverfullWork.ChenShanAdaptiveMatchingCost
public import Mathlib.Data.Finset.Interval

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real
open scoped Classical

variable {I C S : Type*} [Fintype I] [Fintype C] [Nonempty C]

/-- The number of remaining rounds at which a particular test can be hit. -/
noncomputable def remainingHits (active : ℕ → I → Prop) (k q : ℕ) (i : I) : ℕ :=
  ((Ico k q).filter (fun j => active j i)).card

omit [Fintype I] in
theorem remainingHits_step (active : ℕ → I → Prop) {k q : ℕ} (hk : k < q) (i : I) :
    remainingHits active k q i =
      remainingHits active (k+1) q i + (if active k i then 1 else 0) := by
  have hIco : Ico k q = insert k (Ico (k+1) q) := by
    ext j
    rw [mem_insert,mem_Ico,mem_Ico]
    omega
  have hNot : k ∉ (Ico (k+1) q).filter (fun j => active j i) := by
    intro h
    have := (mem_Ico.mp (mem_filter.mp h).1).1
    omega
  unfold remainingHits
  rw [hIco,filter_insert]
  split_ifs <;> simp [card_insert_of_notMem hNot]

/-- Iterating conditional expectation in a finite schedule. Each stage
may choose its own candidates from the state reached in previous stages. -/
theorem exists_adaptive_matching_schedule
    (q : ℕ) (s₀ : S) (valid : ℕ → S → Prop)
    (active : ℕ → I → Prop) (count : S → I → ℕ) (α p cap : ℝ)
    (hα : 0 < α) (hp : 0 ≤ p) (hValid : valid 0 s₀)
    (hInit : (∑ i, exp (α*count s₀ i + p*(exp α-1)*remainingHits active 0 q i - α*cap)) < 1)
    (hStep : ∀ k < q, ∀ s, valid k s → (∀ i, (count s i : ℝ) < cap) →
      ∃ next : C → S, ∃ hit : I → C → Prop,
        (∀ c, valid (k+1) (next c)) ∧
        (∀ i, active k i → ((univ.filter (hit i)).card : ℝ) ≤ p*Fintype.card C) ∧
        (∀ i c, count (next c) i = count s i + (if active k i ∧ hit i c then 1 else 0))) :
    ∃ s, valid q s ∧ ∀ i, (count s i : ℝ) < cap := by
  let β := p*(exp α-1)
  have hβ : 0 ≤ β := mul_nonneg hp (sub_nonneg.mpr (one_le_exp_iff.mpr hα.le))
  let w (k : ℕ) (s : S) (i : I) :=
    exp (α*count s i + β*remainingHits active k q i - α*cap)
  have hCount (k : ℕ) (s : S) (h : (∑ i, w k s i) < 1) (i : I) :
      (count s i : ℝ) < cap := by
    have hi : w k s i ≤ ∑ j, w k s j :=
      single_le_sum (f := w k s) (fun _ _ => (exp_pos _).le) (mem_univ i)
    have hExp : w k s i < exp 0 := by simpa only [exp_zero] using hi.trans_lt h
    have hI := exp_lt_exp.mp hExp
    have hRem : 0 ≤ β * (remainingHits active k q i : ℝ) :=
      mul_nonneg hβ (Nat.cast_nonneg _)
    by_contra! hc
    have hh := mul_le_mul_of_nonneg_left hc hα.le
    linarith only [hI,hRem,hh]
  have schedule (k : ℕ) (hk : k ≤ q) : ∃ s, valid k s ∧ (∑ i, w k s i) < 1 := by
    induction k with
    | zero => exact ⟨s₀,hValid,hInit⟩
    | succ k ih =>
      have hk' : k < q := by omega
      obtain ⟨s,hs,hCost⟩ := ih hk'.le
      obtain ⟨next,hit,hNext,hHits,hUpdate⟩ := hStep k hk' s hs (hCount k s hCost)
      obtain ⟨c,hc⟩ := exists_matching_choice_nonincreasing_cost
        (w k s) (active k) hit α p hα.le (fun _ => (exp_pos _).le) hHits
      have hW (i : I) : w (k+1) (next c) i = w k s i *
          (if active k i then exp ((if hit i c then α else 0)-β) else 1) := by
        unfold w
        rw [hUpdate,remainingHits_step active hk']
        by_cases ha : active k i
        · simp only [ha,ite_true,true_and]
          rw [← exp_add]
          congr 1
          by_cases hh : hit i c <;> simp [hh,Nat.cast_add] <;> ring
        · simp [ha]
      refine ⟨next c,hNext c,?_⟩
      simp_rw [hW]
      exact hc.trans_lt hCost
  obtain ⟨s,hs,hw⟩ := schedule q le_rfl
  exact ⟨s,hs,hCount q s hw⟩

end OverfullWork.ChenShan
