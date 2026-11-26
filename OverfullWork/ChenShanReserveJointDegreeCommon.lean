module

public import OverfullWork.ChenShanCommonNeighborCandidates
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

/-- One reserve sample controls the degree tests, common-neighbor tests,
and additional neighborhood counts.
The embeddings for the latter can have different domains. The cutoff
uses a bound on the total number of tests, including two per vertex. -/
theorem exists_reserve_with_additional_counts
    {I V J H : Type*} [Fintype I] [Fintype V] [Fintype J] [Fintype H]
    {K : J → Type*} [∀ j, Fintype (K j)]
    (p : I → ℝ) (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (In Out : V → Finset I) (T : (j : J) → Finset (K j)) (f : (j : J) → K j × Bool ↪ I)
    (Extra : H → Finset I)
    {μ ρ ξ n C : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) (hξ : 0 < ξ) (hn : 0 < n)
    (hBal : ∀ v, mean p (In v) = mean p (Out v))
    (hUpper : ∀ v, mean p (Out v) ≤ 4*μ*n)
    (hExtra : ∀ j, mean p (Extra j) ≤ 4*μ*n)
    (hLocal : ∀ j x, x ∈ T j → ∀ b, μ/2 ≤ p (f j (x,b)) ∧ p (f j (x,b)) ≤ 2*μ)
    (hCard : ∀ j, ((T j).card : ℝ) ≤ 8*ρ*n)
    (hTests : (2*(Fintype.card V : ℝ)+Fintype.card H)+Fintype.card J ≤ C*n^2)
    (hLarge : 54*C/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 < n) :
    let hits (j : J) (s : I → Bool) :=
      count (T j) (fun x => s (f j (x,false)) && s (f j (x,true)))
    ∃ s : I → Bool,
      (∀ v, |count (Out v) s-count (In v) s| ≤ ξ*n ∧
        count (Out v) s+count (In v) s ≤ 10*μ*n) ∧
      (∀ j, hits j s ≤ 50*μ^2*ρ*n ∧
        (ρ*n/3 ≤ ((T j).card : ℝ) → μ^2*ρ*n/20 ≤ hits j s)) ∧
      ∀ j, |count (Extra j) s-mean p (Extra j)| ≤ min (ξ*n/2) (μ*n) := by
  dsimp only
  let D := min (ξ*n/2) (μ*n)
  let rate₁ := (min (ξ/2) μ)^2/(16*μ)
  let rate₃ := μ^2*ρ/204800
  let rate := min rate₁ rate₃
  let S : (Bool × V) ⊕ H → Finset I
    | .inl b => if b.1 then Out b.2 else In b.2
    | .inr j => Extra j
  let hits (j : J) (s : I → Bool) := count (T j) (fun x => s (f j (x,false)) && s (f j (x,true)))
  let bad : ((Bool × V) ⊕ H) ⊕ J → (I → Bool) → Prop
    | .inl b, s => D ≤ |count (S b) s-mean p (S b)|
    | .inr j, s => 50*μ^2*ρ*n < hits j s ∨
        (ρ*n/3 ≤ ((T j).card : ℝ) ∧ hits j s < μ^2*ρ*n/20)
  have hD : 0 ≤ D := le_min (by positivity) (by positivity)
  have hM : 0 < 4*μ*n := by positivity
  have hD' : D ≤ 2*(4*μ*n) := by
    have hmin := min_le_right (ξ*n/2) (μ*n)
    linarith only [hmin,hM]
  have hRate : 0 < rate := lt_min (by dsimp only [rate₁]; positivity)
    (by dsimp only [rate₃]; positivity)
  have hRate₁ : rate ≤ rate₁ := min_le_left _ _
  have hRate₃ : rate ≤ rate₃ := min_le_right _ _
  have hExp (r : ℝ) (hr : rate ≤ r) :
      2*Real.exp (-(r*n)) ≤ 2*Real.exp (-(rate*n)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hr hn.le)
  have hS (j : (Bool × V) ⊕ H) : mean p (S j) ≤ 4*μ*n := by
    rcases j with ⟨t,v⟩ | j
    · cases t
      · change mean p (In v) ≤ _
        rw [hBal]
        exact hUpper v
      · exact hUpper v
    · exact hExtra j
  have hTail (j : ((Bool × V) ⊕ H) ⊕ J) :
      (∑ s ∈ univ.filter (bad j), mass p s) ≤ 2*Real.exp (-(rate*n)) := by
    rcases j with b | j
    · have ht := abs_tail_bound_of_mean_le p hp₀ hp₁ (S b) hM (hS b) hD hD'
      rw [show 4*(4*μ*n) = 16*μ*n by ring] at ht
      have hId : D^2/(16*μ*n) = rate₁*n := crossing_reserve_exp_rate hμ hn
      rw [hId] at ht
      exact ht.trans (hExp rate₁ hRate₁)
    · have ht := common_neighbor_test_failure p hp₀ hp₁ (f j) (T j) hμ hρ hn (hLocal j) (hCard j)
      have hId : μ^2*ρ*n/204800 = rate₃*n := by dsimp only [rate₃]; ring
      rw [hId] at ht
      calc
        _ = ∑ s ∈ univ.filter (fun s : I → Bool => 50*μ^2*ρ*n < hits j s ∨
            (ρ*n/3 ≤ ((T j).card : ℝ) ∧ hits j s < μ^2*ρ*n/20)), mass p s := by
          apply sum_congr
          · ext s
            simp only [mem_filter,bad]
          · intro s _
            rfl
        _ ≤ _ := ht.trans (hExp rate₃ hRate₃)
  have hUnion : (Fintype.card (((Bool × V) ⊕ H) ⊕ J) : ℝ)*(2*Real.exp (-(rate*n))) < 1 := by
    rw [Fintype.card_sum,Fintype.card_sum,Nat.cast_add,Nat.cast_add,Fintype.card_prod,Nat.cast_mul,Fintype.card_bool,Nat.cast_ofNat]
    have hN : 27*(2*C)/rate^3 < n := by
      have he : 27*(2*C) = 54*C := by ring
      rwa [he]
    calc
      _ ≤ (C*n^2)*(2*Real.exp (-(rate*n))) :=
        mul_le_mul_of_nonneg_right hTests (by positivity)
      _ = (2*C)*n^2*Real.exp (-(rate*n)) := by ring
      _ < _ := quadratic_exponential_union_budget hRate hn hN
  obtain ⟨s,hs⟩ := exists_avoiding_bad_events p hp₀ hp₁ bad _ hTail hUnion
  refine ⟨s,?_,?_,?_⟩
  · intro v
    have hO := (lt_of_not_ge (hs (.inl (.inl (true,v))))).le
    have hI := (lt_of_not_ge (hs (.inl (.inl (false,v))))).le
    change |count (Out v) s-mean p (Out v)| ≤ D at hO
    change |count (In v) s-mean p (In v)| ≤ D at hI
    rw [hBal v] at hI
    have ho := abs_le.mp hO
    have hi := abs_le.mp hI
    have hSmall : D ≤ ξ*n/2 := min_le_left _ _
    have hSmall' : D ≤ μ*n := min_le_right _ _
    exact ⟨abs_le.mpr ⟨by linarith only [hSmall,ho.1,hi.2],
      by linarith only [hSmall,ho.2,hi.1]⟩, by linarith only [hSmall',ho.2,hi.2,hUpper v]⟩
  · intro j
    have hj := hs (.inr j)
    change ¬(50*μ^2*ρ*n < hits j s ∨ (ρ*n/3 ≤ ((T j).card : ℝ) ∧ hits j s < μ^2*ρ*n/20)) at hj
    exact ⟨le_of_not_gt (fun hh => hj (.inl hh)),
      fun hc => le_of_not_gt (fun hh => hj (.inr ⟨hc,hh⟩))⟩
  · intro j
    exact (lt_of_not_ge (hs (.inl (.inr j)))).le

/-- One reserve sample satisfies the degree and common-neighbor tests.
The embeddings for the latter can have different domains. The cutoff
uses a bound on the total number of tests, including two per vertex. -/
theorem exists_reserve_with_degree_and_common_neighbor_tests
    {I V J : Type*} [Fintype I] [Fintype V] [Fintype J]
    {K : J → Type*} [∀ j, Fintype (K j)]
    (p : I → ℝ) (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (In Out : V → Finset I) (T : (j : J) → Finset (K j)) (f : (j : J) → K j × Bool ↪ I)
    {μ ρ ξ n C : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) (hξ : 0 < ξ) (hn : 0 < n)
    (hBal : ∀ v, mean p (In v) = mean p (Out v))
    (hUpper : ∀ v, mean p (Out v) ≤ 4*μ*n)
    (hLocal : ∀ j x, x ∈ T j → ∀ b, μ/2 ≤ p (f j (x,b)) ∧ p (f j (x,b)) ≤ 2*μ)
    (hCard : ∀ j, ((T j).card : ℝ) ≤ 8*ρ*n)
    (hTests : 2*(Fintype.card V : ℝ)+Fintype.card J ≤ C*n^2)
    (hLarge : 54*C/(min ((min (ξ/2) μ)^2/(16*μ)) (μ^2*ρ/204800))^3 < n) :
    let hits (j : J) (s : I → Bool) :=
      count (T j) (fun x => s (f j (x,false)) && s (f j (x,true)))
    ∃ s : I → Bool,
      (∀ v, |count (Out v) s-count (In v) s| ≤ ξ*n ∧
        count (Out v) s+count (In v) s ≤ 10*μ*n) ∧
      ∀ j, hits j s ≤ 50*μ^2*ρ*n ∧
        (ρ*n/3 ≤ ((T j).card : ℝ) → μ^2*ρ*n/20 ≤ hits j s) := by
  dsimp only
  let noExtra : Empty → Finset I := fun j => j.elim
  obtain ⟨s,hDeg,hPairs,_⟩ := exists_reserve_with_additional_counts p hp₀ hp₁ In Out T f
    noExtra hμ hρ hξ hn hBal hUpper (fun j => j.elim) hLocal hCard
    (by simpa using hTests) hLarge
  exact ⟨s,hDeg,hPairs⟩

end OverfullWork.ChenShan
