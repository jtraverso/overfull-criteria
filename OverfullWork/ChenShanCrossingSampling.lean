module

public import OverfullWork.ChenShanCrossingCycle
public import OverfullWork.ChenShanReserveDegreeSampling
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

section Cyclic

variable {J : Type*} {V : J → Type*} [∀ j, Fintype (V j)]
variable (next : J ≃ J)

abbrev CyclicEdgeSlot := Σ j, V j × V (next j)

def cyclicOutSlot (j : J) (a : V j) : V (next j) ↪ CyclicEdgeSlot (V := V) next :=
  ⟨fun b => ⟨j,a,b⟩,by intro b c h; cases h; rfl⟩

def cyclicInSlot (j : J) (b : V (next j)) : V j ↪ CyclicEdgeSlot (V := V) next :=
  ⟨fun a => ⟨j,a,b⟩,by intro a c h; cases h; rfl⟩

noncomputable def cyclicOutNeighbors (E : (j : J) → V j → V (next j) → Prop)
    (j : J) (a : V j) : Finset (CyclicEdgeSlot (V := V) next) :=
  (univ.filter (E j a)).map (cyclicOutSlot next j a)

noncomputable def cyclicInNeighbors (E : (j : J) → V j → V (next j) → Prop)
    (j : J) (b : V (next j)) : Finset (CyclicEdgeSlot (V := V) next) :=
  (univ.filter (fun a => E j a b)).map (cyclicInSlot next j b)

theorem cyclicOutNeighbors_mean
    (E : (j : J) → V j → V (next j) → Prop)
    (p : (j : J) → V j → V (next j) → ℝ)
    (hZero : ∀ j a b, ¬E j a b → p j a b = 0)
    (j : J) (a : V j) :
    mean (fun e : CyclicEdgeSlot (V := V) next => p e.1 e.2.1 e.2.2)
      (cyclicOutNeighbors next E j a) = ∑ b, p j a b := by
  rw [mean,cyclicOutNeighbors,sum_map,sum_filter]
  apply sum_congr rfl
  intro b _
  by_cases hb : E j a b <;> simp [cyclicOutSlot,hb,hZero]

theorem cyclicInNeighbors_mean
    (E : (j : J) → V j → V (next j) → Prop)
    (p : (j : J) → V j → V (next j) → ℝ)
    (hZero : ∀ j a b, ¬E j a b → p j a b = 0)
    (j : J) (b : V (next j)) :
    mean (fun e : CyclicEdgeSlot (V := V) next => p e.1 e.2.1 e.2.2)
      (cyclicInNeighbors next E j b) = ∑ a, p j a b := by
  rw [mean,cyclicInNeighbors,sum_map,sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : E j a b <;> simp [cyclicInSlot,ha,hZero]

variable [Fintype J]

/-- Degree control on one sample of the cyclic pairs. The count of
actual edges ignores absent slots, whose sampling probabilities are zero. -/
theorem exists_cyclic_reserve_degree_control
    (E : (j : J) → V j → V (next j) → Prop)
    (p : (j : J) → V j → V (next j) → ℝ)
    {μ n ξ : ℝ} (hμ : 0 < μ) (hn : 0 < n) (hξ : 0 ≤ ξ)
    (hZero : ∀ j a b, ¬E j a b → p j a b = 0)
    (hp₀ : ∀ j a b, 0 ≤ p j a b) (hp₁ : ∀ j a b, p j a b ≤ 1)
    (hpμ : ∀ j a b, p j a b ≤ 2*μ)
    (hCard : ∀ j, (Fintype.card (V j) : ℝ) ≤ 2*n)
    (hMean : ∀ j (a : V (next j)), (∑ b, p (next j) a b) = ∑ b, p j b a)
    (hUnion : (Fintype.card (Σ j, V (next j)) : ℝ)*4*
      Real.exp (-((min (ξ*n/2) (μ*n))^2/(16*μ*n))) < 1) :
    ∃ sample : CyclicEdgeSlot (V := V) next → Bool, ∀ j (a : V (next j)),
      |count (cyclicOutNeighbors next E (next j) a) sample-
        count (cyclicInNeighbors next E j a) sample| ≤ ξ*n ∧
      count (cyclicOutNeighbors next E (next j) a) sample+
        count (cyclicInNeighbors next E j a) sample ≤ 10*μ*n := by
  let Prob (e : CyclicEdgeSlot (V := V) next) := p e.1 e.2.1 e.2.2
  let In (v : Σ j, V (next j)) := cyclicInNeighbors next E v.1 v.2
  let Out (v : Σ j, V (next j)) := cyclicOutNeighbors next E (next v.1) v.2
  have hBal (v : Σ j, V (next j)) : mean Prob (In v) = mean Prob (Out v) := by
    dsimp only [Prob,In,Out]
    rw [cyclicInNeighbors_mean next E p hZero,cyclicOutNeighbors_mean next E p hZero]
    exact (hMean v.1 v.2).symm
  have hUpper (v : Σ j, V (next j)) : mean Prob (Out v) ≤ 4*μ*n := by
    dsimp only [Prob,Out]
    rw [cyclicOutNeighbors_mean next E p hZero]
    calc
      _ ≤ ∑ _ : V (next (next v.1)), 2*μ := sum_le_sum fun b _ => hpμ _ v.2 b
      _ = (Fintype.card (V (next (next v.1))) : ℝ)*(2*μ) := by simp [nsmul_eq_mul]
      _ ≤ (2*n)*(2*μ) := mul_le_mul_of_nonneg_right (hCard _) (by positivity)
      _ = _ := by ring
  obtain ⟨sample,hsample⟩ := exists_reserve_sample_degree_control
    Prob (fun e => hp₀ e.1 e.2.1 e.2.2) (fun e => hp₁ e.1 e.2.1 e.2.2)
    In Out hμ hn hξ hBal hUpper hUnion
  exact ⟨sample,fun j a => hsample ⟨j,a⟩⟩

end Cyclic


/-- A quadratic number of tests with uniformly exponential failure
probability has a strict union budget above an explicit threshold. -/
theorem quadratic_exponential_union_budget {a c n : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hLarge : 27*a/c^3 < n) :
    a*n^2*Real.exp (-(c*n)) < 1 := by
  have hpos : 0 < c^3 := by positivity
  have hThreshold := (div_lt_iff₀ hpos).mp hLarge
  have hMul := mul_lt_mul_of_pos_right hThreshold (show 0 < n^2 by positivity)
  have hPoly : a*n^2 < (c*n/3)^3 := by nlinarith only [hMul]
  have hcn : 0 ≤ c*n/3 := by positivity
  have hExp : c*n/3 ≤ Real.exp (c*n/3) := by
    linarith only [Real.add_one_le_exp (c*n/3)]
  have hCube : (c*n/3)^3 ≤ Real.exp (c*n) := by
    calc
      _ ≤ Real.exp (c*n/3)^3 := pow_le_pow_left₀ hcn hExp _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num; ring_nf
  rw [Real.exp_neg,← div_eq_mul_inv,div_lt_one (Real.exp_pos _)]
  exact hPoly.trans_le hCube

theorem crossing_reserve_exp_rate {μ ξ n : ℝ} (hμ : 0 < μ) (hn : 0 < n) :
    (min (ξ*n/2) (μ*n))^2/(16*μ*n) = ((min (ξ/2) μ)^2/(16*μ))*n := by
  have hMin : min ((ξ/2)*n) (μ*n) = min (ξ/2) μ*n := by
    rcases le_total (ξ/2) μ with h | h
    · rw [min_eq_left h,min_eq_left (mul_le_mul_of_nonneg_right h hn.le)]
    · rw [min_eq_right h,min_eq_right (mul_le_mul_of_nonneg_right h hn.le)]
  rw [show ξ*n/2 = (ξ/2)*n by ring,hMin]
  field_simp


universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]

theorem crossingPart_card_le {ρ : ℝ} {m k l : ℕ}
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i+1 ≤ l)
    (hρ : ρ ≤ 1) (hn : 2 ≤ (nestedCoreSize ρ m i : ℝ)) (hk : (k:ℝ)/m ≤ 3/2)
    (j : Fin 6) :
    (Fintype.card (CrossingPart S i j) : ℝ) ≤ 2*nestedCoreSize ρ m i := by
  let n : ℝ := nestedCoreSize ρ m i
  let s : ℝ := nestedCoreSize ρ m (i+1)
  let p : ℝ := (k:ℝ)/m
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsn : s ≤ n := by
    dsimp only [s,n]
    exact_mod_cast nestedCoreSize_monotone_down ρ hρ m i
  have hps : p*s ≤ (3/2)*s := mul_le_mul_of_nonneg_right hk hs
  have hpr : p*(n-s) ≤ (3/2)*(n-s) := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hsn)
  have h := (abs_le.mp (crossingSizeErrors S i hi j)).2
  fin_cases j
  · change (Fintype.card (CrossingPart S i 0) : ℝ)-s ≤ 1 at h
    linarith only [h,hsn,hn]
  · change (Fintype.card (CrossingPart S i 1) : ℝ)-(n-s) ≤ 1 at h
    linarith only [h,hs,hn]
  · change (Fintype.card (CrossingPart S i 2) : ℝ)-p*s ≤ 1 at h
    linarith only [h,hps,hsn,hn]
  · change (Fintype.card (CrossingPart S i 3) : ℝ)-(n-s) ≤ 1 at h
    linarith only [h,hs,hn]
  · change (Fintype.card (CrossingPart S i 4) : ℝ)-s ≤ 1 at h
    linarith only [h,hsn,hn]
  · change (Fintype.card (CrossingPart S i 5) : ℝ)-p*(n-s) ≤ 1 at h
    linarith only [h,hpr,hs,hn]

/-- Property (R1) on the six crossing classes. The explicit order
threshold makes the union of the vertex failures have mass below one. -/
theorem exists_crossing_reserve_degree_sample {ρ : ℝ} {m k l : ℕ}
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (p : (j : Fin 6) → CrossingPart S i j → CrossingPart S i (crossingNext j) → ℝ)
    {μ ξ : ℝ} (hμ : 0 < μ) (hξ : 0 < ξ) (hρ : ρ ≤ 1) (hi : i+1 ≤ l)
    (hk : (k:ℝ)/m ≤ 3/2) (hn : 2 ≤ (nestedCoreSize ρ m i : ℝ))
    (hLarge : 1296/(((min (ξ/2) μ)^2/(16*μ))^3) < nestedCoreSize ρ m i)
    (hZero : ∀ j a b, ¬crossingArc S i F P Q j (crossingNext j) a b → p j a b=0)
    (hp : ∀ j a b, crossingArc S i F P Q j (crossingNext j) a b →
      p j a b ∈ Set.Ioo (0:ℝ) 1 ∧ p j a b ≤ 2*μ)
    (hMean : ∀ j (a : CrossingPart S i (crossingNext j)),
      (∑ b, p (crossingNext j) a b) = ∑ b, p j b a) :
    let E := fun j => crossingArc S i F P Q j (crossingNext j)
    let n : ℝ := nestedCoreSize ρ m i
    ∃ sample : CyclicEdgeSlot (V := CrossingPart S i) crossingNext → Bool,
    ∀ j (a : CrossingPart S i (crossingNext j)),
      |count (cyclicOutNeighbors crossingNext E (crossingNext j) a) sample-
        count (cyclicInNeighbors crossingNext E j a) sample| ≤ ξ*n ∧
      count (cyclicOutNeighbors crossingNext E (crossingNext j) a) sample+
        count (cyclicInNeighbors crossingNext E j a) sample ≤ 10*μ*n := by
  dsimp only
  let n : ℝ := nestedCoreSize ρ m i
  let c := (min (ξ/2) μ)^2/(16*μ)
  let E := fun j => crossingArc S i F P Q j (crossingNext j)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hn₀ : 0 < n := by linarith only [hn]
  have hCard := crossingPart_card_le S i hi hρ hn hk
  have hTotal : (Fintype.card (Σ j, CrossingPart S i (crossingNext j)) : ℝ) ≤ 12*n := by
    rw [Fintype.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _ : Fin 6, 2*n := sum_le_sum fun j _ => hCard (crossingNext j)
      _ = _ := by simp [nsmul_eq_mul]; ring
  have hBounds (j : Fin 6) a b : 0 ≤ p j a b ∧ p j a b ≤ 1 ∧ p j a b ≤ 2*μ := by
    by_cases he : E j a b
    · exact ⟨(hp j a b he).1.1.le,(hp j a b he).1.2.le,(hp j a b he).2⟩
    · rw [hZero j a b he]
      exact ⟨le_rfl,by norm_num,by positivity⟩
  apply exists_cyclic_reserve_degree_control crossingNext E p hμ hn₀ hξ.le hZero
    (fun j a b => (hBounds j a b).1) (fun j a b => (hBounds j a b).2.1)
    (fun j a b => (hBounds j a b).2.2) hCard hMean
  rw [crossing_reserve_exp_rate hμ hn₀]
  apply lt_of_le_of_lt _ (quadratic_exponential_union_budget (a := 48) hc hn₀ (by
    dsimp only [c,n]
    norm_num only [show (27:ℝ)*48=1296 by norm_num]
    exact hLarge))
  have hSq : n ≤ n^2 := by have := mul_le_mul_of_nonneg_right (show 1 ≤ n by linarith only [hn]) hn₀.le; nlinarith
  exact mul_le_mul_of_nonneg_right (by linarith only [hSq,hTotal]) (Real.exp_pos _).le

end OverfullWork.ChenShan
