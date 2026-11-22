module

public import OverfullWork.BernoulliPairBlocks
public import OverfullWork.DoubleDegreeCutBudget

@[expose] public section


/-! One finite exponential budget for linear rows and pair-block rows. -/
namespace OverfullWork.BernoulliPairBlocks

open Finset Real
open scoped Classical
universe u v

theorem exists_sample_of_moment_budget {E : Type u} {R : Type v} [Fintype E] [Fintype R]
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (score : R → (E → Bool) → ℝ)
    (var t b : R → ℝ) (ht : ∀ r, 0 < t r)
    (hMoment : ∀ r z, (∑ s, assignmentMass p s * exp (z * score r s)) ≤ exp (z^2 * var r/2))
    (hBudget : (∑ r, 2*exp ((t r)^2*var r/2-t r*b r)) < 1) :
    ∃ s, ∀ r, |score r s| < b r := by
  let P s := ∑ r, (exp (t r*(score r s-b r))+exp (-t r*(score r s+b r)))
  have hShift (r : R) (z w : ℝ) :
      (∑ s, assignmentMass p s*exp (z*(score r s-w))) ≤ exp (z^2*var r/2-z*w) := by
    have h := mul_le_mul_of_nonneg_right (hMoment r z) (exp_pos (-z*w)).le
    rw [←exp_add,show z^2*var r/2 + -z*w = z^2*var r/2-z*w by ring] at h
    apply le_trans _ h
    rw [sum_mul]
    apply le_of_eq
    apply sum_congr rfl
    intro s _
    rw [mul_assoc,←exp_add]
    congr 2
    ring
  have hSum : (∑ s, assignmentMass p s * P s) ≤ ∑ r, 2*exp ((t r)^2*var r/2-t r*b r) := by
    conv_lhs => simp only [P,mul_sum,mul_add]
    rw [sum_comm]
    apply sum_le_sum
    intro r _
    rw [sum_add_distrib]
    have hp' := hShift r (t r) (b r)
    have hn' := hShift r (-t r) (-b r)
    simp only [sub_neg_eq_add,neg_sq,neg_mul,mul_neg,neg_neg] at hn'
    simp only [mul_add,neg_add] at hn'
    simp only [neg_mul] at hn' ⊢
    linarith only [hp',hn']
  have hExists : ∃ s, P s < 1 := by
    by_contra! h
    have hh := sum_le_sum (s := univ) (fun s _ =>
      mul_le_mul_of_nonneg_left (h s) (assignmentMass_nonneg p hp hp1 s))
    simp only [mul_one,assignmentMass_sum] at hh
    linarith only [hh,hSum,hBudget]
  obtain ⟨s,hs⟩ := hExists
  refine ⟨s,?_⟩
  intro r
  have hTerm := single_le_sum (s := univ)
    (f := fun r => exp (t r*(score r s-b r))+exp (-t r*(score r s+b r)))
    (fun _ _ => by positivity) (mem_univ r)
  change _ ≤ P s at hTerm
  have ha : exp (t r*(score r s-b r)) < 1 := by
    linarith only [hTerm,hs,exp_pos (-t r*(score r s+b r))]
  have hb : exp (-t r*(score r s+b r)) < 1 := by
    linarith only [hTerm,hs,exp_pos (t r*(score r s-b r))]
  rw [abs_lt]
  constructor <;> nlinarith only [exp_lt_one_iff.mp ha,exp_lt_one_iff.mp hb,ht r]

/-- A uniform threshold pays for two degree rows per vertex, two rows
per ordered pair of vertices, and all ordered rectangles. -/
theorem eventual_degree_codegree_cut_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      4*((n:ℝ)+n^2)*exp (-(ε^2*(n:ℝ))/8) +
        2*(4:ℝ)^n*exp (-(ε^2*(n:ℝ)^2)/8) < 1 := by
  obtain ⟨N₀,h₀⟩ := DoubleDegreeCutBudget.eventual_budget (ε/2) (by positivity)
  let c := ε^2/8
  let t := 3*c/4
  have ht : 0 < t := by dsimp [t,c]; positivity
  obtain ⟨N₁,h₁⟩ := exists_nat_gt (max 1 (4/t^2))
  refine ⟨max N₀ N₁,?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := (le_max_right _ _).trans hn
  have hh := h₁.trans_le (show (N₁:ℝ) ≤ n by exact_mod_cast hn1)
  have hn' : (1:ℝ) ≤ n := (le_max_left _ _).trans hh.le
  have ht' : 4 < t^2*n := by
    rw [mul_comm]
    exact (div_lt_iff₀ (sq_pos_of_pos ht)).mp ((le_max_right _ _).trans_lt hh)
  have hx := pow_div_factorial_le_exp (t*n) (by positivity) 2
  norm_num only [Nat.factorial,Nat.cast_ofNat,Nat.cast_one] at hx
  have hy := mul_le_mul_of_nonneg_right ht'.le (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hExp : 1+(n:ℝ) ≤ exp (t*n) := by nlinarith only [hx,hy,hn']
  have hDeg : 4*((n:ℝ)+n^2)*exp (-c*n) ≤ 4*(n:ℝ)*exp (-c*n/4) := by
    have h := mul_le_mul_of_nonneg_right hExp (show 0 ≤ 4*(n:ℝ)*exp (-c*n) by positivity)
    have he : exp (t*n)*exp (-c*n) = exp (-c*n/4) := by
      rw [←exp_add]
      congr 1
      dsimp [t]
      ring
    calc
      _ = (1+(n:ℝ))*(4*(n:ℝ)*exp (-c*n)) := by ring
      _ ≤ exp (t*n)*(4*(n:ℝ)*exp (-c*n)) := h
      _ = _ := by rw [show exp (t*n)*(4*(n:ℝ)*exp (-c*n)) =
          4*(n:ℝ)*(exp (t*n)*exp (-c*n)) by ring,he]
  have hCut : 2*(4:ℝ)^n*exp (-c*n^2) ≤ 2*(4:ℝ)^n*exp (-c*n^2/4) := by
    have hc : 0 ≤ c*(n:ℝ)^2 := by dsimp [c]; positivity
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by positivity)
  have hBase := h₀ n ((le_max_left _ _).trans hn)
  have hLinear : -((ε/2)^2*(n:ℝ))/8 = -c*n/4 := by dsimp [c]; ring
  have hQuadratic : -((ε/2)^2*(n:ℝ)^2)/8 = -c*n^2/4 := by dsimp [c]; ring
  rw [hLinear,hQuadratic] at hBase
  have hd : -(ε^2*(n:ℝ))/8 = -c*n := by dsimp [c]; ring
  have hr : -(ε^2*(n:ℝ)^2)/8 = -c*n^2 := by dsimp [c]; ring
  rw [hd,hr]
  linarith only [hDeg,hCut,hBase]

end OverfullWork.BernoulliPairBlocks
