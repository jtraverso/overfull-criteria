module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import OverfullWork.ChenShanUniformInclusion
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

/-- A finite weighted expectation. The capacity estimates apply to any
nonnegative mass, in particular the joint distribution of the blocks. -/
noncomputable def blockMean (mass : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ t, mass t * f t

private theorem blockMean_mono (mass f g : Ω → ℝ)
    (hm : ∀ t, 0 ≤ mass t) (h : ∀ t, f t ≤ g t) :
    blockMean mass f ≤ blockMean mass g :=
  sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h t) (hm t)

/-- The capped term in (5.5), using the harmonic lower bound and
Cauchy–Schwarz on the finite space. The second moment bound is what
the variance estimate for a weighted degree supplies. -/
theorem expected_capped_degree_lower
    (mass X : Ω → ℝ) (hm : ∀ t, 0 ≤ mass t) (hX : ∀ t, 0 ≤ X t)
    (L w m a : ℝ) (hL : 0 < L) (hw : 0 < w) (hm₀ : 0 ≤ m) (ha : 0 ≤ a)
    (hMean : blockMean mass X = m)
    (hSecond : blockMean mass (fun t => (X t)^2) ≤ m*(m+a)) :
    L*m/(L/w+m+a) ≤ blockMean mass (fun t => min (w*X t) L) := by
  by_cases hZero : m = 0
  · rw [hZero,mul_zero,zero_div]
    exact sum_nonneg (fun t _ => mul_nonneg (hm t) (le_min (mul_nonneg hw.le (hX t)) hL.le))
  have hmPos : 0 < m := lt_of_le_of_ne hm₀ (Ne.symm hZero)
  let r (t : Ω) := L + w*X t
  have hr (t : Ω) : 0 < r t := add_pos_of_pos_of_nonneg hL (mul_nonneg hw.le (hX t))
  let f (t : Ω) := mass t*X t
  let g (t : Ω) := mass t*(X t/r t)
  let h (t : Ω) := mass t*(X t*r t)
  have hg (t : Ω) : 0 ≤ g t := mul_nonneg (hm t) (div_nonneg (hX t) (hr t).le)
  have hh (t : Ω) : 0 ≤ h t := mul_nonneg (hm t) (mul_nonneg (hX t) (hr t).le)
  have hsq (t : Ω) : (f t)^2 = g t*h t := by
    dsimp only [f,g,h]
    field_simp [(hr t).ne']
  have hCS := sum_sq_le_sum_mul_sum_of_sq_le_mul (s := (univ : Finset Ω))
    (r := f) (f := g) (g := h) (fun t _ => hg t) (fun t _ => hh t) (fun t _ => (hsq t).le)
  change (blockMean mass X)^2 ≤ (∑ t, g t)*(∑ t, h t) at hCS
  rw [hMean] at hCS
  have hAux : (∑ t, h t) = L*m+w*blockMean mass (fun t => (X t)^2) := by
    rw [← hMean]
    unfold blockMean
    rw [mul_sum,mul_sum,← sum_add_distrib]
    exact sum_congr rfl (fun t _ => by dsimp [h,r]; ring)
  have hAux' : (∑ t, h t) ≤ m*(L+w*(m+a)) := by
    rw [hAux]
    have h := mul_le_mul_of_nonneg_left hSecond hw.le
    nlinarith only [h]
  have hBound : m ≤ (∑ t, g t)*(L+w*(m+a)) := by
    have h := hCS.trans (mul_le_mul_of_nonneg_left hAux' (sum_nonneg fun t _ => hg t))
    apply (mul_le_mul_iff_of_pos_left hmPos).mp
    nlinarith only [h]
  have hDen : 0 < L/w+m+a := by positivity
  have hScaled : L*m ≤ (L*w*(∑ t, g t))*(L/w+m+a) := by
    have hIdent : w*(L/w+m+a) = L+w*(m+a) := by
      field_simp [hw.ne']
      ring
    rw [show (L*w*(∑ t, g t))*(L/w+m+a) =
      L*(∑ t, g t)*(w*(L/w+m+a)) by ring,hIdent]
    nlinarith only [mul_le_mul_of_nonneg_left hBound hL.le]
  have hPoint (t : Ω) : L*w*(X t/r t) ≤ min (w*X t) L := by
    have h1 : L ≤ r t := by dsimp [r]; linarith only [mul_nonneg hw.le (hX t)]
    have h2 : w*X t ≤ r t := by dsimp [r]; linarith only [hL]
    have hwp : 0 ≤ w*X t := mul_nonneg hw.le (hX t)
    rw [← mul_div_assoc]
    apply le_min
    · apply (div_le_iff₀ (hr t)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right h1 hwp]
    · apply (div_le_iff₀ (hr t)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left h2 hL.le]
  apply ((div_le_iff₀ hDen).mpr hScaled).trans
  have h := blockMean_mono mass (fun t => L*w*(X t/r t)) (fun t => min (w*X t) L) hm hPoint
  apply le_trans (le_of_eq ?_) h
  rw [blockMean,mul_sum]
  exact sum_congr rfl (fun t _ => by dsimp [g]; ring)

/-- The numerical comparison for one exceptional vertex in (5.5). -/
theorem block_capped_degree_expected_seven_quarters
    (mass X : Ω → ℝ) (hm : ∀ t, 0 ≤ mass t) (hX : ∀ t, 0 ≤ X t)
    (p fraction c d L a : ℝ)
    (hp : 0 < p) (hf : 0 < fraction) (hc : 0 < c) (hd : 0 ≤ d) (ha : 0 ≤ a)
    (hHalf : d ≤ c/2) (hCapLo : (59/64:ℝ)*fraction*c ≤ L)
    (hCapHi : L ≤ (15/16:ℝ)*fraction*c) (hSmall : a ≤ p*c/4096)
    (hMean : blockMean mass X = p*d)
    (hSecond : blockMean mass (fun t => (X t)^2) ≤ (p*d)*(p*d+a)) :
    (7/4:ℝ)*fraction*d ≤ blockMean mass (fun t => min ((64*fraction/p)*X t) L) := by
  let w := 64*fraction/p
  have hw : 0 < w := by dsimp [w]; positivity
  have hL : 0 < L := (show 0 < (59/64:ℝ)*fraction*c by positivity).trans_le hCapLo
  have hRatio : L/w ≤ 15*p*c/1024 := by
    apply (div_le_iff₀ hw).mpr
    have hEq : (15*p*c/1024)*w = (15/16:ℝ)*fraction*c := by
      dsimp [w]
      field_simp
      ring
    exact hCapHi.trans_eq hEq.symm
  have hDen : 0 < L/w+p*d+a := by positivity
  have hδ : 0 ≤ fraction*d := mul_nonneg hf.le hd
  have hComparison : (7/4:ℝ)*(L/w+p*d+a) ≤ (59/64:ℝ)*p*c := by
    nlinarith only [hRatio,mul_le_mul_of_nonneg_left hHalf hp.le,hSmall,mul_pos hp hc]
  have hNum : (7/4:ℝ)*fraction*d*(L/w+p*d+a) ≤ L*(p*d) := by
    have h1 := mul_le_mul_of_nonneg_right hComparison hδ
    have h2 := mul_le_mul_of_nonneg_right hCapLo (show 0 ≤ p*d by positivity)
    nlinarith only [h1,h2]
  exact ((le_div_iff₀ hDen).mpr hNum).trans
    (expected_capped_degree_lower mass X hm hX L w (p*d) a hL hw (by positivity) ha hMean hSecond)

/-- The rounded cap in the paper satisfies the bounds used in the
capped expectation estimate once the active palette degree is at least 64. -/
theorem palette_floor_cap_bounds (t : ℝ) (ht : 64 ≤ t) :
    (59/64:ℝ)*t ≤ ((⌊(15/16:ℝ)*t⌋₊ : ℕ):ℝ) ∧
    ((⌊(15/16:ℝ)*t⌋₊ : ℕ):ℝ) ≤ (15/16:ℝ)*t := by
  have ht₀ : 0 ≤ (15/16:ℝ)*t := by linarith only [ht]
  have h₁ := Nat.lt_floor_add_one ((15/16:ℝ)*t)
  have h₂ := Nat.floor_le ht₀
  exact ⟨by linarith only [ht,h₁],h₂⟩


/-- Two distinct vertices in the same uniformly sampled part have
joint inclusion at least half the square of the sampled fraction
as soon as the part contributes at least two vertices. -/
theorem block_pair_inclusion_arithmetic (s n : ℝ) (hs : 2 ≤ s) (hn : s ≤ n) :
    (s/n)^2/2 ≤ (s*(s-1))/(n*(n-1)) := by
  have hs₀ : 0 < s := by linarith only [hs]
  have hn₀ : 0 < n := hs₀.trans_le hn
  have hn₁ : 0 < n-1 := by linarith only [hs,hn]
  have hA : (s-1)/s ≥ 1/2 := by
    apply (le_div_iff₀ hs₀).mpr
    linarith only [hs]
  have hB : (n-1)/n ≤ 1 := by
    apply (div_le_iff₀ hn₀).mpr
    linarith
  have hC : (1/2:ℝ)*((n-1)/n) ≤ (s-1)/s := by linarith only [hA,hB]
  have hC' := (le_div_iff₀ hs₀).mp hC
  apply (le_div_iff₀ (mul_pos hn₀ hn₁)).mpr
  have hEq : ((s/n)^2/2)*(n*(n-1)) = s*((1/2:ℝ)*((n-1)/n)*s) := by
    field_simp [hn₀.ne']
  rw [hEq]
  exact mul_le_mul_of_nonneg_left hC' hs₀.le

private theorem blockMean_sum {Z : Type*} (S : Finset Z) (mass : Ω → ℝ) (f : Z → Ω → ℝ) :
    blockMean mass (fun t => ∑ x ∈ S, f x t) = ∑ x ∈ S, blockMean mass (f x) := by
  simp only [blockMean,mul_sum]
  exact sum_comm

/-- The lower bound on the full capacity in (5.5). The internal-edge
term uses its pair inclusion lower bound, and the exceptional terms use
the first and second moments of their degrees into the block. -/
theorem expected_block_capacity_lower {Z : Type*} (S : Finset Z)
    (mass b : Ω → ℝ) (X : Z → Ω → ℝ) (c d L : Z → ℝ)
    (p fraction a totalInternal : ℝ)
    (hm : ∀ t, 0 ≤ mass t) (hp : 0 < p) (hf : 0 < fraction) (ha : 0 ≤ a)
    (hb : 0 ≤ totalInternal)
    (hInternal : p^2/2*totalInternal ≤ blockMean mass b)
    (hX : ∀ x ∈ S, ∀ t, 0 ≤ X x t)
    (hC : ∀ x ∈ S, 0 < c x) (hD : ∀ x ∈ S, 0 ≤ d x)
    (hHalf : ∀ x ∈ S, d x ≤ c x/2)
    (hCapLo : ∀ x ∈ S, (59/64:ℝ)*fraction*c x ≤ L x)
    (hCapHi : ∀ x ∈ S, L x ≤ (15/16:ℝ)*fraction*c x)
    (hSmall : ∀ x ∈ S, a ≤ p*c x/4096)
    (hMean : ∀ x ∈ S, blockMean mass (X x) = p*d x)
    (hSecond : ∀ x ∈ S, blockMean mass (fun t => (X x t)^2) ≤ (p*d x)*(p*d x+a)) :
    (7/4:ℝ)*fraction*(totalInternal+(∑ x ∈ S, d x)) ≤
      blockMean mass (fun t => (64*fraction/p^2)*b t +
        ∑ x ∈ S, min ((64*fraction/p)*X x t) (L x)) := by
  let w := 64*fraction/p^2
  let F (x : Z) (t : Ω) := min ((64*fraction/p)*X x t) (L x)
  have hRewrite : blockMean mass (fun t => w*b t + ∑ x ∈ S, F x t) =
      w*blockMean mass b + ∑ x ∈ S, blockMean mass (F x) := by
    have hAdd : ∀ (f g : Ω → ℝ), blockMean mass (fun t => f t+g t) =
        blockMean mass f+blockMean mass g := by
      intro f g
      simp only [blockMean,mul_add,sum_add_distrib]
    have hMul : blockMean mass (fun t => w*b t) = w*blockMean mass b := by
      simp only [blockMean,mul_sum]
      exact sum_congr rfl (fun t _ => by ring)
    rw [hAdd,hMul,blockMean_sum]
  have hInside : (7/4:ℝ)*fraction*totalInternal ≤ w*blockMean mass b := by
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have h := mul_le_mul_of_nonneg_left hInternal hw
    have hEq : w*(p^2/2*totalInternal) = 32*fraction*totalInternal := by
      dsimp [w]
      field_simp [hp.ne']
      ring
    rw [hEq] at h
    nlinarith only [h,mul_nonneg hf.le hb]
  have hOutside : (∑ x ∈ S, (7/4:ℝ)*fraction*d x) ≤ ∑ x ∈ S, blockMean mass (F x) := by
    apply sum_le_sum
    intro x hx
    exact block_capped_degree_expected_seven_quarters mass (X x) hm (hX x hx) p fraction
      (c x) (d x) (L x) a hp hf (hC x hx) (hD x hx) ha (hHalf x hx) (hCapLo x hx)
      (hCapHi x hx) (hSmall x hx) (hMean x hx) (hSecond x hx)
  change _ ≤ blockMean mass (fun t => w*b t + ∑ x ∈ S, F x t)
  rw [hRewrite,mul_add,mul_sum]
  exact add_le_add hInside hOutside


private theorem choose_two_ratio (n s : ℕ) (hs : 2 ≤ s) (hn : s ≤ n) :
    ((n-2).choose (s-2):ℝ)/n.choose s =
      ((s:ℝ)*((s:ℝ)-1))/((n:ℝ)*((n:ℝ)-1)) := by
  obtain ⟨k,rfl⟩ : ∃ k, s = k+2 := ⟨s-2,by omega⟩
  obtain ⟨l,rfl⟩ : ∃ l, n = l+2 := ⟨n-2,by omega⟩
  have hStep (n k : ℕ) :
      ((n+1).choose (k+1):ℝ)*((k:ℝ)+1) = ((n:ℝ)+1)*(n.choose k:ℝ) := by
    have h := Nat.choose_mul (n := n+1) (k := k+1) (s := 1) (by omega)
    have h' : (n+1).choose (k+1)*(k+1) = (n+1)*n.choose k := by
      simpa only [Nat.choose_one_right,Nat.add_sub_cancel] using h
    exact_mod_cast h'
  have hb : (0:ℝ) < (l+2).choose (k+2) := by exact_mod_cast Nat.choose_pos hn
  have hnR : 0 < (l:ℝ)+2 := by positivity
  have hnR' : 0 < (l:ℝ)+1 := by positivity
  have h₁ := hStep l k
  have h₂ := hStep (l+1) (k+1)
  push_cast at h₂
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_ofNat]
  rw [show (k:ℝ)+2-1 = (k:ℝ)+1 by ring,show (l:ℝ)+2-1 = (l:ℝ)+1 by ring]
  apply (div_eq_div_iff hb.ne' (mul_pos hnR hnR').ne').mpr
  calc
    (l.choose k:ℝ)*(((l:ℝ)+2)*((l:ℝ)+1)) =
        ((l:ℝ)+2)*(((l:ℝ)+1)*(l.choose k:ℝ)) := by ring
    _ = ((l:ℝ)+2)*(((l+1).choose (k+1):ℝ)*((k:ℝ)+1)) := by rw [h₁]
    _ = (((l:ℝ)+1+1)*((l+1).choose (k+1):ℝ))*((k:ℝ)+1) := by ring
    _ = _ := by rw [← h₂]; ring

open UniformSubsetSampling in
/-- The actual inclusion bound for an internal edge in one sampled part. -/
theorem same_part_edge_inclusion_lower {V : Type*} [Fintype V]
    (x y : V) (hxy : x ≠ y) (s : ℕ) (hs : 2 ≤ s) (hn : s ≤ Fintype.card V) :
    ((s:ℝ)/Fintype.card V)^2/2 ≤ probability s (fun T => ({x,y} : Finset V) ⊆ T) := by
  have hCard : ({x,y} : Finset V).card = 2 := by simp [card_insert_of_notMem,hxy]
  have hs' : ({x,y} : Finset V).card ≤ s := by rwa [hCard]
  rw [probability_contains_eq _ hs',hCard,choose_two_ratio _ _ hs hn]
  exact block_pair_inclusion_arithmetic _ _ (by exact_mod_cast hs) (by exact_mod_cast hn)

end OverfullWork.ChenShan
