module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

/-- The gap used in §5.1.2. The z+1 half-open intervals are disjoint,
so at most z special vertices cannot hit all of them. -/
theorem exists_empty_special_degree_interval {V : Type*} (Z₀ : Finset V)
    (c : V → ℝ) (z : ℕ) (k θ₀ : ℝ)
    (hZ : Z₀.card ≤ z) (hk : 0 < k) (hθ₀ : 0 < θ₀) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ θ₀ ∧ θ₀/(2^16*((z:ℝ)+1))^z ≤ θ ∧
      ∀ x ∈ Z₀, c x < θ*k/(2^16*((z:ℝ)+1)) ∨ θ*k ≤ c x := by
  let L : ℝ := 2^16*((z:ℝ)+1)
  have hL : 1 < L := by dsimp [L]; nlinarith only [Nat.cast_nonneg (α := ℝ) z]
  let t (i : ℕ) : ℝ := θ₀ / L^i
  have hPos (i : ℕ) : 0 < t i := div_pos hθ₀ (pow_pos (by linarith only [hL]) _)
  have hNext (i : ℕ) : t (i+1)*k = t i*k/L := by
    dsimp [t]
    rw [pow_succ]
    ring
  have hMono : Antitone t := by
    apply antitone_nat_of_succ_le
    intro i
    dsimp [t]
    rw [pow_succ,← div_div]
    apply div_le_self (div_nonneg hθ₀.le (pow_nonneg (by linarith only [hL]) _)) hL.le
  suffices h : ∃ i : Fin (z+1), ∀ x ∈ Z₀, c x < t (i.val+1)*k ∨ t i.val*k ≤ c x by
    obtain ⟨i,hi⟩ := h
    refine ⟨t i.val,hPos _,?_,?_,?_⟩
    · simpa [t] using hMono (Nat.zero_le i.val)
    · exact hMono (Nat.le_of_lt_succ i.isLt)
    · intro x hx
      have hh := hi x hx
      rwa [hNext] at hh
  by_contra! h
  choose f hmem hLo hHi using h
  let g (i : Fin (z+1)) : ↥Z₀ := ⟨f i,hmem i⟩
  have hg : Function.Injective g := by
    have hLess (i j : Fin (z+1)) (hij : i < j) : g i ≠ g j := by
      intro he
      have hf : f i = f j := congrArg Subtype.val he
      have ht : t j.val*k ≤ t (i.val+1)*k :=
        mul_le_mul_of_nonneg_right (hMono (Nat.succ_le_of_lt hij)) hk.le
      have hi := hLo i
      have hj := hHi j
      rw [hf] at hi
      exact (not_lt_of_ge (ht.trans hi)) hj
    intro i j he
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (hLess i j hlt he).elim
    · exact heq
    · exact (hLess j i hgt he.symm).elim
  have hh := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin,Fintype.card_coe] at hh
  omega

/-- Excluding the colors of low vertices and of the two small edge
classes leaves at least 511/512 of the colors at every active vertex. -/
theorem palette_exclusion_budget {V W : Type*} [DecidableEq W]
    (low : Finset V) (C : V → Finset W) (E₁ E₂ : Finset W)
    (z : ℕ) (T : ℝ) (hT : 0 < T)
    (hLow : low.card ≤ z)
    (hWeight : ∀ x ∈ low, ((C x).card : ℝ) ≤ T/(2^16*((z:ℝ)+1)))
    (h₁ : (E₁.card:ℝ) ≤ T/2^16) (h₂ : (E₂.card:ℝ) ≤ T/2^16) :
    let forbidden := (low.biUnion C) ∪ E₁ ∪ E₂
    (forbidden.card : ℝ) < T/512 ∧
      ∀ x, T ≤ (C x).card → (511/512 : ℝ)*(C x).card ≤ ((C x \ forbidden).card:ℝ) := by
  intro F
  let a := T/(2^16*((z:ℝ)+1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hsum : (((low.biUnion C).card : ℕ) : ℝ) ≤ (z:ℝ)*a := by
    have hs : ((low.biUnion C).card : ℝ) ≤ ∑ x ∈ low, ((C x).card : ℝ) := by
      exact_mod_cast (card_biUnion_le : (low.biUnion C).card ≤ ∑ x ∈ low, (C x).card)
    calc
      _ ≤ ∑ x ∈ low, ((C x).card : ℝ) := hs
      _ ≤ ∑ _x ∈ low, a := sum_le_sum hWeight
      _ = (low.card : ℝ)*a := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hLow) ha.le
  have hza : (z:ℝ)*a ≤ T/2^16 := by
    have hz : (0:ℝ) ≤ z := Nat.cast_nonneg _
    have hden : 0 < (z:ℝ)+1 := by positivity
    have hEq : a * ((z:ℝ)+1) = T/2^16 := by
      dsimp [a]
      rw [← div_div]
      exact div_mul_cancel₀ _ hden.ne'
    linarith only [hEq,ha]
  have hc : (F.card : ℝ) ≤ ((low.biUnion C).card:ℝ)+E₁.card+E₂.card := by
    exact_mod_cast ((card_union_le ((low.biUnion C) ∪ E₁) E₂).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have hlt : (F.card:ℝ) < T/512 := by
    norm_num at hza h₁ h₂
    linarith only [hc,hsum,hza,h₁,h₂,hT]
  refine ⟨hlt,?_⟩
  intro x hx
  have hcount : ((C x).card : ℝ) ≤ ((C x \ F).card:ℝ)+F.card := by
    have hh := card_sdiff_add_card_inter (C x) F
    have hi : (C x ∩ F).card ≤ F.card := card_le_card inter_subset_right
    exact_mod_cast (show (C x).card ≤ (C x \ F).card+F.card by omega)
  linarith only [hcount,hlt,hx]

/-- Deterministic stability of the capped capacity (5.5). The retained
edge counts are allowed to drop at arbitrary vertices of the block. -/
theorem palette_capacity_after_edge_deletions {V : Type*} (Z : Finset V)
    (b b' w₁ w₂ budget : ℝ) (d d' cap : V → ℝ)
    (hw₁ : 0 ≤ w₁) (hw : w₁ ≤ w₂)
    (hd : ∀ x ∈ Z, d' x ≤ d x)
    (hBudget : b-b'+(∑ x ∈ Z, (d x-d' x)) ≤ budget) :
    w₂*b + (∑ x ∈ Z, min (w₁*d x) (cap x)) ≤
      w₂*b' + (∑ x ∈ Z, min (w₁*d' x) (cap x)) + w₂*budget := by
  have hMin (x : V) (hx : x ∈ Z) :
      min (w₁*d x) (cap x) ≤ min (w₁*d' x) (cap x) + w₂*(d x-d' x) := by
    have he : 0 ≤ d x-d' x := sub_nonneg.mpr (hd x hx)
    have hw₂ : 0 ≤ w₂ := hw₁.trans hw
    by_cases h : w₁*d' x ≤ cap x
    · rw [min_eq_left h]
      have h' := mul_le_mul_of_nonneg_right hw he
      nlinarith only [h',min_le_left (w₁*d x) (cap x)]
    · rw [min_eq_right (le_of_not_ge h)]
      have h' := mul_nonneg hw₂ he
      linarith only [h',min_le_right (w₁*d x) (cap x)]
  have hs := sum_le_sum hMin
  rw [sum_add_distrib,← mul_sum] at hs
  have hb' := mul_le_mul_of_nonneg_left hBudget (hw₁.trans hw)
  nlinarith only [hs,hb']


/-- The last capacity estimate of §5.1.2 with its numerical constants.
A deletion budget of p²E/512 costs at most fractionE/8. -/
theorem palette_capacity_retains_three_halves {V : Type*} (Z : Finset V)
    (b b' p fraction E : ℝ) (d d' cap : V → ℝ)
    (hp : 0 < p) (hp₁ : p ≤ 1) (hfraction : 0 ≤ fraction)
    (hd : ∀ x ∈ Z, d' x ≤ d x)
    (hBudget : b-b'+(∑ x ∈ Z, (d x-d' x)) ≤ p^2*E/512)
    (hBefore : (13/8)*fraction*E ≤ (64*fraction/p^2)*b +
      ∑ x ∈ Z, min ((64*fraction/p)*d x) (cap x)) :
    (3/2)*fraction*E ≤ (64*fraction/p^2)*b' + ∑ x ∈ Z, min ((64*fraction/p)*d' x) (cap x) := by
  have hScale : 64*fraction/p ≤ 64*fraction/p^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have h := mul_le_mul_of_nonneg_left hp₁ hp.le
    nlinarith only [h]
  have h := palette_capacity_after_edge_deletions Z b b' (64*fraction/p) (64*fraction/p^2)
    (p^2*E/512) d d' cap (by positivity) hScale hd hBudget
  have hCost : (64*fraction/p^2)*(p^2*E/512) = fraction*E/8 := by
    field_simp
    ring
  rw [hCost] at h
  linarith only [h,hBefore]

private theorem scaled_even_palette (δ : ℝ) (k : ℕ) (hδ : 0 < δ)
    (hSize : 2 ≤ δ*k) :
    ∃ s : ℕ, 0 < s ∧ Even s ∧ δ ≤ (s:ℝ)/k ∧ (s:ℝ)/k ≤ 2*δ := by
  have hk : 0 < (k:ℝ) := by
    by_contra! h
    have h' := mul_nonpos_of_nonneg_of_nonpos hδ.le h
    linarith only [h',hSize]
  let r : ℕ := ⌈δ*k/2⌉₊
  have hLo : δ*k/2 ≤ (r:ℝ) := Nat.le_ceil _
  have hHi : (r:ℝ) < δ*k/2+1 := Nat.ceil_lt_add_one (by positivity)
  have hr : 0 < r := by exact_mod_cast (show 0 < (r:ℝ) by linarith only [hSize,hLo])
  refine ⟨2*r,by omega,⟨r,by omega⟩,?_,?_⟩
  · apply (le_div_iff₀ hk).mpr
    norm_num
    linarith only [hLo]
  · apply (div_le_iff₀ hk).mpr
    norm_num
    linarith only [hSize,hHi]

/-- Positive even sizes meeting all four inequalities in (5.2).
The palette fractions have a positive lower bound independent of k. -/
theorem exists_even_palette_sizes (q : ℕ) (hq : 0 < q) (β θ : ℝ)
    (hβ : 0 < β) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∃ k₁ k₂ : ℕ, 0 < k₁ ∧ 0 < k₂ ∧ Even k₁ ∧ Even k₂ ∧
        let p₁ : ℝ := 1/q
        let p₂ : ℝ := 1/7
        let fraction₁ := (k₁:ℝ)/k
        let fraction₂ := (k₂:ℝ)/k
        δ ≤ fraction₁ ∧ δ ≤ fraction₂ ∧
        fraction₁ ≤ β*p₁^2*θ/2^18 ∧ fraction₂ ≤ β*p₂^2*θ/2^18 ∧
        (q:ℝ)*k₁+7*k₂ ≤ β*θ*k/400 ∧
        (q:ℝ)*k₁ ≤ β*p₂*θ*k/400 ∧
        (5/4)*(q:ℝ)*fraction₁ ≤ p₂^2/1024 := by
  let p₁ : ℝ := 1/q
  let p₂ : ℝ := 1/7
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  let c₁ := β*p₁^2*θ/2^18
  let c₂ := β*p₂^2*θ/2^18
  let c₃ := β*θ/(400*((q:ℝ)+7))
  let c₄ := β*p₂*θ/(400*(q:ℝ))
  let c₅ := p₂^2/(1280*(q:ℝ))
  let t := min c₁ (min c₂ (min c₃ (min c₄ c₅)))
  let δ := t/2
  have ht : 0 < t := by
    dsimp [t,c₁,c₂,c₃,c₄,c₅,p₁,p₂]
    exact lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let N := ⌈2/δ⌉₊
  refine ⟨δ,hδ,N,?_⟩
  intro k hk
  have hN : (2:ℝ)/δ ≤ (k:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hSize : 2 ≤ δ*k := by
    have h := (div_le_iff₀ hδ).mp hN
    linarith only [h]
  obtain ⟨s,hs,hEven,hLower,hUpper⟩ := scaled_even_palette δ k hδ hSize
  have hUpper' : (s:ℝ)/k ≤ t := by dsimp [δ] at hUpper; linarith only [hUpper]
  have hkR : 0 < (k:ℝ) := by
    by_contra! h
    have hh := mul_nonpos_of_nonneg_of_nonpos hδ.le h
    linarith only [hSize,hh]
  have ht₁ : t ≤ c₁ := min_le_left _ _
  have ht₂ : t ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have ht₃ : t ≤ c₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht₄ : t ≤ c₄ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have ht₅ : t ≤ c₅ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨s,s,hs,hs,hEven,hEven,hLower,hLower,hUpper'.trans ht₁,hUpper'.trans ht₂,?_,?_,?_⟩
  · have h := (div_le_iff₀ hkR).mp (hUpper'.trans ht₃)
    have h₃ : c₃*((q:ℝ)+7) = β*θ/400 := by
      dsimp [c₃]
      field_simp
    have h' := mul_le_mul_of_nonneg_right h (show 0 ≤ (q:ℝ)+7 by positivity)
    nlinarith only [h',h₃,congrArg (fun x : ℝ => x*k) h₃]
  · have h := (div_le_iff₀ hkR).mp (hUpper'.trans ht₄)
    have h₄ : c₄*(q:ℝ) = β*p₂*θ/400 := by
      dsimp [c₄]
      field_simp
    have h' := mul_le_mul_of_nonneg_right h hqR.le
    nlinarith only [h',congrArg (fun x : ℝ => x*k) h₄]
  · have h' := mul_le_mul_of_nonneg_left (hUpper'.trans ht₅)
      (show 0 ≤ (5/4)*(q:ℝ) by positivity)
    have h₅ : (5/4)*(q:ℝ)*c₅ = p₂^2/1024 := by
      dsimp [c₅]
      field_simp; ring
    exact h'.trans_eq h₅

end OverfullWork.ChenShan
