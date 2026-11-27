module

public import OverfullWork.ChenShanBlockCapacitySwap
public import OverfullWork.ChenShanProductVariance
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {I : Type*} [Fintype I] {V : I → Type*} [∀ i, Fintype (V i)]

/-- The subset of the disjoint union picked by the independent samples. -/
noncomputable def blockPartsSelected (s : I → ℕ) (t : BlockParts (V := V) s) :
    Finset (Σ i, V i) :=
  univ.filter (blockPartsContains s t)

theorem sum_blockPartsSelected (s : I → ℕ) (t : BlockParts (V := V) s)
    (w : (Σ i, V i) → ℝ) :
    (∑ v ∈ blockPartsSelected s t, w v) = ∑ i, ∑ v ∈ (t i).val, w ⟨i,v⟩ := by
  classical
  rw [blockPartsSelected, sum_filter, Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter]
  congr 1
  apply Finset.ext
  intro v
  rw [mem_filter]
  exact and_iff_right (mem_univ v)

/-- Uniform probability on the product equals the product of the
uniform subset probabilities. -/
theorem blockPartsMass_eq_uniform (s : I → ℕ) (t : BlockParts (V := V) s) :
    blockPartsMass s t = (Fintype.card (BlockParts (V := V) s) : ℝ)⁻¹ := by
  simp only [blockPartsMass, partProductMass, Fintype.card_pi, Nat.cast_prod, Fintype.card_coe,
    card_powersetCard, card_univ, partSampleMass, one_div, Finset.prod_inv_distrib]

/-- Variance adds across the independently sampled parts, with each
part charged its own sampling fraction. -/
theorem sampled_block_capacity_variance {E Z : Type*} [Fintype E]
    (s : I → ℕ) (hs : ∀ i, s i ≤ Fintype.card (V i))
    (x y : E → Σ i, V i) (S : Finset Z) (w : Z → (Σ i, V i) → ℝ)
    (cap : Z → ℝ) (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw : ∀ z ∈ S, ∀ v, 0 ≤ w z v) :
    blockVariance (blockPartsMass s) (fun t =>
      subsetBlockCapacity x y S w cap w₁ w₂ (blockPartsSelected s t)) ≤
      ∑ i, 4*((s i:ℝ)/Fintype.card (V i)) *
        (∑ v : V i, (blockCapacityInfluence x y S w w₁ w₂ ⟨i,v⟩)^2) := by
  classical
  let _ (i : I) : Nonempty (PartSample (V i) (s i)) := by
    obtain ⟨T,hT⟩ := (powersetCard_nonempty.mpr
      (by simpa only [card_univ] using hs i) : ((univ : Finset (V i)).powersetCard (s i)).Nonempty)
    exact ⟨⟨T,hT⟩⟩
  rw [funext (blockPartsMass_eq_uniform s)]
  change uniformBlockVariance _ ≤ _
  refine uniform_pi_variance_le
    (fun t => subsetBlockCapacity x y S w cap w₁ w₂ (blockPartsSelected s t))
    (fun i => 4*((s i:ℝ)/Fintype.card (V i)) *
      (∑ v : V i, (blockCapacityInfluence x y S w w₁ w₂ ⟨i,v⟩)^2)) ?_
  intro i t
  let embed : V i ↪ (Σ j, V j) := ⟨Sigma.mk i, fun a b h => by cases h; rfl⟩
  let R := (blockPartsSelected s t).filter (fun q => q.1 ≠ i)
  let g (T : Finset (V i)) := R ∪ T.map embed
  have hG (T : PartSample (V i) (s i)) :
      blockPartsSelected s (Function.update t i T) = g T.val := by
    ext ⟨j,v⟩
    by_cases hji : j = i
    · subst j
      simp [g, R, blockPartsSelected, blockPartsContains, mem_map]
      exact ⟨fun hv => ⟨v,hv,rfl⟩, fun ⟨a,ha,h⟩ => (embed.injective h) ▸ ha⟩
    · have hNot : ⟨j,v⟩ ∉ T.val.map embed := by
        intro h
        obtain ⟨a,_,ha⟩ := mem_map.mp h
        exact hji (congrArg Sigma.fst ha).symm
      simp [g, R, blockPartsSelected, blockPartsContains, hji, hNot, Function.update_of_ne]
  simp only [hG]
  let f (T : Finset (V i)) := subsetBlockCapacity x y S w cap w₁ w₂ (g T)
  let influence (v : V i) := blockCapacityInfluence x y S w w₁ w₂ ⟨i,v⟩
  refine fixed_size_swap_variance univ (s i) (by simpa only [card_univ] using hs i)
    f influence ?_
  intro T _ a _ b _ hab _ _
  apply block_capacity_swap_abs_le x y S w cap w₁ w₂ _ _ ⟨i,a⟩ ⟨i,b⟩
    (fun h => hab (embed.injective h)) hw₁ hw₂ hw
  intro q hqa hqb
  simp only [g, map_insert, mem_union, mem_insert, show q ≠ embed a from hqa,
    show q ≠ embed b from hqb, false_or]


/-- The capacity has the same expression in the expectation and
variance calculations. -/
theorem subsetBlockCapacity_eq_blockParts (s : I → ℕ) (t : BlockParts (V := V) s)
    {E Z : Type*} [Fintype E] (x y : E → Σ i, V i)
    (S : Finset Z) (w : Z → (Σ i, V i) → ℝ) (cap : Z → ℝ) (w₁ w₂ : ℝ) :
    subsetBlockCapacity x y S w cap w₁ w₂ (blockPartsSelected s t) =
      w₂ * blockPartsInternalCount s x y t +
      ∑ z ∈ S, min (w₁ * (∑ i, ∑ v ∈ (t i).val, w z ⟨i,v⟩)) (cap z) := by
  unfold subsetBlockCapacity blockPartsInternalCount
  simp only [sum_blockPartsSelected]
  have hMem (v : Σ i, V i) : v ∈ blockPartsSelected s t ↔ blockPartsContains s t v := by
    simp only [blockPartsSelected, mem_filter, mem_univ, true_and]
  simp only [hMem]

/-- The variance bound for the capacity with a common fraction in all parts. -/
theorem sampled_block_capacity_variance_common_fraction {E Z : Type*} [Fintype E]
    (s : I → ℕ) (p a : ℝ) (hs : ∀ i, s i ≤ Fintype.card (V i))
    (hFrac : ∀ i, (s i:ℝ)/Fintype.card (V i) = p) (hp : 0 ≤ p) (ha : 0 ≤ a)
    (x y : E → Σ i, V i) (S : Finset Z) (w : Z → (Σ i, V i) → ℝ)
    (cap : Z → ℝ) (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hScale : w₁ ≤ w₂)
    (hw : ∀ z ∈ S, ∀ v, 0 ≤ w z v)
    (hDegree : ∀ v, internalEdgeIncidences x y v + (∑ z ∈ S, w z v) ≤ a) :
    blockVariance (blockPartsMass s) (fun t =>
      subsetBlockCapacity x y S w cap w₁ w₂ (blockPartsSelected s t)) ≤
      8*p*w₂^2*a*((Fintype.card E:ℝ)+(∑ z ∈ S, ∑ v, w z v)) := by
  apply (sampled_block_capacity_variance s hs x y S w cap w₁ w₂ hw₁ (hw₁.trans hScale) hw).trans
  simp only [hFrac, ← mul_sum]
  have h := mul_le_mul_of_nonneg_left
    (block_capacity_influence_sq_sum x y S w w₁ w₂ a hw₁ hScale ha hw hDegree)
    (show 0 ≤ 4*p by positivity)
  rw [Fintype.sum_sigma] at h
  convert h using 1
  ring


theorem blockPartsMass_nonneg (s : I → ℕ) (t : BlockParts (V := V) s) :
    0 ≤ blockPartsMass s t := by
  rw [blockPartsMass_eq_uniform]
  positivity

theorem blockPartsMass_sum (s : I → ℕ) (hs : ∀ i, s i ≤ Fintype.card (V i)) :
    (∑ t : BlockParts (V := V) s, blockPartsMass s t) = 1 := by
  have h := blockMean_product (fun i => partSampleMass (V := V i) (s i))
    (fun _ _ => (1:ℝ))
  simpa only [blockMean, prod_const_one, mul_one, partSampleMass_sum _ (hs _),
    blockPartsMass] using h

/-- One-sided Chebyshev on the same finite probability space as the
capacity expectation. -/
theorem blockMean_below_threshold_le_variance_div {Ω : Type*} [Fintype Ω]
    (mass : Ω → ℝ) (hMass : ∀ x, 0 ≤ mass x) (hTotal : (∑ x, mass x) = 1)
    (f : Ω → ℝ) (L t : ℝ) (ht : 0 < t) (hMean : L+t ≤ blockMean mass f) :
    blockMean mass (fun x => eventIndicator (f x < L)) ≤ blockVariance mass f / t^2 := by
  let μ := blockMean mass f
  have hMarkov : blockMean mass (fun x => eventIndicator (f x < L)) ≤
      (∑ x, mass x*(f x-μ)^2)/t^2 := by
    apply (le_div_iff₀ (show 0 < t^2 by positivity)).mpr
    rw [blockMean, sum_mul]
    apply sum_le_sum
    intro x _
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hMass x)
    by_cases hx : f x < L
    · simp only [eventIndicator, ite_eq_left hx, one_mul]
      have hGap : t ≤ μ-f x := by linarith only [hx,hMean]
      have hSq : t^2 ≤ (μ-f x)^2 :=
        sq_le_sq' (by linarith only [hGap,ht]) hGap
      nlinarith only [hSq]
    · simp only [eventIndicator, ite_eq_right hx, zero_mul]
      exact sq_nonneg _
  have hExpand (x : Ω) : mass x*(f x-μ)^2 =
      mass x*(f x)^2-(2*μ)*(mass x*f x)+mass x*μ^2 := by ring
  rw [show (∑ x, mass x*(f x-μ)^2) = blockVariance mass f by
    simp only [hExpand, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hTotal,
      one_mul, blockVariance]
    change _ - (2*μ)*μ + μ^2 = _ - μ^2
    simp only [blockMean]
    ring] at hMarkov
  exact hMarkov

private theorem capacity_tail_arithmetic (p fraction a m : ℝ)
    (hp : 0 < p) (hf : 0 < fraction) (hm : 0 < m) :
    (8*p*(64*fraction/p^2)^2*a*m)/(fraction*m/8)^2 =
      (2:ℝ)^21*a/(p^3*m) := by
  field_simp [hp.ne',hf.ne',hm.ne']
  ring

set_option maxHeartbeats 900000 in
/-- The paper's lower tail for the capacity, combining (5.5), the
independent-part form of (5.6), and Chebyshev. -/
theorem sampled_block_capacity_lower_tail {E Z : Type*} [Fintype E]
    (s : I → ℕ) (p fraction a : ℝ)
    (hs : ∀ i, s i ≤ Fintype.card (V i)) (hTwo : ∀ i, 2 ≤ s i)
    (hFrac : ∀ i, (s i:ℝ)/Fintype.card (V i) = p)
    (hp : 0 < p) (hp₁ : p ≤ 1) (hf : 0 < fraction) (ha : 0 ≤ a)
    (x y : E → Σ i, V i) (hxy : ∀ e, x e ≠ y e)
    (S : Finset Z) (w : Z → (Σ i, V i) → ℝ) (c : Z → ℝ)
    (hWeight : ∀ z ∈ S, ∀ v, 0 ≤ w z v ∧ w z v ≤ a)
    (hDegree : ∀ v, internalEdgeIncidences x y v + (∑ z ∈ S, w z v) ≤ a)
    (hHalf : ∀ z ∈ S, (∑ v, w z v) ≤ c z/2)
    (hRound : ∀ z ∈ S, 64 ≤ fraction*c z)
    (hSmall : ∀ z ∈ S, a ≤ p*c z/4096)
    (hSize : 0 < (Fintype.card E:ℝ)+(∑ z ∈ S, ∑ v, w z v)) :
    let m := (Fintype.card E:ℝ)+(∑ z ∈ S, ∑ v, w z v)
    let cap (z : Z) := (⌊(15/16:ℝ)*fraction*c z⌋₊ : ℝ)
    let stat (t : BlockParts (V := V) s) :=
      subsetBlockCapacity x y S w cap (64*fraction/p) (64*fraction/p^2) (blockPartsSelected s t)
    blockMean (blockPartsMass s) (fun t => eventIndicator (stat t < (13/8:ℝ)*fraction*m)) ≤
      (2:ℝ)^21*a/(p^3*m) := by
  intro m cap stat
  have hm : 0 < m := hSize
  have hMean := expected_sampled_block_capacity s p fraction a hs hTwo hFrac
    hp hf ha x y hxy S (fun z i v => w z ⟨i,v⟩) c
    (fun z hz i v => hWeight z hz ⟨i,v⟩)
    (fun z hz => by simpa only [← Fintype.sum_sigma] using hHalf z hz)
    hRound hSmall
  have hh (z : Z) : (∑ i, ∑ v : V i, w z ⟨i,v⟩) = ∑ v, w z v :=
    (Fintype.sum_sigma (fun v => w z v)).symm
  dsimp only at hMean
  simp only [hh] at hMean
  have hMean' : (7/4:ℝ)*fraction*m ≤ blockMean (blockPartsMass s) stat := by
    simpa only [stat, cap, m, subsetBlockCapacity_eq_blockParts] using hMean
  have hGap : (13/8:ℝ)*fraction*m+fraction*m/8 ≤ blockMean (blockPartsMass s) stat := by
    linarith only [hMean']
  have hScale : 64*fraction/p ≤ 64*fraction/p^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr hp₁)]
  have hVar := sampled_block_capacity_variance_common_fraction s p a hs hFrac hp.le ha
    x y S w cap (64*fraction/p) (64*fraction/p^2) (by positivity) hScale
    (fun z hz v => (hWeight z hz v).1) hDegree
  have hTail := blockMean_below_threshold_le_variance_div (blockPartsMass s)
    (blockPartsMass_nonneg s) (blockPartsMass_sum s hs) stat
    ((13/8:ℝ)*fraction*m) (fraction*m/8) (by positivity) hGap
  refine hTail.trans ((div_le_div_of_nonneg_right hVar (sq_nonneg _)).trans_eq ?_)
  exact capacity_tail_arithmetic p fraction a m hp hf hm



/-- A finite law has an outcome avoiding a family of tests whenever
the sum of their failure bounds is strictly below one. -/
theorem exists_finite_outcome_avoiding {Ω J : Type*} [Fintype Ω] [Fintype J]
    (mass : Ω → ℝ) (hNonneg : ∀ t, 0 ≤ mass t) (hTotal : (∑ t, mass t) = 1)
    (bad : J → Ω → Prop) (risk : J → ℝ)
    (hRisk : ∀ j, blockMean mass (fun t => eventIndicator (bad j t)) ≤ risk j)
    (hSum : (∑ j, risk j) < 1) :
    ∃ t, ∀ j, ¬ bad j t := by
  classical
  by_contra! hBad
  have hPoint (t : Ω) : 1 ≤ ∑ j, eventIndicator (bad j t) := by
    obtain ⟨j,hj⟩ := hBad t
    have h := single_le_sum (s := (univ : Finset J))
      (f := fun k => eventIndicator (bad k t)) (by
        intro k _
        unfold eventIndicator
        positivity) (mem_univ j)
    simpa only [eventIndicator, ite_eq_left hj] using h
  have hMass : 1 ≤ ∑ j, blockMean mass (fun t => eventIndicator (bad j t)) := by
    simp only [blockMean]
    rw [sum_comm (s := (univ : Finset J)), ← hTotal]
    apply sum_le_sum
    intro t _
    simpa only [mul_one, Finset.mul_sum] using mul_le_mul_of_nonneg_left (hPoint t) (hNonneg t)
  exact (not_lt_of_ge (hMass.trans (sum_le_sum fun j _ => hRisk j))) hSum

/-- A single choice of all parts can avoid a finite family of tests. -/
theorem exists_block_sample_avoiding {J : Type*} [Fintype J]
    (s : I → ℕ) (hs : ∀ i, s i ≤ Fintype.card (V i))
    (bad : J → BlockParts (V := V) s → Prop) (risk : J → ℝ)
    (hRisk : ∀ j, blockMean (blockPartsMass s) (fun t => eventIndicator (bad j t)) ≤ risk j)
    (hSum : (∑ j, risk j) < 1) :
    ∃ t, ∀ j, ¬ bad j t :=
  exists_finite_outcome_avoiding (blockPartsMass s) (blockPartsMass_nonneg s)
    (blockPartsMass_sum s hs) bad risk hRisk hSum


/-- Preferred-edge test for an active special vertex, where each
weight counts parallel edges to a core vertex on its preferred side. -/
theorem sampled_special_preferred_degree_lower_tail
    (s : I → ℕ) (p a c : ℝ)
    (hs : ∀ i, s i ≤ Fintype.card (V i))
    (hFrac : ∀ i, (s i:ℝ)/Fintype.card (V i) = p)
    (hp : 0 < p) (ha : 0 ≤ a) (hc : 0 < c)
    (w : ∀ i, V i → ℝ) (hw : ∀ i v, 0 ≤ w i v ∧ w i v ≤ a)
    (hPreferred : c/2 ≤ ∑ i, ∑ v, w i v) :
    let X (t : BlockParts (V := V) s) := ∑ i, ∑ v ∈ (t i).val, w i v
    blockMean (blockPartsMass s) (fun t => eventIndicator (X t < p*c/3)) ≤
      18*a/(p*c) := by
  intro X
  let d := ∑ i, ∑ v, w i v
  let μ := p*d
  have hd : 0 < d := by linarith only [hc,hPreferred]
  have hμ : 0 < μ := mul_pos hp hd
  have hPref := mul_le_mul_of_nonneg_left hPreferred hp.le
  obtain ⟨hMean,hSecond⟩ := block_parts_degree_moments s p a hs hFrac hp.le w hw
  change blockMean (blockPartsMass s) X = μ at hMean
  change blockMean (blockPartsMass s) (fun t => (X t)^2) ≤ μ*(μ+a) at hSecond
  have hGap : p*c/3+μ/3 ≤ blockMean (blockPartsMass s) X := by
    rw [hMean]
    dsimp only [μ]
    nlinarith only [hPref]
  have hVar : blockVariance (blockPartsMass s) X ≤ μ*a := by
    unfold blockVariance
    rw [hMean]
    nlinarith only [hSecond]
  have hTail := blockMean_below_threshold_le_variance_div (blockPartsMass s)
    (blockPartsMass_nonneg s) (blockPartsMass_sum s hs) X (p*c/3) (μ/3)
    (by positivity) hGap
  refine hTail.trans ((div_le_div_of_nonneg_right hVar (sq_nonneg _)).trans ?_)
  have hExact : μ*a/(μ/3)^2 = 9*a/μ := by
    field_simp [hμ.ne']
    ring
  rw [hExact]
  have hDenom : p*c/2 ≤ μ := by
    dsimp only [μ]
    nlinarith only [hPref]
  calc
    _ ≤ 9*a/(p*c/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hDenom
    _ = _ := by ring

end OverfullWork.ChenShan
