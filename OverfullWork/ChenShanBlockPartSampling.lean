module

public import OverfullWork.ChenShanBlockCapacityMean
public import OverfullWork.ChenShanWeightedPaletteMoments
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset UniformSubsetSampling
open scoped Classical

section Product

variable {I : Type*} [Fintype I] {T : I → Type*} [∀ i, Fintype (T i)]

/-- The independent product of the finite distributions of the parts. -/
noncomputable def partProductMass (mass : ∀ i, T i → ℝ) (t : ∀ i, T i) : ℝ :=
  ∏ i, mass i (t i)

theorem blockMean_product (mass f : ∀ i, T i → ℝ) :
    blockMean (partProductMass mass) (fun t => ∏ i, f i (t i)) =
      ∏ i, blockMean (mass i) (f i) := by
  simp only [blockMean,partProductMass,← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i t => mass i t*f i t)).symm

theorem blockMean_one_part (mass : ∀ i, T i → ℝ)
    (hMass : ∀ i, (∑ t, mass i t) = 1) (i : I) (f : T i → ℝ) :
    blockMean (partProductMass mass) (fun t => f (t i)) = blockMean (mass i) f := by
  let g := Function.update (fun j (_ : T j) => (1:ℝ)) i f
  have hg (t : ∀ j, T j) : (∏ j, g j (t j)) = f (t i) := by
    rw [prod_eq_single i]
    · simp [g]
    · intro j _ hne
      simp [g,Function.update_of_ne hne]
    · simp
  have hMean := blockMean_product mass g
  simp_rw [hg] at hMean
  rw [hMean,prod_eq_single i]
  · simp [g]
  · intro j _ hne
    simp [g,Function.update_of_ne hne,blockMean,hMass]
  · simp

theorem blockMean_two_parts (mass : ∀ i, T i → ℝ)
    (hMass : ∀ i, (∑ t, mass i t) = 1) (i j : I) (hij : i ≠ j)
    (f : T i → ℝ) (g : T j → ℝ) :
    blockMean (partProductMass mass) (fun t => f (t i)*g (t j)) =
      blockMean (mass i) f * blockMean (mass j) g := by
  let a := Function.update (fun l (_ : T l) => (1:ℝ)) i f
  let b := Function.update (fun l (_ : T l) => (1:ℝ)) j g
  let c (l : I) (x : T l) := a l x*b l x
  have prodOne (t : ∀ l, T l) (q : I) (h : T q → ℝ) :
      (∏ l, Function.update (fun l (_ : T l) => (1:ℝ)) q h l (t l)) = h (t q) := by
    rw [prod_eq_single q]
    · simp
    · intro l _ hne
      simp [Function.update_of_ne hne]
    · simp
  have hProd (t : ∀ l, T l) : (∏ l, c l (t l)) = f (t i)*g (t j) := by
    rw [show (∏ l, c l (t l)) = (∏ l, a l (t l))*(∏ l, b l (t l)) from prod_mul_distrib]
    rw [show (∏ l, a l (t l)) = f (t i) from prodOne t i f,
      show (∏ l, b l (t l)) = g (t j) from prodOne t j g]
  have hMean := blockMean_product mass c
  simp_rw [hProd] at hMean
  rw [hMean,← prod_erase_mul _ _ (mem_univ i)]
  have hj : j ∈ (univ : Finset I).erase i := mem_erase.mpr ⟨hij.symm,mem_univ _⟩
  rw [prod_eq_single j]
  · simp [c,a,b,Function.update_of_ne hij,Function.update_of_ne hij.symm,mul_comm]
  · intro l hl hlj
    have hli := (mem_erase.mp hl).1
    simp [c,a,b,Function.update_of_ne hli,Function.update_of_ne hlj,blockMean,hMass]
  · exact fun h => (h hj).elim

private theorem blockMean_univ_sum {Z Ω : Type*} [Fintype Z] [Fintype Ω]
    (mass : Ω → ℝ) (f : Z → Ω → ℝ) :
    blockMean mass (fun t => ∑ i, f i t) = ∑ i, blockMean mass (f i) := by
  simp only [blockMean,mul_sum]
  exact sum_comm

/-- Independent parts add their variances. The form below records the
result as a bound on the second moment of the total degree. -/
theorem blockMean_product_sum_moments (mass : ∀ i, T i → ℝ) (f : ∀ i, T i → ℝ)
    (hMass : ∀ i, (∑ t, mass i t) = 1) (μ : I → ℝ) (a : ℝ)
    (hMean : ∀ i, blockMean (mass i) (f i) = μ i)
    (hSecond : ∀ i, blockMean (mass i) (fun t => (f i t)^2) ≤ (μ i)^2+a*μ i) :
    blockMean (partProductMass mass) (fun t => ∑ i, f i (t i)) = ∑ i, μ i ∧
      blockMean (partProductMass mass) (fun t => (∑ i, f i (t i))^2) ≤
        (∑ i, μ i)*((∑ i, μ i)+a) := by
  constructor
  · rw [blockMean_univ_sum]
    exact sum_congr rfl (fun i _ => (blockMean_one_part mass hMass i (f i)).trans (hMean i))
  have hExpand (t : ∀ i, T i) : (∑ i, f i (t i))^2 =
      ∑ i, ∑ j, f i (t i)*f j (t j) := by simp_rw [pow_two,sum_mul,mul_sum]
  simp_rw [hExpand]
  simp_rw [blockMean_univ_sum]
  have hPair (i j : I) : blockMean (partProductMass mass) (fun t => f i (t i)*f j (t j)) ≤
      μ i*μ j + if i = j then a*μ i else 0 := by
    by_cases h : i = j
    · subst j
      rw [ite_eq_left rfl]
      simpa only [pow_two] using
        (blockMean_one_part mass hMass i (fun t => (f i t)^2)).le.trans (hSecond i)
    · rw [ite_eq_right h,add_zero,blockMean_two_parts mass hMass i j h,hMean,hMean]
  have hBound := sum_le_sum (s := (univ : Finset I)) (fun i _ =>
    sum_le_sum (s := (univ : Finset I)) (fun j _ => hPair i j))
  simp only [sum_add_distrib,sum_ite_eq,mem_univ,ite_true] at hBound
  have hμEq : (∑ i, ∑ j, μ i*μ j) = (∑ i, μ i)^2 := by
    rw [pow_two,sum_mul]
    exact sum_congr rfl (fun i _ => (mul_sum univ μ (μ i)).symm)
  rw [hμEq,← mul_sum] at hBound
  nlinarith only [hBound]

end Product

section Subsets

variable {V : Type*} [Fintype V]

abbrev PartSample (V : Type*) [Fintype V] (s : ℕ) :=
  ↥((univ : Finset V).powersetCard s)

noncomputable def partSampleMass (s : ℕ) (_ : PartSample V s) : ℝ :=
  1 / ((Fintype.card V).choose s : ℝ)

theorem partSampleMass_sum (s : ℕ) (hs : s ≤ Fintype.card V) :
    (∑ t : PartSample V s, partSampleMass s t) = 1 := by
  have hn : (0:ℝ) < (Fintype.card V).choose s := by exact_mod_cast Nat.choose_pos hs
  simp only [partSampleMass,sum_const,card_univ,nsmul_eq_mul,Fintype.card_coe,card_powersetCard]
  field_simp

theorem blockMean_partSample (s : ℕ) (f : Finset V → ℝ) :
    blockMean (partSampleMass s) (fun t : PartSample V s => f t.val) =
      sampleExpectation s f := by
  unfold blockMean partSampleMass sampleExpectation
  rw [← mul_sum,Finset.sum_coe_sort]
  ring

end Subsets


section BlockMoments

variable {I : Type*} [Fintype I] {V : I → Type*} [∀ i, Fintype (V i)]

/-- The block chooses the prescribed number of vertices independently
in each part. -/
abbrev BlockParts (s : I → ℕ) := ∀ i, PartSample (V i) (s i)

noncomputable def blockPartsMass (s : I → ℕ) (t : BlockParts (V := V) s) : ℝ :=
  partProductMass (fun i => partSampleMass (s i)) t

/-- These are the degree moments entering (5.5). The weights can count
parallel copies, and each vertex has weight at most a. -/
theorem block_parts_degree_moments (s : I → ℕ) (p a : ℝ)
    (hs : ∀ i, s i ≤ Fintype.card (V i))
    (hFrac : ∀ i, (s i:ℝ)/Fintype.card (V i) = p) (hp : 0 ≤ p)
    (w : ∀ i, V i → ℝ) (hw : ∀ i x, 0 ≤ w i x ∧ w i x ≤ a) :
    let d := ∑ i, ∑ x, w i x
    let X (t : BlockParts (V := V) s) := ∑ i, ∑ x ∈ (t i).val, w i x
    blockMean (blockPartsMass s) X = p*d ∧
      blockMean (blockPartsMass s) (fun t => (X t)^2) ≤ (p*d)*(p*d+a) := by
  intro d X
  let m (i : I) := p*(∑ x, w i x)
  let f (i : I) (t : PartSample (V i) (s i)) := ∑ x ∈ t.val, w i x
  have hMass (i : I) := partSampleMass_sum (V := V i) (s i) (hs i)
  have hMean (i : I) : blockMean (partSampleMass (s i)) (f i) = m i := by
    have h := blockMean_partSample (s i) (fun X : Finset (V i) => ∑ x ∈ X, w i x)
    rw [expected_fixed_size_weight _ (hs i),hFrac] at h
    exact h
  have hSecond (i : I) : blockMean (partSampleMass (s i)) (fun t => (f i t)^2) ≤
      (m i)^2+a*m i := by
    have h := fixed_size_weight_variance_le (s i) (hs i) (w i) (fun x => (hw i x).1)
    change sampleExpectation (s i) (fun T => (∑ x ∈ T, w i x)^2) -
      (sampleExpectation (s i) (fun T => ∑ x ∈ T, w i x))^2 ≤
      ((s i:ℝ)/Fintype.card (V i))*(∑ x, (w i x)^2) at h
    rw [hFrac,← blockMean_partSample,← blockMean_partSample,hMean] at h
    have hSq : (∑ x, (w i x)^2) ≤ a*(∑ x, w i x) := by
      rw [mul_sum]
      apply sum_le_sum
      intro x _
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hw i x).2 (hw i x).1
    have hBound := mul_le_mul_of_nonneg_left hSq hp
    dsimp [m,f] at *
    nlinarith only [h,hBound]
  have hSum : (∑ i, m i) = p*d := by simp only [d,m,mul_sum]
  have h := blockMean_product_sum_moments (fun i => partSampleMass (s i)) f hMass m a hMean hSecond
  rw [hSum] at h
  exact h


noncomputable def eventIndicator (P : Prop) : ℝ := if P then 1 else 0

private theorem expected_indication {W : Type*} [Fintype W] (s : ℕ) (P : Finset W → Prop) :
    sampleExpectation s (fun X => eventIndicator (P X)) = probability s P := by
  unfold sampleExpectation eventIndicator probability
  rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one]

/-- Membership of a vertex in a block formed by the independent part
samples. The sigma index specifies its original part. -/
def blockPartsContains (s : I → ℕ) (t : BlockParts (V := V) s) (x : Σ i, V i) : Prop :=
  x.2 ∈ (t x.1).val

set_option maxHeartbeats 1200000 in
/-- The internal edge contribution to (5.5). Vertices in different
parts have independent indicators. Vertices in the same part use
the finite inclusion law for a two-element set. -/
theorem block_parts_edge_inclusion_lower (s : I → ℕ) (p : ℝ)
    (hs : ∀ i, s i ≤ Fintype.card (V i)) (hTwo : ∀ i, 2 ≤ s i)
    (hFrac : ∀ i, (s i:ℝ)/Fintype.card (V i) = p)
    (x y : Σ i, V i) (hxy : x ≠ y) :
    p^2/2 ≤ blockMean (blockPartsMass s)
      (fun t => eventIndicator (blockPartsContains s t x ∧ blockPartsContains s t y)) := by
  have hMass (i : I) := partSampleMass_sum (V := V i) (s i) (hs i)
  obtain ⟨i,x⟩ := x
  obtain ⟨j,y⟩ := y
  by_cases hij : i = j
  · subst j
    have hne : x ≠ y := fun h => hxy (congrArg (Sigma.mk i) h)
    have hFunc (T : Finset (V i)) : eventIndicator (x ∈ T ∧ y ∈ T) =
        eventIndicator (({x,y} : Finset (V i)) ⊆ T) := by
      congr 1
      exact propext (by simp [insert_subset_iff])
    change p^2/2 ≤ blockMean (partProductMass (fun i => partSampleMass (s i)))
      (fun t => eventIndicator (x ∈ (t i).val ∧ y ∈ (t i).val))
    simp_rw [hFunc]
    rw [blockMean_one_part _ hMass i (fun T : PartSample (V i) (s i) =>
      eventIndicator (({x,y} : Finset (V i)) ⊆ T.val))]
    rw [blockMean_partSample (s i) (fun T : Finset (V i) =>
      eventIndicator (({x,y} : Finset (V i)) ⊆ T)),expected_indication]
    have h := same_part_edge_inclusion_lower x y hne (s i) (hTwo i) (hs i)
    rwa [hFrac i] at h
  · have hFunc (t : BlockParts (V := V) s) :
        eventIndicator (x ∈ (t i).val ∧ y ∈ (t j).val) =
          eventIndicator (x ∈ (t i).val)*eventIndicator (y ∈ (t j).val) := by
      by_cases hx : x ∈ (t i).val <;> by_cases hy : y ∈ (t j).val <;>
        simp [eventIndicator,hx,hy]
    change p^2/2 ≤ blockMean (partProductMass (fun i => partSampleMass (s i)))
      (fun t => eventIndicator (x ∈ (t i).val ∧ y ∈ (t j).val))
    simp_rw [hFunc]
    rw [blockMean_two_parts _ hMass i j hij
      (fun T : PartSample (V i) (s i) => eventIndicator (x ∈ T.val))
      (fun T : PartSample (V j) (s j) => eventIndicator (y ∈ T.val))]
    rw [blockMean_partSample (s i) (fun T : Finset (V i) => eventIndicator (x ∈ T)),
      blockMean_partSample (s j) (fun T : Finset (V j) => eventIndicator (y ∈ T))]
    rw [expected_indication,expected_indication,probability_contains_vertex x (hs i),
      probability_contains_vertex y (hs j),hFrac i,hFrac j,← pow_two]
    linarith only [sq_nonneg p]

/-- The number of included copies, counting each indexed edge once. -/
noncomputable def blockPartsInternalCount {E : Type*} [Fintype E] (s : I → ℕ)
    (x y : E → Σ i, V i) (t : BlockParts (V := V) s) : ℝ :=
  ∑ e, eventIndicator (blockPartsContains s t (x e) ∧ blockPartsContains s t (y e))

theorem block_parts_internal_count_mean_lower {E : Type*} [Fintype E]
    (s : I → ℕ) (p : ℝ)
    (hs : ∀ i, s i ≤ Fintype.card (V i)) (hTwo : ∀ i, 2 ≤ s i)
    (hFrac : ∀ i, (s i:ℝ)/Fintype.card (V i) = p)
    (x y : E → Σ i, V i) (hxy : ∀ e, x e ≠ y e) :
    p^2/2*(Fintype.card E:ℝ) ≤ blockMean (blockPartsMass s) (blockPartsInternalCount s x y) := by
  unfold blockPartsInternalCount
  rw [blockMean_univ_sum]
  have h := sum_le_sum (s := (univ : Finset E)) (fun e _ =>
    block_parts_edge_inclusion_lower s p hs hTwo hFrac (x e) (y e) (hxy e))
  simpa only [sum_const,card_univ,nsmul_eq_mul,mul_comm] using h


set_option maxHeartbeats 1200000 in
/-- The expectation bound of (5.5) for the actual independent block
samples. Internal edges and exceptional incidences may have parallel
copies. The two kinds of edges are counted by separate terms. -/
theorem expected_sampled_block_capacity {E Z : Type*} [Fintype E]
    (s : I → ℕ) (p fraction a : ℝ)
    (hs : ∀ i, s i ≤ Fintype.card (V i)) (hTwo : ∀ i, 2 ≤ s i)
    (hFrac : ∀ i, (s i:ℝ)/Fintype.card (V i) = p)
    (hp : 0 < p) (hf : 0 < fraction) (ha : 0 ≤ a)
    (x y : E → Σ i, V i) (hxy : ∀ e, x e ≠ y e)
    (S : Finset Z) (w : Z → ∀ i, V i → ℝ) (c : Z → ℝ)
    (hWeight : ∀ z ∈ S, ∀ i v, 0 ≤ w z i v ∧ w z i v ≤ a)
    (hHalf : ∀ z ∈ S, (∑ i, ∑ v, w z i v) ≤ c z/2)
    (hRound : ∀ z ∈ S, 64 ≤ fraction*c z)
    (hSmall : ∀ z ∈ S, a ≤ p*c z/4096) :
    let d (z : Z) := ∑ i, ∑ v, w z i v
    let cap (z : Z) := (⌊(15/16:ℝ)*fraction*c z⌋₊ : ℝ)
    let stat (t : BlockParts (V := V) s) :=
      (64*fraction/p^2)*blockPartsInternalCount s x y t +
      ∑ z ∈ S, min ((64*fraction/p)*(∑ i, ∑ v ∈ (t i).val, w z i v)) (cap z)
    (7/4:ℝ)*fraction*((Fintype.card E:ℝ)+(∑ z ∈ S, d z)) ≤
      blockMean (blockPartsMass s) stat := by
  intro d cap stat
  let X (z : Z) (t : BlockParts (V := V) s) := ∑ i, ∑ v ∈ (t i).val, w z i v
  have hBounds (z : Z) (hz : z ∈ S) :
      (59/64:ℝ)*fraction*c z ≤ cap z ∧ cap z ≤ (15/16:ℝ)*fraction*c z := by
    have h := palette_floor_cap_bounds (fraction*c z) (hRound z hz)
    simpa only [cap,mul_assoc] using h
  have hc (z : Z) (hz : z ∈ S) : 0 < c z := by
    by_contra! hNot
    have hPos := mul_nonpos_of_nonneg_of_nonpos hf.le hNot
    linarith only [hPos,hRound z hz]
  have hMom (z : Z) (hz : z ∈ S) := block_parts_degree_moments s p a hs hFrac hp.le (w z) (hWeight z hz)
  exact expected_block_capacity_lower S (blockPartsMass s) (blockPartsInternalCount s x y) X c d cap
    p fraction a (Fintype.card E)
    (fun t => prod_nonneg (fun i _ => by unfold partSampleMass; positivity))
    hp hf ha (Nat.cast_nonneg _)
    (block_parts_internal_count_mean_lower s p hs hTwo hFrac x y hxy)
    (fun z hz t => sum_nonneg fun i _ => sum_nonneg fun v _ => (hWeight z hz i v).1)
    hc (fun z hz => sum_nonneg fun i _ => sum_nonneg fun v _ => (hWeight z hz i v).1)
    hHalf (fun z hz => (hBounds z hz).1) (fun z hz => (hBounds z hz).2) hSmall
    (fun z hz => (hMom z hz).1) (fun z hz => (hMom z hz).2)

end BlockMoments

end OverfullWork.ChenShan
