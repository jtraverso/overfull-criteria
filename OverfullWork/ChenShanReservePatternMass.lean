module

public import OverfullWork.IndependentBernoulliSampling
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.IndependentBernoulliSampling

open Finset
open scoped Classical

variable {I : Type*} [Fintype I]

/-- In the Bernoulli sample space the probability that every index in
a finite set is selected is the product of its individual probabilities. -/
theorem mass_forced_true (p : I → ℝ) (K : Finset I) :
    (∑ s ∈ univ.filter (fun s : I → Bool => ∀ e ∈ K, s e = true), mass p s) =
      ∏ e ∈ K, p e := by
  let f (i : I) (b : Bool) : ℝ :=
    if b then p i else if i ∈ K then 0 else 1-p i
  rw [sum_filter]
  have hPoint (s : I → Bool) :
      (if ∀ e ∈ K, s e = true then mass p s else 0) = ∏ i, f i (s i) := by
    split_ifs with h
    · unfold mass
      apply prod_congr rfl
      intro i _
      by_cases hi : i ∈ K
      · simp [f,h i hi]
      · simp [f,hi]
    · push Not at h
      obtain ⟨i,hi,hs⟩ := h
      have hs₀ : s i = false := by cases hsi : s i <;> simp_all
      symm
      apply prod_eq_zero (mem_univ i)
      simp [f,hi,hs₀]
  simp_rw [hPoint]
  rw [← Fintype.prod_sum (κ := fun _ : I => Bool) f]
  have hFactor (i : I) : (∑ b : Bool, f i b) = if i ∈ K then p i else 1 := by
    by_cases hi : i ∈ K
    · simp [f,hi]
    · simp [f,hi]
  simp_rw [hFactor]
  have hK : (univ.filter (fun i => i ∈ K) : Finset I) = K := by ext; simp
  rw [← prod_filter,hK]


private noncomputable def patternMass {J Ω : Type*} [Fintype Ω]
    (bits : Ω → J → Bool) (w : Ω → ℝ) (U W : Finset J) : ℝ :=
  ∑ s ∈ univ.filter (fun s => (∀ j ∈ U, bits s j = true) ∧ (∀ j ∈ W, bits s j = false)), w s

private theorem patternMass_insert_false {J Ω : Type*} [Fintype Ω]
    (g : Ω → J → Bool) (w : Ω → ℝ) (U W : Finset J) (j : J) :
    patternMass g w U (insert j W) =
      patternMass g w U W - patternMass g w (insert j U) W := by
  unfold patternMass
  let A := univ.filter (fun s => (∀ k ∈ U, g s k = true) ∧ (∀ k ∈ W, g s k = false))
  let B := univ.filter (fun s => (∀ k ∈ insert j U, g s k = true) ∧ (∀ k ∈ W, g s k = false))
  have hB : B ⊆ A := by
    intro s hs
    simp only [A,B,mem_filter,mem_univ,true_and,forall_mem_insert] at hs ⊢
    exact ⟨hs.1.2,hs.2⟩
  have hEq : univ.filter
      (fun s => (∀ k ∈ U, g s k = true) ∧ (∀ k ∈ insert j W, g s k = false)) = A \ B := by
    ext s
    simp only [A,B,mem_filter,mem_univ,true_and,forall_mem_insert,mem_sdiff]
    cases g s j <;> simp only [Bool.false_eq_true,Bool.true_eq_false] <;> tauto
  rw [hEq]
  exact eq_sub_of_add_eq (sum_sdiff hB)

private theorem patternMass_eq_of_forced_true {J Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (g : Ω → J → Bool) (h : Ξ → J → Bool) (a : Ω → ℝ) (b : Ξ → ℝ)
    (hh : ∀ U, patternMass g a U ∅ = patternMass h b U ∅)
    (U W : Finset J) : patternMass g a U W = patternMass h b U W := by
  induction W using Finset.induction_on generalizing U with
  | empty => exact hh U
  | insert j W _ ih =>
    rw [patternMass_insert_false,patternMass_insert_false,ih U,ih (insert j U)]

/-- The indicators that both edges of a pair are sampled have the product
Bernoulli law when all pairs are edge-disjoint. -/
theorem pair_sample_mass {J : Type*} [Fintype J] (p : I → ℝ)
    (f : J × Bool ↪ I) (t : J → Bool) :
    (∑ s ∈ univ.filter (fun s : I → Bool =>
      (fun j => s (f (j,false)) && s (f (j,true))) = t), mass p s) =
      mass (fun j => p (f (j,false))*p (f (j,true))) t := by
  let g (s : I → Bool) (j : J) := s (f (j,false)) && s (f (j,true))
  let q (j : J) := p (f (j,false))*p (f (j,true))
  have hForced (U : Finset J) :
      patternMass g (mass p) U ∅ = patternMass id (mass q) U ∅ := by
    unfold patternMass
    simp only [notMem_empty, false_implies, implies_true, and_true, id_eq]
    rw [mass_forced_true q U]
    let K := (U ×ˢ (univ : Finset Bool)).map f
    have hE : (univ.filter fun s : I → Bool => ∀ j ∈ U, g s j = true) =
        (univ.filter fun s : I → Bool => ∀ e ∈ K, s e = true) := by
      ext s
      simp only [mem_filter,mem_univ,true_and,g,Bool.and_eq_true]
      constructor
      · intro hs e he
        obtain ⟨⟨j,b⟩,hjb,rfl⟩ := mem_map.mp he
        have hj := (mem_product.mp hjb).1
        cases b
        · exact (hs j hj).1
        · exact (hs j hj).2
      · intro hs j hj
        exact ⟨hs _ (mem_map.mpr ⟨(j,false),mem_product.mpr ⟨hj,mem_univ _⟩,rfl⟩),
          hs _ (mem_map.mpr ⟨(j,true),mem_product.mpr ⟨hj,mem_univ _⟩,rfl⟩)⟩
    rw [hE,mass_forced_true p K]
    simp [K,q,prod_map,prod_product,mul_comm]
  let U := univ.filter fun j => t j = true
  let W := univ.filter fun j => t j = false
  have hMatch (r : J → Bool) :
      ((∀ j ∈ U, r j = true) ∧ (∀ j ∈ W, r j = false)) ↔ r=t := by
    constructor
    · intro hh
      funext j
      cases hj : t j
      · exact hh.2 j (by simp [W,hj])
      · exact hh.1 j (by simp [U,hj])
    · rintro rfl
      exact ⟨fun j hj => (mem_filter.mp hj).2,fun j hj => (mem_filter.mp hj).2⟩
  have h := patternMass_eq_of_forced_true g id (mass p) (mass q) hForced U W
  unfold patternMass at h
  simp only [id_eq,hMatch] at h
  rw [h]
  have hOne : (univ.filter (fun s : J → Bool => s=t)) = {t} := by
    ext s
    simp only [mem_filter,mem_univ,true_and,mem_singleton]
  rw [hOne,sum_singleton]


/-- Any event of the pair indicators can be measured in the original
sample space or in the smaller independent Bernoulli sample space. -/
theorem pair_event_mass {J : Type*} [Fintype J] (p : I → ℝ)
    (f : J × Bool ↪ I) (B : (J → Bool) → Prop) :
    (∑ s ∈ univ.filter (fun s : I → Bool =>
      B (fun j => s (f (j,false)) && s (f (j,true)))), mass p s) =
      ∑ t ∈ univ.filter B, mass (fun j => p (f (j,false))*p (f (j,true))) t := by
  let g (s : I → Bool) (j : J) := s (f (j,false)) && s (f (j,true))
  change (∑ s ∈ univ.filter (fun s => B (g s)), mass p s) = _
  calc
    _ = ∑ t ∈ univ.filter B, ∑ s ∈ univ.filter (fun s : I → Bool => g s=t), mass p s := by
      simp_rw [sum_filter]
      have hSplit (t : J → Bool) :
          (if B t then ∑ s, if g s=t then mass p s else 0 else 0) =
            ∑ s, if g s=t ∧ B t then mass p s else 0 := by
        by_cases hb : B t <;> simp [hb]
      simp_rw [hSplit]
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      rw [sum_eq_single (g s)]
      · by_cases hs : B (g s) <;> simp [hs]
      · intro t _ hne
        have hn : g s ≠ t := Ne.symm hne
        by_cases ht : B t <;> simp [ht,hn]
      · simp
    _ = _ := by
      apply sum_congr rfl
      intro t _
      exact pair_sample_mass p f t

/-- The two-sided deviation bound for the number of selected pairs,
including pairs whose two edges have different probabilities. -/
theorem pair_count_abs_tail {J : Type*} [Fintype J] (p : I → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp' : ∀ e, p e ≤ 1)
    (f : J × Bool ↪ I) (T : Finset J)
    {M D : ℝ} (hM : 0 < M)
    (hMean : mean (fun j => p (f (j,false))*p (f (j,true))) T ≤ M)
    (hD : 0 ≤ D) (hD' : D ≤ 2*M) :
    (∑ s ∈ univ.filter (fun s : I → Bool => D ≤
      |count T (fun j => s (f (j,false)) && s (f (j,true))) -
        mean (fun j => p (f (j,false))*p (f (j,true))) T|), mass p s) ≤
      2*Real.exp (-(D^2/(4*M))) := by
  let q (j : J) := p (f (j,false))*p (f (j,true))
  have hq (j : J) : 0 ≤ q j := mul_nonneg (hp _) (hp _)
  have hq' (j : J) : q j ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right (hp' _) (hp _)).trans (by simpa only [one_mul] using hp' (f (j,true)))
  calc
    _ = ∑ t ∈ univ.filter (fun t : J → Bool => D ≤ |count T t-mean q T|), mass q t :=
      pair_event_mass p f (fun t => D ≤ |count T t-mean q T|)
    _ ≤ _ := abs_tail_bound_of_mean_le q hq hq' T hM hMean hD hD'

end OverfullWork.IndependentBernoulliSampling
