module

public import OverfullWork.ChenShanUniformInclusion
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace OverfullWork.UniformSubsetSampling

open Finset Real
open scoped Classical

variable {V : Type*} [Fintype V]

omit [Fintype V] in
private theorem intersection_exp_powerset (A X : Finset V) (t : ℝ) :
    exp (t*((A ∩ X).card : ℝ)) =
      ∑ T ∈ A.powerset, if T ⊆ X then (exp t-1)^T.card else 0 := by
  let z := exp t-1
  calc
    _ = ∏ v ∈ A, exp (if v ∈ X then t else 0) := by
      rw [← exp_sum,← sum_filter,filter_mem_eq_inter]
      congr 1
      simp [nsmul_eq_mul,mul_comm]
    _ = ∏ v ∈ A, (1 + if v ∈ X then z else 0) := by
      apply prod_congr rfl
      intro v _
      by_cases hv : v ∈ X <;> simp [hv,z]
    _ = _ := by
      rw [prod_one_add]
      apply sum_congr rfl
      intro T _
      by_cases hT : T ⊆ X
      · rw [ite_eq_left hT]
        have hProd : (∏ v ∈ T, if v ∈ X then z else 0) = ∏ _v ∈ T, z :=
          prod_congr rfl (fun v hv => ite_eq_left (hT hv))
        rw [hProd,prod_const]
      · rw [ite_eq_right hT]
        obtain ⟨v,hv,hx⟩ := not_subset.mp hT
        exact prod_eq_zero hv (ite_eq_right hx)

/-- The moment bound for sampling without replacement has no prefactor
depending on the ambient order. The mean is the sample proportion
times the size of the set being tested. -/
theorem fixed_size_intersection_moment {k : ℕ} (hk : k ≤ Fintype.card V)
    (A : Finset V) (t : ℝ) (ht : 0 ≤ t) :
    (∑ X ∈ (univ : Finset V).powersetCard k, exp (t*((A ∩ X).card : ℝ))) /
        (Fintype.card V).choose k ≤
      exp (((k:ℝ)/Fintype.card V)*A.card*(exp t-1)) := by
  let p := (k:ℝ)/Fintype.card V
  let z := exp t-1
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hz : 0 ≤ z := sub_nonneg.mpr (one_le_exp_iff.mpr ht)
  let C := (univ : Finset V).powersetCard k
  have hSum :
      (∑ X ∈ C, exp (t*((A ∩ X).card : ℝ))) / (Fintype.card V).choose k =
        ∑ T ∈ A.powerset, z^T.card*probability k (fun X => T ⊆ X) := by
    simp_rw [intersection_exp_powerset]
    rw [sum_comm,sum_div]
    apply sum_congr rfl
    intro T _
    let W := @Finset.filter (Finset V) (fun X => T ⊆ X)
      (fun X => Classical.propDecidable (T ⊆ X)) C
    have hW : (∑ X ∈ C, if T ⊆ X then (exp t-1)^T.card else 0) =
        ∑ _X ∈ W, z^T.card := by
      dsimp only [W]
      rw [sum_filter]
      apply sum_congr rfl
      intro X _
      by_cases h : T ⊆ X <;> simp [h,z]
    rw [hW,sum_const,nsmul_eq_mul]
    change (W.card : ℝ)*z^T.card/(Fintype.card V).choose k =
      z^T.card * ((W.card : ℝ) / (Fintype.card V).choose k)
    ring
  change (∑ X ∈ C, _) / _ ≤ _
  rw [hSum]
  calc
    _ ≤ ∑ T ∈ A.powerset, (p*z)^T.card := by
      apply sum_le_sum
      intro T _
      rw [mul_pow,mul_comm (p^T.card)]
      exact mul_le_mul_of_nonneg_left (probability_contains_le T hk) (pow_nonneg hz _)
    _ = (1+p*z)^A.card := by
      simpa only [prod_const] using (prod_one_add (f := fun _ : V => p*z) A).symm
    _ ≤ (exp (p*z))^A.card :=
      pow_le_pow_left₀ (by positivity) (add_one_le_exp (p*z) |> fun h => by simpa only [add_comm] using h) _
    _ = _ := by
      rw [← exp_nat_mul]
      congr 1
      dsimp only [p,z]
      ring

/-- The upper tail for the intersection count of a uniform sample of
size k, with an additive deviation e*k. -/
theorem fixed_size_intersection_upper {k : ℕ} (hk : k ≤ Fintype.card V)
    (A : Finset V) (e : ℝ) (he : 0 ≤ e) (he₁ : e ≤ 2) :
    probability k (fun X => e*k ≤
      ((A ∩ X).card : ℝ)-((k:ℝ)/Fintype.card V)*A.card) ≤ exp (-(e^2*k)/4) := by
  let μ := ((k:ℝ)/Fintype.card V)*A.card
  let t := e/2
  let P (X : Finset V) := e*k ≤ ((A ∩ X).card : ℝ)-μ
  let C := (univ : Finset V).powersetCard k
  let H := (Fintype.card V).choose k
  have hH : 0 < (H:ℝ) := by exact_mod_cast Nat.choose_pos hk
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have ht₁ : |t| ≤ 1 := by rw [abs_of_nonneg ht]; dsimp only [t]; linarith only [he₁]
  have hμ : 0 ≤ μ := by dsimp only [μ]; positivity
  have hμk : μ ≤ k := by
    by_cases hN : Fintype.card V = 0
    · simp [μ,hN]
    · have hN' : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
      have hA : (A.card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ A
      have hm := mul_le_mul_of_nonneg_left hA (show 0 ≤ (k:ℝ)/Fintype.card V by positivity)
      rw [div_mul_cancel₀ _ hN'.ne'] at hm
      exact hm
  have hPoint (X : Finset V) (hX : P X) : exp (t*(μ+e*k)) ≤ exp (t*((A ∩ X).card:ℝ)) := by
    unfold P at hX
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith only [hX]) ht)
  have hSum :
      ((C.filter P).card : ℝ)*exp (t*(μ+e*k)) ≤
        ∑ X ∈ C, exp (t*((A ∩ X).card:ℝ)) := by
    calc
      _ = ∑ _X ∈ C.filter P, exp (t*(μ+e*k)) := by simp [nsmul_eq_mul]
      _ ≤ ∑ X ∈ C.filter P, exp (t*((A ∩ X).card:ℝ)) :=
        sum_le_sum fun X hX => hPoint X (mem_filter.mp hX).2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => (exp_pos _).le)
  have hScale :
      probability k P * exp (t*(μ+e*k)) ≤ exp (μ*(exp t-1)) := by
    have h := div_le_div_of_nonneg_right hSum hH.le
    rw [mul_div_right_comm] at h
    exact h.trans (fixed_size_intersection_moment hk A t ht)
  have hh := (le_div_iff₀ (exp_pos _)).2 hScale
  rw [← exp_sub] at hh
  refine hh.trans (exp_le_exp.mpr ?_)
  have hTaylor := (le_abs_self (exp t-1-t)).trans (abs_exp_sub_one_sub_id_le ht₁)
  have h1 := mul_le_mul_of_nonneg_left hTaylor hμ
  have h2 := mul_le_mul_of_nonneg_right hμk (sq_nonneg t)
  dsimp only [t] at h1 h2 ⊢
  nlinarith only [h1,h2]

/-- Two-sided hypergeometric concentration with the sample size in
the exponent. The lower tail is the upper tail for nonmembers of A. -/
theorem fixed_size_intersection_two_sided {k : ℕ} (hk : k ≤ Fintype.card V)
    (A : Finset V) (e : ℝ) (he : 0 ≤ e) (he₁ : e ≤ 2) :
    probability k (fun X => e*k ≤
      |((A ∩ X).card : ℝ)-((k:ℝ)/Fintype.card V)*A.card|) ≤
        2*exp (-(e^2*k)/4) := by
  let p := (k:ℝ)/Fintype.card V
  let P (X : Finset V) := e*k ≤ ((A ∩ X).card : ℝ)-p*A.card
  let Q (X : Finset V) := e*k ≤ ((Aᶜ ∩ X).card : ℝ)-p*(Aᶜ : Finset V).card
  let H (X : Finset V) := e*k ≤ |((A ∩ X).card : ℝ)-p*A.card|
  let _ : DecidablePred P := fun _ => Classical.propDecidable _
  let _ : DecidablePred Q := fun _ => Classical.propDecidable _
  let _ : DecidablePred H := fun _ => Classical.propDecidable _
  let C := (univ : Finset V).powersetCard k
  have hComplementMean : p*(Aᶜ : Finset V).card+p*A.card = k := by
    by_cases hn : Fintype.card V = 0
    · have hk₀ : k = 0 := by omega
      simp [p,hk₀,hn]
    · have hn' : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
      have hCards : ((Aᶜ : Finset V).card : ℝ)+A.card = (Fintype.card V : ℝ) := by
        rw [card_compl,Nat.cast_sub (card_le_univ A)]
        ring
      rw [← mul_add,hCards]
      exact div_mul_cancel₀ _ hn'
  have hSub : C.filter H ⊆ C.filter P ∪ C.filter Q := by
    intro X hX
    obtain ⟨hC,hH⟩ := mem_filter.mp hX
    rcases le_abs.mp hH with hp|hq
    · exact mem_union_left _ (mem_filter.mpr ⟨hC,hp⟩)
    · have hDiff : X \ A = Aᶜ ∩ X := by ext v; simp [mem_sdiff,and_comm]
      have hCard := card_sdiff_add_card_inter X A
      rw [hDiff,inter_comm X A,(mem_powersetCard.mp hC).2] at hCard
      have hCardR : ((Aᶜ ∩ X).card : ℝ)+((A ∩ X).card : ℝ)=k := by exact_mod_cast hCard
      apply mem_union_right _ (mem_filter.mpr ⟨hC,?_⟩)
      dsimp only [Q]
      linarith only [hCardR,hComplementMean,hq]
  have hN : 0 ≤ ((Fintype.card V).choose k : ℝ) := by positivity
  have hUnionNat := (card_le_card hSub).trans (card_union_le _ _)
  have hUnion : probability k H ≤ probability k P + probability k Q := by
    unfold probability
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hUnionNat) hN
  calc
    _ ≤ probability k P + probability k Q := hUnion
    _ ≤ exp (-(e^2*k)/4) + exp (-(e^2*k)/4) :=
      add_le_add (fixed_size_intersection_upper hk A e he he₁)
        (fixed_size_intersection_upper hk Aᶜ e he he₁)
    _ = _ := by ring

end OverfullWork.UniformSubsetSampling
