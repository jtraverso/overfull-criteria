module

public import OverfullWork.ChenShanSampledCapacityVariance
public import OverfullWork.ChenShanHypergeometricTail
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real UniformSubsetSampling
open scoped Classical

variable {I : Type*} [Fintype I] {V : I → Type*} [∀ i, Fintype (V i)]

/-- The intersection counts add over parts. Their exponential moments
multiply under the product law, with no loss from a union over parts. -/
theorem sampled_block_intersection_moment (s : I → ℕ) (p t : ℝ)
    (hs : ∀ i, s i ≤ Fintype.card (V i))
    (hFrac : ∀ i, (s i:ℝ)/Fintype.card (V i) = p) (ht : 0 ≤ t)
    (A : ∀ i, Finset (V i)) :
    blockMean (blockPartsMass s) (fun X => exp (t*(∑ i, ((A i ∩ (X i).val).card:ℝ)))) ≤
      exp (p*(∑ i, ((A i).card:ℝ))*(exp t-1)) := by
  classical
  let g (i : I) (X : PartSample (V i) (s i)) := exp (t*((A i ∩ X.val).card:ℝ))
  have hg (X : BlockParts (V := V) s) :
      exp (t*(∑ i, ((A i ∩ (X i).val).card:ℝ))) = ∏ i, g i (X i) := by
    rw [mul_sum, exp_sum]
  simp only [hg]
  change blockMean (partProductMass (fun i => partSampleMass (s i))) _ ≤ _
  rw [blockMean_product]
  calc
    _ ≤ ∏ i, exp (p*((A i).card:ℝ)*(exp t-1)) := by
      apply prod_le_prod₀
      · intro i _
        apply sum_nonneg
        intro X _
        unfold partSampleMass g
        positivity
      · intro i _
        dsimp only [g]
        rw [blockMean_partSample (s i) (fun Y => exp (t*((A i ∩ Y).card:ℝ)))]
        have h := fixed_size_intersection_moment (hs i) (A i) t ht
        rw [hFrac] at h
        unfold sampleExpectation
        simpa only [div_eq_mul_inv, one_div, mul_comm] using h
    _ = _ := by
      rw [← exp_sum, ← sum_mul, ← mul_sum]

/-- All ordinary preferred edges have distinct core endpoints. If A
lists those endpoints in each part, a block has at least half the
expected count except with exponentially small probability. -/
theorem sampled_ordinary_preferred_edges_lower_tail (s : I → ℕ) (p : ℝ)
    (hs : ∀ i, s i ≤ Fintype.card (V i))
    (hFrac : ∀ i, (s i:ℝ)/Fintype.card (V i) = p) (hp : 0 < p)
    (A : ∀ i, Finset (V i)) (hA : 0 < ∑ i, ((A i).card:ℝ)) :
    let N : ℝ := ∑ i, (Fintype.card (V i):ℝ)
    let d : ℝ := ∑ i, ((A i).card:ℝ)
    blockMean (blockPartsMass s) (fun X =>
      eventIndicator ((∑ i, ((A i ∩ (X i).val).card:ℝ)) < p*d/2)) ≤
        exp (-p*d^2/(16*N)) := by
  classical
  intro N d
  have hd : 0 < d := hA
  have hDN : d ≤ N := sum_le_sum (fun i _ => by exact_mod_cast card_le_univ (A i))
  have hN : 0 < N := hd.trans_le hDN
  let C (i : I) : Finset (V i) := (A i)ᶜ
  let μ := p*(∑ i, ((C i).card:ℝ))
  let t := d/(4*N)
  have ht : 0 ≤ t := by positivity
  have ht₁ : |t| ≤ 1 := by
    rw [abs_of_nonneg ht]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [hDN,hN])
  have hμ : 0 ≤ μ := by dsimp [μ]; positivity
  have hμN : μ ≤ p*N :=
    mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => by exact_mod_cast card_le_univ (C i)) hp.le
  have hSizes : (∑ i, (s i:ℝ)) = p*N := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    by_cases h : (Fintype.card (V i):ℝ) = 0
    · rw [h, mul_zero]
      have h' : Fintype.card (V i) = 0 := by exact_mod_cast h
      have hz : s i = 0 := Nat.le_zero.mp ((hs i).trans_eq h')
      simp [hz]
    · rw [← hFrac i, div_mul_cancel₀ _ h]
  have hSplit (X : BlockParts (V := V) s) :
      (∑ i, ((A i ∩ (X i).val).card:ℝ)) +
      (∑ i, ((C i ∩ (X i).val).card:ℝ)) = p*N := by
    rw [← sum_add_distrib, ← hSizes]
    apply sum_congr rfl
    intro i _
    have hPart := (X i).property
    have hCount := card_inter_add_card_sdiff (X i).val (A i)
    rw [inter_comm, sdiff_eq_inter_compl, inter_comm (X i).val] at hCount
    exact_mod_cast hCount.trans (mem_powersetCard.mp hPart).2
  have hMuEq : p*N = μ+p*d := by
    dsimp only [μ, N, d]
    rw [← mul_add, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    exact_mod_cast (card_compl_add_card (A i)).symm
  let P (X : BlockParts (V := V) s) := (∑ i, ((A i ∩ (X i).val).card:ℝ)) < p*d/2
  have hMoment := sampled_block_intersection_moment s p t hs hFrac ht C
  have hMarkov :
      blockMean (blockPartsMass s) (fun X => eventIndicator (P X))*exp (t*(μ+p*d/2)) ≤
        exp (μ*(exp t-1)) := by
    refine le_trans ?_ hMoment
    unfold blockMean
    rw [sum_mul]
    apply sum_le_sum
    intro X _
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (blockPartsMass_nonneg s X)
    by_cases h : P X
    · simp only [eventIndicator, ite_eq_left h, one_mul]
      apply exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ ht
      have hh := hSplit X
      rw [hMuEq] at hh
      dsimp only [P] at h
      linarith only [hh,h]
    · simp only [eventIndicator, ite_eq_right h, zero_mul]
      exact (exp_pos _).le
  have hBound := (le_div_iff₀ (exp_pos (t*(μ+p*d/2)))).mpr hMarkov
  rw [← exp_sub] at hBound
  refine hBound.trans (exp_le_exp.mpr ?_)
  have hTaylor := (le_abs_self (exp t-1-t)).trans (abs_exp_sub_one_sub_id_le ht₁)
  have h1 := mul_le_mul_of_nonneg_left hTaylor hμ
  have h2 := mul_le_mul_of_nonneg_right hμN (sq_nonneg t)
  have hAlgebra : p*N*t^2-t*(p*d/2) = -p*d^2/(16*N) := by
    dsimp only [t]
    field_simp [hN.ne']
    ring
  rw [← hAlgebra]
  nlinarith only [h1,h2]

end OverfullWork.ChenShan
