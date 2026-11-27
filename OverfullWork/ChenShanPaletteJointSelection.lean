module

public import OverfullWork.ChenShanDisjointPaletteSampling
public import OverfullWork.ChenShanWeightedPaletteMoments
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real UniformSubsetSampling
open scoped Classical
universe u

set_option maxHeartbeats 1200000 in
/-- The large edge-set tests of (5.4) hold together with (5.3) on a
single family of disjoint palettes. Here delta bounds palette sizes
below as a fraction of k, and xi bounds large edge counts below as a
fraction of k. Only the large edge sets need appear among the tests. -/
theorem exists_palettes_with_incidence_and_edge_counts
    (p j : ℕ) (C θ δ ξ : ℝ)
    (hC : 0 ≤ C) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hδ : 0 < δ) (hξ : 0 < ξ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
    ∀ {W I V J : Type u} [Fintype W] [Fintype I] [Fintype V] [Fintype J],
      Fintype.card I ≤ p → (Fintype.card V:ℝ) ≤ C*k → Fintype.card J ≤ j →
      (511/512 : ℝ)*k ≤ Fintype.card W → Fintype.card W ≤ k →
    ∀ (s : I → ℕ) (c : V → ℕ) (A : V → Finset W)
      (label : J → I) (w : J → W → ℝ) (E : J → ℝ),
      (∑ i, s i) ≤ Fintype.card W →
      (∀ i, δ*k ≤ (s i:ℝ)) →
      (∀ v, θ*k ≤ (c v:ℝ)) →
      (∀ v, (511/512 : ℝ)*(c v:ℝ) ≤ (A v).card) →
      (∀ v, (A v).card ≤ c v) →
      (∀ t, ξ*k ≤ E t) →
      (∀ t x, 0 ≤ w t x ∧ w t x ≤ ζ*k) →
      (∀ t, (∑ x, w t x) ≤ E t) →
      ∃ P : I → Finset W, (∀ i, (P i).card = s i) ∧
        Pairwise (fun i l => Disjoint (P i) (P l)) ∧
        (∀ i v, (15/16 : ℝ)*((s i:ℝ)/k)*c v ≤ ((A v ∩ P i).card:ℝ) ∧
          ((A v ∩ P i).card:ℝ) ≤ 2*((s i:ℝ)/k)*c v) ∧
        ∀ t, (∑ x ∈ P (label t), w t x) ≤ (5/4 : ℝ)*((s (label t):ℝ)/k)*E t := by
  let ζ := δ*ξ/(100*((j:ℝ)+1))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  obtain ⟨N,hN⟩ := exists_palette_incidence_risk_threshold.{u} p C θ δ (1/2)
    hC hθ hδ (by norm_num)
  refine ⟨ζ,hζ,max N 1,?_⟩
  intro k hk W I V J _ _ _ _ hI hV hJ hWlo hWhi
    s c A label w E hSlots hFrac hActive hAvailable hTotal hLarge hWeight hSum
  have hk₀ : 0 < k := (le_max_right N 1).trans hk
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk₀
  let bad (t : J) (X : Finset W) := (5/4:ℝ)*((s (label t):ℝ)/k)*E t < ∑ x ∈ X, w t x
  have hBound (t : J) : probability (s (label t)) (bad t) ≤ 1/(4*((j:ℝ)+1)) := by
    let fraction := (s (label t):ℝ)/k
    have hsR : 0 < (s (label t):ℝ) :=
      (mul_pos hδ hkR).trans_le (hFrac (label t))
    have hs₀ : 0 < s (label t) := by exact_mod_cast hsR
    have hs : s (label t) ≤ Fintype.card W :=
      (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ (label t))).trans hSlots
    have hE : 0 < E t := (mul_pos hξ hkR).trans_le (hLarge t)
    have hf : 0 < fraction := div_pos hsR hkR
    have hflo : δ ≤ fraction := (le_div_iff₀ hkR).mpr (hFrac (label t))
    have hTail := palette_edge_count_tail (s (label t)) k hs hs₀ hk₀ hWlo
      (w t) (ζ*k) (E t) (by positivity) hE (hWeight t) (hSum t)
    change probability (s (label t)) (bad t) ≤
      ((33/32:ℝ)*fraction*(ζ*k)*E t)/(((7/32:ℝ)*fraction*E t)^2) at hTail
    have hSimpl : ((33/32:ℝ)*fraction*(ζ*k)*E t)/(((7/32:ℝ)*fraction*E t)^2) =
        (1056/49:ℝ)*((ζ*k)/(fraction*E t)) := by
      field_simp [hf.ne',hE.ne']
      norm_num
    have hDen : 0 < (100:ℝ)*((j:ℝ)+1) := by positivity
    have hRatio : (ζ*k)/(fraction*E t) ≤ 1/(100*((j:ℝ)+1)) := by
      apply (div_le_div_iff₀ (mul_pos hf hE) hDen).mpr
      have hProd := mul_le_mul hflo (hLarge t) (by positivity : 0 ≤ ξ*(k:ℝ)) hf.le
      have hEq : (ζ*k)*(100*((j:ℝ)+1)) = δ*(ξ*k) := by
        dsimp [ζ]
        field_simp
      rw [hEq,one_mul]
      exact hProd
    rw [hSimpl] at hTail
    calc
      _ ≤ (1056/49:ℝ)*((ζ*k)/(fraction*E t)) := hTail
      _ ≤ (1056/49:ℝ)*(1/(100*((j:ℝ)+1))) := mul_le_mul_of_nonneg_left hRatio (by norm_num)
      _ ≤ _ := by
        have hj : 0 < (j:ℝ)+1 := by positivity
        apply (le_div_iff₀ (show 0 < (4:ℝ)*((j:ℝ)+1) by positivity)).mpr
        field_simp
        nlinarith only [hj]
  have hWeighted : (∑ t, probability (s (label t)) (bad t)) ≤ (1/4:ℝ) := by
    calc
      _ ≤ ∑ _t : J, 1/(4*((j:ℝ)+1)) := sum_le_sum (fun t _ => hBound t)
      _ ≤ (j:ℝ)*(1/(4*((j:ℝ)+1))) := by
        simp only [sum_const,card_univ,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) (by positivity)
      _ ≤ _ := by
        rw [mul_one_div]
        apply (div_le_iff₀ (show 0 < (4:ℝ)*((j:ℝ)+1) by positivity)).mpr
        linarith
  have hIncRisk := hN k ((le_max_left N 1).trans hk) hI hV s hFrac
  have hRisk : (∑ i : I × V, 2*exp (-((θ/32)^2*(s i.1:ℝ))/4)) +
      (∑ t, probability (s (label t)) (bad t)) < 1 := by
    linarith only [hWeighted,hIncRisk]
  obtain ⟨P,hCard,hDisj,hTest,hInc⟩ := exists_disjoint_palettes_with_incidence_and_tests
    s hSlots k hk₀ θ hθ hθ₁ hWlo hWhi c A hActive hAvailable hTotal label bad hRisk
  exact ⟨P,hCard,hDisj,hInc,fun t => le_of_not_gt (hTest t)⟩

end OverfullWork.ChenShan
