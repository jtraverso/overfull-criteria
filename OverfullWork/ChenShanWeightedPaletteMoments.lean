module

public import OverfullWork.ChenShanConditionalPermutation
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.UniformSubsetSampling

open Finset
open scoped Classical

variable {W : Type*} [Fintype W]

/-- Finite expectation for the same fixed-size sample as probability. -/
noncomputable def sampleExpectation (s : ℕ) (f : Finset W → ℝ) : ℝ :=
  (∑ X ∈ (univ : Finset W).powersetCard s, f X) / (Fintype.card W).choose s

/-- Each weight contributes with its exact marginal inclusion probability. -/
theorem expected_fixed_size_weight (s : ℕ) (hs : s ≤ Fintype.card W) (w : W → ℝ) :
    sampleExpectation s (fun X => ∑ x ∈ X, w x) =
      ((s:ℝ)/Fintype.card W) * ∑ x, w x := by
  let F := (univ : Finset W).powersetCard s
  let n := Fintype.card W
  have hX (X : Finset W) : (∑ x ∈ X, w x) = ∑ x, if x ∈ X then w x else 0 := by
    rw [← sum_filter]
    congr 1
    ext x
    simp
  have hAtom (x : W) : (∑ X ∈ F, if x ∈ X then w x else 0)/(n.choose s) =
      ((s:ℝ)/n)*w x := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
    have h := probability_contains_vertex x hs
    unfold probability at h
    have hRatio : ((F.filter (fun X => x ∈ X)).card:ℝ)/(n.choose s) = (s:ℝ)/n := by
      convert h using 3
      congr 1
      ext X
      simp [F]
    rw [← hRatio]
    ring
  change (∑ X ∈ F, ∑ x ∈ X, w x)/(n.choose s) = _
  simp_rw [hX]
  rw [sum_comm,sum_div,mul_sum]
  exact sum_congr rfl (fun x _ => by simpa only [mem_univ,ite_true] using hAtom x)

end OverfullWork.UniformSubsetSampling

namespace OverfullWork.ChenShan

open Finset UniformSubsetSampling

/-- The expectation estimate in (5.4), allowing a palette drawn only
from the permitted colors. The weights count copies of each color. -/
theorem expected_palette_edge_count
    {W : Type*} [Fintype W] (s k : ℕ) (hs : s ≤ Fintype.card W) (hk : 0 < k)
    (hW : (511/512 : ℝ)*k ≤ Fintype.card W)
    (w : W → ℝ) (E : ℝ) (hE : 0 ≤ E) (hWeight : (∑ x, w x) ≤ E) :
    sampleExpectation s (fun X => ∑ x ∈ X, w x) ≤ (33/32 : ℝ)*((s:ℝ)/k)*E := by
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hLower : 0 < (511/512 : ℝ)*k := by positivity
  have hFraction : (s:ℝ)/Fintype.card W ≤ (512/511:ℝ)*((s:ℝ)/k) := by
    calc
      _ ≤ (s:ℝ)/((511/512:ℝ)*k) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hLower hW
      _ = _ := by ring
  rw [expected_fixed_size_weight s hs]
  calc
    _ ≤ ((s:ℝ)/Fintype.card W)*E := mul_le_mul_of_nonneg_left hWeight (by positivity)
    _ ≤ ((512/511:ℝ)*((s:ℝ)/k))*E := mul_le_mul_of_nonneg_right hFraction hE
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (512/511:ℝ) ≤ 33/32) (by positivity)) hE

end OverfullWork.ChenShan
