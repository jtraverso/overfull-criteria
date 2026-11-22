module

public import OverfullWork.DirectedLocalBatchParameters
public import OverfullWork.DirectedBatchScales

@[expose] public section


/-! Stage-scale choices in GGKLO 7.3(ii). A larger reserve block makes
the small-batch tolerance available, while the reciprocal block count
controls the accumulated cyclic charge of the stage. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset
open scoped Classical

/-- Pick an integer block count compatible with both the regularity
tolerance of a small batch and the loss rate of the entire stage. -/
theorem exists_stage_block_count (κ s : ℝ) (hκ : 0 < κ) (hs : 0 < s)
    (hSmall : 16*s ≤ κ) :
    ∃ k : ℕ, 4*s ≤ κ/((k+2:ℕ):ℝ) ∧ 1/((k+2:ℕ):ℝ) ≤ 8*s/κ := by
  let K := ⌈κ/(8*s)⌉₊
  have hd : 0 < 8*s := by positivity
  have hLo : (2:ℝ) ≤ κ/(8*s) := (le_div_iff₀ hd).mpr (by linarith only [hSmall])
  have hC : κ/(8*s) ≤ (K:ℝ) := Nat.le_ceil _
  have hK : 2 ≤ K := by exact_mod_cast hLo.trans hC
  have hKR : 0 < (K:ℝ) := by positivity
  have hUp : (K:ℝ) ≤ κ/(4*s) := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ κ/(8*s) by positivity)
    have he : κ/(4*s) = 2*(κ/(8*s)) := by field_simp; ring
    linarith only [h,hLo,he]
  refine ⟨K-2,?_⟩
  rw [Nat.sub_add_cancel hK]
  constructor
  · apply (le_div_iff₀ hKR).mpr
    have h := (le_div_iff₀ (show 0 < 4*s by positivity)).mp hUp
    linarith only [h]
  · have h := (div_le_iff₀ hd).mp hC
    exact (div_le_div_iff₀ hKR hκ).mpr (by linarith only [h])

/-- With those block counts, the cyclic contribution in (7.1) is
at most a quarter of the stage tolerance. The other quarter accounts
for the small-layout budgets and the ceilings. -/
theorem total_stage_reserve_charge {J : Type*} (S : Finset J)
    (κ s : ℝ) (n k : ℕ) (hκ : 0 < κ) (hk : 0 < k)
    (hRecip : 1/(k:ℝ) ≤ 8*s/κ) (m b cap : J → ℕ)
    (hSize : (∑ i ∈ S,(m i:ℝ)) ≤ (κ/64)*(n:ℝ))
    (hOverhead : (∑ i ∈ S, ((b i+2*cap i:ℕ):ℝ))+2*(S.card:ℝ) ≤ (s/4)*(n:ℝ)) :
    (∑ i ∈ S, ((b i+2*cap i+2*((m i+k-1)/k):ℕ):ℝ)) ≤ (s/2)*(n:ℝ) := by
  have hSum : 0 ≤ ∑ i ∈ S,(m i:ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hC : (∑ i ∈ S,(m i:ℝ))/(k:ℝ) ≤ (s/8)*(n:ℝ) := by
    calc
      _ = (1/(k:ℝ))*(∑ i ∈ S,(m i:ℝ)) := by ring
      _ ≤ (8*s/κ)*(∑ i ∈ S,(m i:ℝ)) := mul_le_mul_of_nonneg_right hRecip hSum
      _ ≤ (8*s/κ)*((κ/64)*(n:ℝ)) := by
        apply mul_le_mul_of_nonneg_left hSize
        exact (by positivity : 0 ≤ 1/(k:ℝ)).trans hRecip
      _ = _ := by field_simp; ring
  have h := sum_cyclic_reserve_cost_le S k hk m b cap
  linarith only [h,hC,hOverhead]

end OverfullWork.DirectedSpanningConfiguration
