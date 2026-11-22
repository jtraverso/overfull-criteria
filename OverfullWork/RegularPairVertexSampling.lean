module

public import OverfullWork.UniformSamplingBudget
public import OverfullWork.RegularPairNeighbourhood

@[expose] public section


/-! Uniform fixed-size samples retain large pieces of prescribed cells,
and therefore inherit every supplied regular pair by slicing. No robust
reduced graph, directed regular partition or spanning layout is assumed
to have been constructed by these estimates. -/
namespace OverfullWork.RegularPairVertexSampling
open SimpleGraph Finset Real UniformSubsetSampling
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 18000000

theorem sampled_cell_large (X U : Finset V) (k : ℕ) (c σ : ℝ)
    (hc : 0 < c) (_hσ : 0 < σ) (hn : 0 < Fintype.card V)
    (hSize : c*(Fintype.card V:ℝ) ≤ (k:ℝ))
    (hU : σ*(Fintype.card V:ℝ) ≤ (U.card:ℝ))
    (hError : |((X ∩ U).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*(U.card:ℝ)| <
      (c*σ/4)*(Fintype.card V:ℝ)) :
    (c/2)*(U.card:ℝ) ≤ ((X ∩ U).card:ℝ) := by
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
  have hp : c ≤ (k:ℝ)/(Fintype.card V:ℝ) := (le_div_iff₀ hnR).mpr hSize
  have hExpected := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg U.card)
  have hCell := mul_le_mul_of_nonneg_left hU (show (0:ℝ) ≤ c/4 by positivity)
  have hLow := (abs_lt.mp hError).1
  have hPos := mul_nonneg hc.le (Nat.cast_nonneg U.card : (0:ℝ) ≤ U.card)
  nlinarith only [hExpected,hCell,hLow,hPos]

theorem uniform_on_sample (G : SimpleGraph V) [DecidableRel G.Adj]
    (X U W : Finset V) (c ε : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hε : 0 ≤ ε) (hεc : ε ≤ c/2) (hUniform : G.IsUniform ε U W)
    (hU : (c/2)*(U.card:ℝ) ≤ ((X ∩ U).card:ℝ))
    (hW : (c/2)*(W.card:ℝ) ≤ ((X ∩ W).card:ℝ)) :
    G.IsUniform (4*ε/c) (X ∩ U) (X ∩ W) := by
  have hCap : 2*ε ≤ 4*ε/c := by
    apply (le_div_iff₀ hc).mpr
    have hh := mul_le_mul_of_nonneg_left hc1 (show (0:ℝ) ≤ 2*ε by positivity)
    nlinarith only [hh,hε]
  have hScale : ∀ a b : ℝ,0 ≤ a → (c/2)*a ≤ b → a*ε ≤ b ∧ a*ε ≤ b*(4*ε/c) := by
    intro a b ha hab
    constructor
    · have hh := mul_le_mul_of_nonneg_right hεc ha
      nlinarith only [hh,hab]
    · have hh := mul_le_mul_of_nonneg_left hab (show (0:ℝ) ≤ 4*ε by positivity)
      have hNonneg := mul_nonneg hε (mul_nonneg hc.le ha)
      have hId : b*(4*ε/c)=(b*(4*ε))/c := by ring
      rw [hId]
      apply (le_div_iff₀ hc).mpr
      nlinarith only [hh,hNonneg]
  obtain ⟨hULarge,hUScale⟩ := hScale _ _ (Nat.cast_nonneg _) hU
  obtain ⟨hWLarge,hWScale⟩ := hScale _ _ (Nat.cast_nonneg _) hW
  exact RegularPairNeighbourhood.uniform_on_subcells G hUniform inter_subset_right inter_subset_right
    hULarge hWLarge hUScale hWScale hCap

end OverfullWork.RegularPairVertexSampling

namespace OverfullWork.RegularPairVertexSampling
open SimpleGraph Finset Real UniformSubsetSampling
open scoped Classical
universe u v
set_option maxHeartbeats 18000000

theorem exists_uniform_slicing_threshold (C c σ ε : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hc1 : c ≤ 1) (hσ : 0 < σ)
    (hε : 0 ≤ ε) (hεc : ε ≤ c/2) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      (G : SimpleGraph V) [DecidableRel G.Adj] (U : I → Finset V) (k : ℕ),
      N ≤ Fintype.card V → k ≤ Fintype.card V → c*(Fintype.card V:ℝ) ≤ (k:ℝ) →
      (Fintype.card I:ℝ) ≤ C*(Fintype.card V:ℝ) →
      (∀ i,σ*(Fintype.card V:ℝ) ≤ ((U i).card:ℝ)) →
      probability k (fun X => ∃ i j,G.IsUniform ε (U i) (U j) ∧
        ¬G.IsUniform (4*ε/c) (X ∩ U i) (X ∩ U j)) ≤ 1/(Fintype.card V:ℝ)^2 := by
  obtain ⟨N,hN⟩ := exists_uniform_profile_threshold.{u,v} C (c*σ/4) hC (by positivity)
  refine ⟨max N 2,?_⟩
  intro V _ I _ G _ U k hn hk hSize hI hCells
  have hTail := hN U k (by omega) hk hI
  apply (probability_mono k ?_).trans hTail
  intro X hBad
  by_contra hGood
  have hErrors : ∀ i,|((X ∩ U i).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*((U i).card:ℝ)| <
      (c*σ/4)*(Fintype.card V:ℝ) := by
    simpa only [not_exists,not_le] using hGood
  have hLarge : ∀ i,(c/2)*((U i).card:ℝ) ≤ ((X ∩ U i).card:ℝ) :=
    fun i => sampled_cell_large X (U i) k c σ hc hσ (by omega) hSize (hCells i) (hErrors i)
  obtain ⟨i,j,hUniform,hNot⟩ := hBad
  exact hNot (uniform_on_sample G X (U i) (U j) c ε hc hc1 hε hεc hUniform (hLarge i) (hLarge j))

end OverfullWork.RegularPairVertexSampling
