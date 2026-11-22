module

public import OverfullWork.RegularPairVertexSampling
public import OverfullWork.InducedRegularPairs

@[expose] public section


/-! Directed slicing under uniform vertex sampling. Directions are
preserved, and the density loss is recorded together with regularity. -/
namespace OverfullWork.DirectedRegularPairs
open Finset Real UniformSubsetSampling
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 18000000

theorem sample_scales (c ε : ℝ) (hc : 0 < c) (hε : 0 ≤ ε) (hεc : ε ≤ c/2)
    (a b : ℝ) (ha : 0 ≤ a) (hab : (c/2)*a ≤ b) :
    a*ε ≤ b ∧ a*ε ≤ b*(4*ε/c) := by
  constructor
  · have hh := mul_le_mul_of_nonneg_right hεc ha
    nlinarith only [hh,hab]
  · have hh := mul_le_mul_of_nonneg_left hab (show (0:ℝ) ≤ 4*ε by positivity)
    have hNonneg := mul_nonneg hε (mul_nonneg hc.le ha)
    have hId : b*(4*ε/c)=(b*(4*ε))/c := by ring
    rw [hId]
    apply (le_div_iff₀ hc).mpr
    nlinarith only [hh,hNonneg]

theorem regular_pair_on_sample (D : Digraph V) (X U W : Finset V) (c ε d : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 ≤ ε) (hεc : ε ≤ c/2)
    (hUniform : IsUniform D ε U W) (hDensity : d ≤ density D U W)
    (hU : (c/2)*(U.card:ℝ) ≤ ((X ∩ U).card:ℝ))
    (hW : (c/2)*(W.card:ℝ) ≤ ((X ∩ W).card:ℝ)) :
    IsUniform D (4*ε/c) (X ∩ U) (X ∩ W) ∧ d-ε ≤ density D (X ∩ U) (X ∩ W) := by
  have hCap : 2*ε ≤ 4*ε/c := by
    apply (le_div_iff₀ hc).mpr
    have hh := mul_le_mul_of_nonneg_left hc1 (show (0:ℝ) ≤ 2*ε by positivity)
    nlinarith only [hh,hε]
  obtain ⟨hULarge,hUScale⟩ := sample_scales c ε hc hε hεc _ _ (Nat.cast_nonneg _) hU
  obtain ⟨hWLarge,hWScale⟩ := sample_scales c ε hc hε hεc _ _ (Nat.cast_nonneg _) hW
  exact ⟨uniform_on_subcells D hUniform inter_subset_right inter_subset_right
      hULarge hWLarge hUScale hWScale hCap,
    (density_on_subcells D hUniform hDensity inter_subset_right inter_subset_right hULarge hWLarge).le⟩

end OverfullWork.DirectedRegularPairs

namespace OverfullWork.DirectedRegularPairs
open Finset Real UniformSubsetSampling
open scoped Classical
universe u v
set_option maxHeartbeats 18000000

theorem exists_uniform_slicing_threshold (C c σ ε d : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hc1 : c ≤ 1) (hσ : 0 < σ)
    (hε : 0 ≤ ε) (hεc : ε ≤ c/2) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      (D : Digraph V) (U : I → Finset V) (k : ℕ),
      N ≤ Fintype.card V → k ≤ Fintype.card V → c*(Fintype.card V:ℝ) ≤ (k:ℝ) →
      (Fintype.card I:ℝ) ≤ C*(Fintype.card V:ℝ) →
      (∀ i,σ*(Fintype.card V:ℝ) ≤ ((U i).card:ℝ)) →
      probability k (fun X => ∃ i j,IsUniform D ε (U i) (U j) ∧ d ≤ density D (U i) (U j) ∧
        ¬(IsUniform D (4*ε/c) (X ∩ U i) (X ∩ U j) ∧ d-ε ≤ density D (X ∩ U i) (X ∩ U j)))
        ≤ 1/(Fintype.card V:ℝ)^2 := by
  obtain ⟨N,hN⟩ := exists_uniform_profile_threshold.{u,v} C (c*σ/4) hC (by positivity)
  refine ⟨max N 2,?_⟩
  intro V _ I _ D U k hn hk hSize hI hCells
  have hTail := hN U k (by omega) hk hI
  apply (probability_mono k ?_).trans hTail
  intro X hBad
  by_contra hGood
  have hErrors : ∀ i,|((X ∩ U i).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*((U i).card:ℝ)| <
      (c*σ/4)*(Fintype.card V:ℝ) := by
    simpa only [not_exists,not_le] using hGood
  have hLarge : ∀ i,(c/2)*((U i).card:ℝ) ≤ ((X ∩ U i).card:ℝ) :=
    fun i => RegularPairVertexSampling.sampled_cell_large X (U i) k c σ hc hσ (by omega)
      hSize (hCells i) (hErrors i)
  obtain ⟨i,j,hUniform,hDensity,hNot⟩ := hBad
  exact hNot (regular_pair_on_sample D X (U i) (U j) c ε d hc hc1 hε hεc
    hUniform hDensity (hLarge i) (hLarge j))

end OverfullWork.DirectedRegularPairs
