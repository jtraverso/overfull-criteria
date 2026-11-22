module

public import OverfullWork.RobustSamplingConstants

@[expose] public section


/-! End-to-end robust vertex sampling from an arbitrary robust digraph.
The regularity source, equal two-sided cells and reduced robustness are
constructed internally. The retained robust parameter precedes c. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset UniformSubsetSampling
open scoped Classical
variable {V : Type*} [Fintype V]

theorem real_robust_mono (D : Digraph V) {ν ν' τ τ' : ℝ}
    (hν : ν' ≤ ν) (hτ : τ ≤ τ') (hR : IsRealRobust D ν τ) : IsRealRobust D ν' τ' := by
  intro S hLo hHi
  have hτn := mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  have hGrow := hR S (by linarith only [hLo,hτn]) (by nlinarith only [hHi,hτn])
  have hSub : realNeighbourhood D ν S ⊆ realNeighbourhood D ν' S := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _,(mul_le_mul_of_nonneg_right hν
      (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)).trans (mem_filter.mp hv).2⟩
  have hCount : ((realNeighbourhood D ν S).card:ℝ) ≤ ((realNeighbourhood D ν' S).card:ℝ) := by
    exact_mod_cast card_le_card hSub
  have hνn := mul_le_mul_of_nonneg_right hν (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  linarith only [hGrow,hCount,hνn]

def IsVertexSamplingRobust (D : Digraph V) (c p ν τ : ℝ) : Prop :=
  IsRealRobust D ν τ ∧ ∀ k : ℕ,k ≤ Fintype.card V → c*(Fintype.card V:ℝ) ≤ (k:ℝ) →
    probability k (fun X => ¬IsRealRobust (InducedDigraphSampling.induced D X) ν τ) ≤ p

end OverfullWork.DirectedRobustExpansion

namespace OverfullWork.BipartiteRegularitySource
open Finset DirectedRobustExpansion DirectedClusterQuotient UniformSubsetSampling
open scoped Classical
universe u
set_option maxHeartbeats 18000000

theorem robust_vertex_sampling (ν τ : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : 0 < τ) (hτSmall : τ ≤ 1/8) :
    ∃ ν' : ℝ,0 < ν' ∧ ν'=ν^6/(2:ℝ)^60 ∧ ∀ c : ℝ,0 < c → c ≤ 1 → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] (D : Digraph V),N ≤ Fintype.card V →
        IsRealRobust D ν τ → IsVertexSamplingRobust D c (1/(Fintype.card V:ℝ)^2) ν' (4*τ) := by
  let θ := ν/1024
  let d := θ^4/256
  let β := θ^4/256
  let δ := d/4
  let ρ := ν/2
  let ν' := δ*ρ^2/256
  have hν1 : ν ≤ 1 := by linarith only [hντ,hτSmall]
  have hθ : 0 < θ := by dsimp only [θ];positivity
  have hθ1 : θ ≤ 1 := by dsimp only [θ];linarith only [hν1]
  have hθSmall : θ ≤ 1/16 := by dsimp only [θ];linarith only [hν1]
  have hθν : θ ≤ ν/16 := by dsimp only [θ];linarith only [hν]
  have hd : 0 < d := by dsimp only [d];positivity
  have hβ : 0 < β := by dsimp only [β];positivity
  have hδ : 0 < δ := by dsimp only [δ];positivity
  have hθ2 : θ^2 ≤ 1 := (sq_le_one_iff₀ hθ.le).mpr hθ1
  have hθ4 : θ^4 ≤ 1 := by
    have hh := (sq_le_one_iff₀ (sq_nonneg θ)).mpr hθ2
    nlinarith only [hh]
  have hδ1 : δ ≤ 1 := by dsimp only [δ,d];linarith only [hθ4]
  have hρ : 0 < ρ := by dsimp only [ρ];positivity
  have hρ1 : ρ ≤ 1 := by dsimp only [ρ];linarith only [hν1]
  have hν' : 0 < ν' := by dsimp only [ν'];positivity
  have hν'ν : ν' ≤ ν := by
    have hνSquare : ν^2 ≤ ν := by nlinarith only [hν,hν1]
    have hδν := mul_le_mul_of_nonneg_right hδ1 (sq_nonneg ν)
    dsimp only [ν',ρ]
    nlinarith only [hνSquare,hδν,hν]
  refine ⟨ν',hν',?_,?_⟩
  · dsimp only [ν',δ,d,θ,ρ]
    norm_num
    ring
  intro c hc hc1
  obtain ⟨ε,hε,hεθ,hεBudget,hεc,hεSmall,hDensityMargin⟩ :=
    exists_sampling_regular_error ν c θ d hν hν1 hc hc1 hθ hθ1 hd
  have hBudget : 16*ε+2*β+16*d ≤ θ^4/2 := by
    have hPos : 0 ≤ θ^4 := by positivity
    dsimp only [β,d]
    linarith only [hεBudget,hPos]
  obtain ⟨K,N₀,hInitial⟩ := exists_initial_two_sided_robust_data.{u} ε d β θ ν τ
    hε hd.le hβ hθ hθSmall hθν hν hτ hεθ hBudget
  let K' := ⌈2*((K:ℝ)+1)/θ⌉₊
  let σ := θ/(2*((K:ℝ)+1))
  let η := min (ρ*c/(2048*((K':ℝ)+1))) (c*σ/8)
  have hσ : 0 < σ := by dsimp only [σ];positivity
  have hη : 0 < η := by dsimp only [η];positivity
  have hηK : η*(K':ℝ) ≤ ρ*c/1024 := by
    have hMin : η ≤ ρ*c/(2048*((K':ℝ)+1)) := min_le_left _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 2048*((K':ℝ)+1))).mp hMin
    have hPos : 0 < ρ*c := mul_pos hρ hc
    nlinarith only [hh,hη,hPos]
  have hηSmall : η ≤ c*σ/4 := by
    have hh : η ≤ c*σ/8 := min_le_right _ _
    have hPos : 0 < c*σ := mul_pos hc hσ
    linarith only [hh,hPos]
  have hRhoTau : ρ ≤ 2*τ := by dsimp only [ρ];linarith only [hντ,hτ]
  obtain ⟨N₁,hSample⟩ := TwoSidedClusterQuotient.exists_normalized_sampling_threshold.{u,0}
    K' ρ (2*τ) (12*ε/θ) (d-ε) δ c η σ hρ hρ1 (by positivity)
    (by linarith only [hτSmall]) hRhoTau hδ hδ1 hc hc1 hη hσ hηK hηSmall
    (by positivity) hεc hεSmall hDensityMargin
  refine ⟨max N₀ N₁,?_⟩
  intro V _ D hn hD
  obtain ⟨q,m,H,f,g,hLe,hm,hF,hG,hSame,hE,hProfile,hQ,hScale,hR,hPairs⟩ := hInitial D (by omega) hD
  refine ⟨real_robust_mono D hν'ν (by linarith only [hτ]) hD,?_⟩
  intro k hk hSize
  have hq : 0 < q := by
    by_contra hh
    have hz : q=0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero] at hScale
    norm_num at hScale
  have hQK : Fintype.card (Fin q) ≤ K' := by
    simp only [Fintype.card_fin]
    have hh : (q:ℝ) ≤ 2*((K:ℝ)+1)/θ := by
      apply (le_div_iff₀ hθ).mpr
      nlinarith only [hQ]
    have hFinal : (q:ℝ) ≤ (K':ℝ) := hh.trans (Nat.le_ceil _)
    exact_mod_cast hFinal
  have hCell : σ*(Fintype.card V:ℝ) ≤ (m:ℝ) := by
    rw [show σ*(Fintype.card V:ℝ)=θ*(Fintype.card V:ℝ)/(2*((K:ℝ)+1)) by dsimp only [σ];ring]
    apply (div_le_iff₀ (by positivity : 0 < 2*((K:ℝ)+1))).mpr
    have hmR : (0:ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith only [hProfile,hmR]
  have hException : ((exceptional f).card:ℝ) ≤ ρ*(Fintype.card V:ℝ)/128 := by
    have hh : 2*θ*(Fintype.card V:ℝ) ≤ ρ*(Fintype.card V:ℝ)/128 := by
      dsimp only [θ,ρ]
      have hPos : 0 ≤ ν*(Fintype.card V:ℝ) := by positivity
      linarith only [hPos]
    exact hE.trans hh
  have hTauQ : 8 ≤ (2*τ)*(Fintype.card (Fin q):ℝ) := by
    simp only [Fintype.card_fin]
    have hh := mul_le_mul_of_nonneg_right hντ (Nat.cast_nonneg q : (0:ℝ) ≤ q)
    linarith only [hScale,hh]
  have hResult := hSample D (TwoSidedClusterQuotient.quotient H f g) f g m k (by omega) hk hSize
    hm (by simpa only [Fintype.card_fin] using hq) hQK hF hG hCell hException hR hTauQ
    (fun i j hij => (hPairs i j hij).1) (fun i j hij => (hPairs i j hij).2)
  simpa only [ν',show 2*(2*τ)=4*τ by ring] using hResult

theorem robust_vertex_sampling_explicit (ν τ : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : 0 < τ) (hτSmall : τ ≤ 1/8) :
    ∀ c : ℝ,0 < c → c ≤ 1 → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] (D : Digraph V),N ≤ Fintype.card V →
        IsRealRobust D ν τ →
          IsVertexSamplingRobust D c (1/(Fintype.card V:ℝ)^2) (ν^6/(2:ℝ)^60) (4*τ) := by
  obtain ⟨ν',hPos,hEq,hSampling⟩ := robust_vertex_sampling.{u} ν τ hν hντ hτ hτSmall
  simpa only [hEq] using hSampling

end OverfullWork.BipartiteRegularitySource
