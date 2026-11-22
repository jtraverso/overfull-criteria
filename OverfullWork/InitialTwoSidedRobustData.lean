module

public import OverfullWork.TwoSidedParentPairs
public import OverfullWork.QuantitativePureRegularization

@[expose] public section


/-! Initial regular directed data constructed from an arbitrary robust
host, using separate source and target partitions of the same order.
No regular partition or robust reduced graph is an existence premise. -/
namespace OverfullWork.BipartiteRegularitySource
open Finset Finpartition DirectedClusterQuotient DirectedRobustExpansion DirectedDegreeTrimming
open scoped Classical
universe u
set_option maxHeartbeats 18000000

theorem exists_initial_two_sided_robust_data (ε d β θ ν τ : ℝ)
    (hε : 0 < ε) (hd : 0 ≤ d) (hβ : 0 < β) (hθ : 0 < θ)
    (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/16) (hν : 0 < ν) (hτ : 0 < τ)
    (hεθ : ε ≤ θ/6) (hBudget : 16*ε+2*β+16*d ≤ θ^4/2) :
    ∃ K N : ℕ,∀ {V : Type u} [Fintype V] (D : Digraph V),
      N ≤ Fintype.card V → IsRealRobust D ν τ →
      ∃ (k m : ℕ) (H : Digraph V) (f g : V → Option (Fin k)),
        H ≤ D ∧ 0 < m ∧ (∀ i,(cluster f i).card=m) ∧ (∀ i,(cluster g i).card=m) ∧
        (exceptional f).card=(exceptional g).card ∧
        ((exceptional f).card:ℝ) ≤ 2*θ*(Fintype.card V:ℝ) ∧
        θ*(Fintype.card V:ℝ) ≤ 2*(m:ℝ)*(K:ℝ) ∧ θ*(k:ℝ) ≤ 2*(K:ℝ) ∧
        4 ≤ ν*(k:ℝ) ∧
        IsRealRobust (TwoSidedClusterQuotient.quotient H f g) (ν/2) (2*τ) ∧
        (∀ i j,(TwoSidedClusterQuotient.quotient H f g).Adj i j →
          DirectedRegularPairs.IsUniform D (12*ε/θ) (cluster f i) (cluster g j) ∧
            d-ε ≤ DirectedRegularPairs.density D (cluster f i) (cluster g j)) := by
  let l := max 1 ⌈4/ν⌉₊
  obtain ⟨K,N₀,hSource⟩ := exists_general_initial_source ε d β hε hd hβ l
  refine ⟨K,max N₀ (max ⌈4*(K:ℝ)/θ⌉₊ ⌈2/τ⌉₊),?_⟩
  intro V _ D hn hD
  obtain ⟨P,H,hLe,hEqui,hUniform,hLow,hHigh,hH,hTotal⟩ := hSource D (by omega)
  have hp : 0 < P.parts.card := by have hh := le_max_left 1 ⌈4/ν⌉₊;omega
  have hK : 0 < K := lt_of_lt_of_le hp hHigh
  have hScaleK : 4*(K:ℝ) ≤ θ*(Fintype.card V:ℝ) := by
    have hh : 4*(K:ℝ)/θ ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈4*(K:ℝ)/θ⌉₊ ≤ Fintype.card V by omega))
    have hPaid := (div_le_iff₀ hθ).mp hh
    nlinarith only [hPaid]
  have hScaleP : 4*(P.parts.card:ℝ) ≤ θ*(Fintype.card V:ℝ) := by
    have hh : (P.parts.card:ℝ) ≤ (K:ℝ) := by exact_mod_cast hHigh
    linarith only [hh,hScaleK]
  have hnPos : 0 < Fintype.card V := by
    by_contra hh
    have hz : Fintype.card V=0 := by omega
    have hKR : (0:ℝ) < K := by exact_mod_cast hK
    simp only [hz,Nat.cast_zero,mul_zero] at hScaleK
    linarith only [hScaleK,hKR]
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hnPos
  have hLarge : 1 ≤ θ*(Fintype.card V:ℝ) := by
    have hKR : (1:ℝ) ≤ K := by exact_mod_cast hK
    linarith only [hScaleK,hKR]
  let L := ⌈θ^2*(Fintype.card V:ℝ)⌉₊
  let X := bad (D\H) L
  let m := ⌊θ*(Fintype.card V:ℝ)/(P.parts.card:ℝ)⌋₊
  have hTotalSmall : (total (D\H):ℝ) ≤ θ^4*(Fintype.card V:ℝ)^2/2 := by
    have hh := mul_le_mul_of_nonneg_right hBudget (sq_nonneg (Fintype.card V:ℝ))
    nlinarith only [hTotal,hh]
  obtain ⟨_,_,_,hThreshold,hL⟩ := floor_ceil_regularization_choices (Fintype.card V) 1 0 θ hθ
    (by linarith only [hθSmall]) hLarge (by omega)
  have hX := bad_fraction_of_total D H L θ hnPos hθ hTotalSmall hThreshold
  obtain ⟨hm,hMLo,hMHi,hMParent⟩ := rounded_chunk_scale (Fintype.card V) P.parts.card θ hp hθ
    (by linarith only [hθSmall]) hScaleP
  obtain ⟨k,π,σ,f,g,hF,hG,hFP,hGP,hFX,hGX,hSame,hExc⟩ := exists_aligned_punctured_cells P X m hm
  have hExcSmall : ((exceptional f).card:ℝ) ≤ 2*θ*(Fintype.card V:ℝ) := by
    have hCast : ((exceptional f).card:ℝ) ≤ (X.card:ℝ)+(P.parts.card:ℝ)*((m-1:ℕ):ℝ) := by exact_mod_cast hExc
    have hRem : P.parts.card*(m-1) ≤ m*P.parts.card := by nlinarith only [Nat.sub_le m 1]
    have hRemR : (P.parts.card:ℝ)*((m-1:ℕ):ℝ) ≤ (m:ℝ)*(P.parts.card:ℝ) := by exact_mod_cast hRem
    have hθSquare : θ^2 ≤ θ := by nlinarith only [hθ,hθSmall]
    have hSquareN := mul_le_mul_of_nonneg_right hθSquare hnR.le
    nlinarith only [hCast,hX,hRemR,hMHi,hSquareN]
  have hOrderN := order_eq f m hF
  simp only [Fintype.card_fin] at hOrderN
  have hOrderR : (Fintype.card V:ℝ)=((exceptional f).card:ℝ)+(m:ℝ)*(k:ℝ) := by exact_mod_cast hOrderN
  have hPK : (P.parts.card:ℝ) ≤ (K:ℝ) := by exact_mod_cast hHigh
  have hProfile : θ*(Fintype.card V:ℝ) ≤ 2*(m:ℝ)*(K:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hPK (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    nlinarith only [hMLo,hh]
  have hMK : (m:ℝ)*(k:ℝ) ≤ (Fintype.card V:ℝ) := by nlinarith only [hOrderR,(show (0:ℝ) ≤ ((exceptional f).card:ℝ) from Nat.cast_nonneg _)]
  have hUpperK : θ*(k:ℝ) ≤ 2*(K:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hMLo (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    have hh' := mul_le_mul_of_nonneg_right hMK (Nat.cast_nonneg P.parts.card : (0:ℝ) ≤ _)
    have hPKn := mul_le_mul_of_nonneg_right hPK hnR.le
    apply (mul_le_mul_iff_right₀ hnR).mp
    nlinarith only [hh,hh',hPKn]
  have hLowerK : P.parts.card ≤ k := by
    have hEquation := congrArg (fun z : ℝ => z*(P.parts.card:ℝ)) hOrderR
    have hEPart := mul_le_mul_of_nonneg_right hExcSmall (Nat.cast_nonneg P.parts.card : (0:ℝ) ≤ _)
    have hMPart := mul_le_mul_of_nonneg_right hMHi (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    have hCompare : (P.parts.card:ℝ) ≤ 2*θ*(P.parts.card:ℝ)+θ*(k:ℝ) := by
      apply (mul_le_mul_iff_right₀ hnR).mp
      nlinarith only [hEquation,hEPart,hMPart]
    by_contra hh
    have hKP : (k:ℝ) ≤ (P.parts.card:ℝ) := by exact_mod_cast (by omega : k ≤ P.parts.card)
    have hScaled := mul_le_mul_of_nonneg_left hKP hθ.le
    have hSmall := mul_le_mul_of_nonneg_right hθSmall (Nat.cast_nonneg P.parts.card : (0:ℝ) ≤ _)
    have hpR : (0:ℝ) < P.parts.card := by exact_mod_cast hp
    nlinarith only [hCompare,hScaled,hSmall,hpR]
  have hNuK : 4 ≤ ν*(k:ℝ) := by
    have h₀ : 4/ν ≤ (k:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right 1 ⌈4/ν⌉₊).trans (hLow.trans hLowerK))
    have hh := (div_le_iff₀ hν).mp h₀
    nlinarith only [hh]
  have hOrderLarge : 2 ≤ τ*(Fintype.card V:ℝ) := by
    have hh : 2/τ ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈2/τ⌉₊ ≤ Fintype.card V by omega))
    have hPaid := (div_le_iff₀ hτ).mp hh
    nlinarith only [hPaid]
  have hEg : ((exceptional g).card:ℝ)=((exceptional f).card:ℝ) := by exact_mod_cast hSame.symm
  have hException : ((exceptional g).card:ℝ) ≤ (Fintype.card V:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right hθSmall hnR.le
    linarith only [hEg,hExcSmall,hh]
  have hLoss : ((exceptional g).card:ℝ)+(L:ℝ) ≤ ν*(Fintype.card V:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right hθν hnR.le
    linarith only [hEg,hExcSmall,hL,hh]
  have hNuScale : 4 ≤ ν*(Fintype.card (Fin k):ℝ) := by simpa only [Fintype.card_fin] using hNuK
  obtain ⟨hPaid,hInterval⟩ := RobustClusterQuotient.paper_scale_budgets g m L hG ν τ hν hτ
    hNuScale hOrderLarge hException hLoss
  have hReduced := TwoSidedClusterQuotient.real_robust_from_host D H hLe f g m L hm hF hG ν τ
    hν hτ hD (fun v hv => (loss_outside_bad (D\H) L v (hGX v hv)).1) hPaid hInterval
  refine ⟨k,m,H,f,g,hLe,hm,hF,hG,hSame,hExcSmall,hProfile,hUpperK,hNuK,hReduced,?_⟩
  intro i j hij
  have hArc : (TwoSidedClusterQuotient.quotient
      (crossDigraph ((DirectedBipartiteEncoding.graph D).regularityReduced P ε d)) f g).Adj i j := by
    simpa only [hH] using hij
  exact two_sided_pair_from_parents D P f g π σ m ε d θ hF hG hFP hGP
    (fun U => parent_chunk_scale P hEqui θ hθ (by linarith only [hθSmall]) hp hScaleP U)
    hθ (by linarith only [hθSmall]) hε.le hεθ i j hArc

end OverfullWork.BipartiteRegularitySource
