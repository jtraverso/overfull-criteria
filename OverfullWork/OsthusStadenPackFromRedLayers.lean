module

public import OverfullWork.OsthusStadenBalancingFromPrimarySizes
public import OverfullWork.OsthusStadenClosingScales

@[expose] public section


/-! The red graph, its physical H2 additions and the extracted
Hamilton cycles all use the same actual layers and bridge stars. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u v

set_option maxHeartbeats 2900000 in
/-- Balance all the red layers, then use the common extraction and
merging thresholds to obtain the Hamilton pack. -/
theorem exists_osthus_staden_hamilton_pack_from_red_layers
    (K s p mClose : ℕ) [NeZero (2*s)] [NeZero p] (hs : 2 ≤ s) (hp : 3 ≤ p)
    (β γ ν t₀ α thinErr shadowErr redRate rate redLimit δ : ℝ)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hγ : 0 < γ) (hγβ : γ*β ≤ 1/2)
    (hν : 0 < ν) (hντ : ν ≤ t₀) (hτ : t₀ ≤ 1/4) (hAlpha : 8*t₀ ≤ α)
    (hThin : 0 ≤ thinErr) (hThinSmall : (((2*s)*p:ℕ):ℝ)*thinErr ≤ γ*β/8)
    (hErr : 0 < shadowErr) (hErrSmall : 16*shadowErr ≤ ν^2/2)
    (hRed : 0 < redRate) (hRate : 0 < rate) (hLimit : 0 < redLimit)
    (hReuse : 128*rate ≤ β*(γ*β/4)) (hLoad : 32*rate ≤ redLimit) (hRedSmall : 4*redRate ≤ redLimit)
    (hShadow : 40*(p:ℝ)*redRate ≤ shadowErr*rate*(ν^2/2)^2)
    (fraction δ₃ dMerge εMerge νMerge τMerge γMerge : ℝ)
    (hFraction : 0 < fraction) (hFractionOne : fraction ≤ 1)
    (hδ : 0 ≤ δ) (hδ₃ : 0 < δ₃) (hδ₃One : δ₃ ≤ 1) (hδSplit : δ ≤ δ₃/4)
    (hνMerge : 0 < νMerge) (hWidth : εMerge+νMerge ≤ τMerge) (hεMerge : 0 < εMerge)
    (hτγ : 16*τMerge ≤ γMerge) (hγMerge : γMerge ≤ 1) (hMerge : 0 < dMerge)
    (hReg : δ₃ ≤ εMerge) (hDensity : dMerge ≤ fraction*((1-5*γ)*β)-2*δ₃)
    (hClose : ∀ m : ℕ, mClose ≤ m →
      let n := 2*m-1
      let d := (1-5*γ)*β
      let κ := ⌊(1-γ)*d*((2*m:ℕ):ℝ)⌋₊
      ∀ redCap : ℝ, 0 ≤ redCap → redCap ≤ redLimit*(m:ℝ) →
        ∃ cutoff minDemand batch : ℕ,
          redCap ≤ ((κ-minDemand:ℕ):ℝ) ∧
          OsthusStadenDenseFactorMargins n κ cutoff minDemand δ₃ ((1-fraction)*d) ∧
          κ ≤ (p-4)*batch ∧
          (batch:ℝ)+νMerge*(n:ℝ) ≤ dMerge*τMerge*(n:ℝ) ∧
          γMerge*(n:ℝ)+(batch:ℝ) ≤ dMerge*(n:ℝ)) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I] [Nonempty I]
      {r m mBase m₀ b : ℕ}
      {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ} {a exc : ℝ}
      (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ thinErr a exc)
      {E : Fin r → I → Digraph V} {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I}
      {τ εBase ε : ℝ}
      (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster B.partition i) (2*s) p mBase εBase εBase εBase)
      {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster (g t) i) (2*s) p m τ τ τ}
      (A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ ε ((1-5*γ)*β) R)
      (D : PrimaryRedSelection (p := p) A.coordinates)
      (Q : Digraph I) (hCopy : ∀ i k, Q.Adj i k → 0 < M i k) (hHost : H ≤ G)
      (hRobust : IsRealRobust Q ν t₀)
      (hIn : ∀ i, α*(Fintype.card I:ℝ) ≤ (inDegree Q i:ℝ))
      (hOut : ∀ i, α*(Fintype.card I:ℝ) ≤ (outDegree Q i:ℝ))
      (hOrder : 2 ≤ t₀*(Fintype.card I:ℝ)) (hCount : 8 ≤ α*(Fintype.card I:ℝ))
      (hI : Fintype.card I ≤ K) (hr : (r:ℝ) ≤ (Fintype.card I:ℝ)/β)
      (hBaseSize : B.size = (2*s)*(p*(2*mBase))) (hBase : mBase ≤ 2*m)
      (C : Equiv.Perm I)
      (src dst : RefinedFactorIndex r (2*s) p → I → RefinedVertex I (2*s) p)
      (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
      (hErase : ∀ j u, erase j u ∈ primaryPCells (R j.1) u)
      (halfLoss : ℕ)
      (hHalf : ∀ t u (q : Bool), (primaryHalfCell (R t) u q \ primaryHalfCell base u q).card ≤ halfLoss)
      (hHalfSize : halfLoss+1 ≤ m/4) (hm : N ≤ m)
      (hTags : ∀ j i, (src j i).1.1 = i ∧ (dst j i).1.1 = C i)
      (hDir : ∀ j i, D.selectedPCell false j ((A.factor j).symm (src j i)) ∧
        D.selectedPCell true j (dst j i)),
      let J := RefinedFactorIndex r (2*s) p
      let d := (1-5*γ)*β
      let original := fun (j : J) => primaryPCells (R j.1)
      let cell := fun j u => (original j u).erase (erase j u)
      let ordinary := fun j => univ.biUnion (cell j)
      let halfIn := fun (j : J) i =>
        primaryHalfCell (R j.1) ((A.factor j).symm (src j i)) (redPhase p j.1.val).2
      let halfOut := fun (j : J) i =>
        primaryHalfCell (R j.1) (dst j i) (redPhase p j.1.val).2
      let κ := ⌊(1-γ)*d*((2*m:ℕ):ℝ)⌋₊
      ∀ (bridge : TrimmedPhysicalBridgeLayers G (unwoundSlice E A.label A.factor) A.factor C
          original erase src dst halfIn halfOut κ (2*m) δ d)
        (F : J → Digraph V) (redCap : ℝ),
        OsthusStadenRedLayerProperties G (primaryThinDigraphs B 4) (unwoundSlice E A.label A.factor)
          F A.factor ordinary cell D.vertices (fun j i => erase j (src j i))
          bridge.incoming bridge.outgoing κ redCap δ d →
        0 ≤ redCap → redCap ≤ redRate*(m:ℝ) →
          ∃ Pack : Fin ((r*((2*s-1)*(p-1)))*κ) → Equiv.Perm V,
            (∀ i, HasSpanningCycle (fun x y => Pack i x = y)) ∧ (∀ i x, G.Adj x (Pack i x)) ∧
            ∀ i k, i ≠ k → ∀ x, Pack i x ≠ Pack k x := by
  obtain ⟨N₁,hN₁⟩ := exists_osthus_staden_balancing_from_primary_sizes.{u,v} K s p hs hp
    β γ ν t₀ α thinErr shadowErr redRate rate redLimit hβ hβ₁ hγ hγβ hν hντ hτ hAlpha hThin hThinSmall
    hErr hErrSmall hRed hRate hLimit hReuse hLoad hRedSmall hShadow
  obtain ⟨N₂,hN₂⟩ := exists_osthus_staden_hamilton_pack_from_balanced_layers.{v,u}
    fraction δ δ₃ dMerge εMerge νMerge τMerge γMerge hFraction hFractionOne hδ hδ₃ hδ₃One hδSplit
    hνMerge hWidth hεMerge hτγ hγMerge hMerge
  refine ⟨max mClose (max (max N₁ N₂) 2),?_⟩
  intro V _ I _ _ r m mBase m₀ b G H f M a exc B E g σ τ εBase ε base R A D Q hCopy hHost
    hRobust hIn hOut hOrder hCount hI hr hBaseSize hBase C src dst erase hErase halfLoss hHalf
    hHalfSize hm hTags hDir J d original cell ordinary halfIn halfOut κ bridge F redCap hRedLayer hCap hCapSize
  have hN : max (max N₁ N₂) 2 ≤ m := (le_max_right _ _).trans hm
  have hm₂ : 2 ≤ m := (le_max_right _ _).trans hN
  have hBal : N₁ ≤ m := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hPack : N₂ ≤ 2*m-1 := ((le_max_right _ _).trans ((le_max_left _ _).trans hN)).trans (by omega)
  obtain ⟨P,balancedCap,hBalCap,hCapUp,hP,hRanges,hBalanced⟩ :=
    hN₁ B base A D Q hCopy hHost hRobust hIn hOut hOrder hCount hI hr hBaseSize hBase erase hErase
      halfLoss hHalf hHalfSize hBal hRedLayer hCap hCapSize
  obtain ⟨cutoff,minDemand,batch,hBound,hDense,hBatch,hCost,hDegree⟩ :=
    hClose m ((le_max_left _ _).trans hm) balancedCap hBalCap hCapUp
  exact hN₂ base A D hp hs hm₂ C src dst erase κ cutoff minDemand batch F P (primaryThinDigraphs B 4)
    redCap balancedCap hPack hBound hDense hBatch hReg hDensity hCost hDegree hTags hDir hP hRanges
    bridge hRedLayer hBalanced

end OverfullWork.DirectedRobustExpansion
