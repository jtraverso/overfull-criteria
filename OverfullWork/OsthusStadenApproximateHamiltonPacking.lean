module

public import Mathlib.Data.Nat.Prime.Infinite
public import OverfullWork.KuhnOsthusExactOfApproximate
public import OverfullWork.OsthusStadenPrimaryHostWithCycle
public import OverfullWork.OsthusStadenBridgedLayersFromPrimaryReserves
public import OverfullWork.OsthusStadenRedLayersFromPrimarySizes
public import OverfullWork.OsthusStadenPackFromRedLayers
public import OverfullWork.OsthusStadenLowerScales
public import OverfullWork.OsthusStadenApproximatePackConclusion

@[expose] public section


/-! Assemble the successive constructions of Osthus–Staden §5
with one choice of parameters and one sufficiently large host. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u

set_option maxHeartbeats 6200000 in
/-- The existence of an approximate Hamilton decomposition in
Osthus–Staden Theorem 1.1. The parameters and order threshold are
independent of the choice of regular host. -/
theorem osthus_staden_theorem_1_1_existence : RobustApproximateHamiltonPacking.{u} := by
  intro α₀ hα₀
  let α := min α₀ 1
  have hα : 0 < α := lt_min hα₀ (by norm_num)
  have hα₁ : α ≤ 1 := min_le_right _ _
  let τ := α/128
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτα : 64*τ ≤ α := by dsimp only [τ]; linarith only [hα]
  have ht₀ : 2*τ ≤ 1/4 := by dsimp only [τ]; linarith only [hα₁]
  have ht₀α : 8*(2*τ) ≤ α/2 := by dsimp only [τ]; linarith only [hα]
  refine ⟨τ,hτ,?_⟩
  intro ν₀ η hν₀ hη
  let ν := min ν₀ τ
  have hν : 0 < ν := lt_min hν₀ hτ
  have hντ : ν ≤ τ := min_le_right _ _
  have hν₁ : ν ≤ 1 := by linarith only [hντ,ht₀]
  let μ := min (ν/16) (ν^2/32)
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hμν : μ ≤ ν/2 := by linarith only [(min_le_left _ _ : μ ≤ ν/16),hν]
  have hμτ : μ ≤ 2*τ := by linarith only [hμν,hντ,hτ]
  let dense := min (ν^2/32) (α/16)
  have hDense : 0 < dense := by dsimp only [dense]; positivity
  have hDenseν : 8*(μ+dense) ≤ ν^2 := by
    linarith only [(min_le_right _ _ : μ ≤ ν^2/32),(min_le_left _ _ : dense ≤ ν^2/32),sq_nonneg ν]
  have hDenseα : dense ≤ α/16 := min_le_right _ _
  let γ := min (dense*μ^2/12) (min (α/8) (min (η/60) (η*α/10)))
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  have hγDense : 12*γ ≤ dense*μ^2 := by linarith only [(min_le_left _ _ : γ ≤ dense*μ^2/12)]
  have hγSmall : γ ≤ α/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hγ₈ : γ ≤ 1/8 := by linarith only [hγSmall,hα₁]
  have hγ₅ : 5*γ < 1 := by linarith only [hγ₈]
  have hγLocal : 12*γ ≤ η/5 := by
    have h : γ ≤ η/60 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [h]
  have hγMain : γ ≤ (η/5)*α/2 := by
    have h : γ ≤ η*α/10 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith only [h]
  let d₀ := min (ν/16) (min (μ*γ/256) (α/128))
  have hd₀ : 0 < d₀ := by dsimp only [d₀]; positivity
  have hd₀ν : 2*d₀ ≤ ν/8 := by linarith only [(min_le_left _ _ : d₀ ≤ ν/16)]
  have hd₀Loss : d₀ ≤ μ*γ/256 := (min_le_right _ _).trans (min_le_left _ _)
  have hd₀α : d₀ ≤ α/128 := (min_le_right _ _).trans (min_le_right _ _)
  let β := min (d₀/2) (min (dense/2) (min (γ*d₀/32) (min (α/4) ((η/5)*α/2))))
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hβd : β ≤ d₀/2 := min_le_left _ _
  have hβDense : β ≤ dense/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hβDegree : 32*β ≤ γ*d₀ := by
    have h : β ≤ γ*d₀/32 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [h]
  have hβSmall : β ≤ α/4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hβ₁ : β ≤ 1 := by linarith only [hβSmall,hα₁]
  have hβMain : β ≤ (η/5)*α/2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hPrimaryLoss : 3*(2*d₀)+β ≤ (μ/16)*γ/2 := by nlinarith only [hd₀Loss,hβd,mul_pos hμ hγ]
  have hPrimaryDegree : 3*(2*d₀)+dense ≤ α/2 := by linarith only [hd₀α,hDenseα,hα]
  have hCopyDegree : 3*(2*d₀)+β ≤ α/8 := by linarith only [hd₀α,hβd,hα]
  have hγβ : γ*β ≤ 1/2 := by
    have h := mul_le_mul hγ₈ hβ₁ hβ.le (by norm_num : (0:ℝ) ≤ 1/8)
    linarith only [h]
  let d := (1-5*γ)*β
  have hd : 0 < d := mul_pos (by linarith only [hγ₅]) hβ
  have hd₁ : d ≤ 1 := (mul_le_of_le_one_left hβ.le (by linarith only [hγ])).trans hβ₁
  obtain ⟨pMin,mClose,fraction,δ₃,dMerge,εMerge,νMerge,τMerge,γMerge,redLimit,
    hFraction,hFractionOne,hδ₃,hδ₃One,hMerge,hεMerge,hνMerge,hWidth,hτγ,hγMerge,hMergeReg,
    hMergeDensity,hLimit,hClose⟩ := exists_osthus_staden_closing_scales γ d hγ hγ₈ hd hd₁
  have he : 0 < η/5 := by positivity
  obtain ⟨p,hPMin,hPrime⟩ := Nat.exists_infinite_primes (max 3 (max pMin ⌈1/(η/5)⌉₊))
  have hp : 3 ≤ p := (le_max_left _ _).trans hPMin
  have hpClose : pMin ≤ p := (le_max_left _ _).trans ((le_max_right _ _).trans hPMin)
  have hPCeil : ⌈1/(η/5)⌉₊ ≤ p := (le_max_right _ _).trans ((le_max_right _ _).trans hPMin)
  have hP : 1 ≤ (η/5)*(p:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ he).mp ((Nat.le_ceil _).trans (by exact_mod_cast hPCeil))
  let s := max 4 (max ⌈1/(γ/8)⌉₊ ⌈1/(η/5)⌉₊)
  have hs : 4 ≤ s := le_max_left _ _
  have hSCeil₁ : ⌈1/(γ/8)⌉₊ ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hSCeil₂ : ⌈1/(η/5)⌉₊ ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have hDirections : 1 ≤ (γ/8)*(s:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ (by positivity : 0 < γ/8)).mp ((Nat.le_ceil _).trans (by exact_mod_cast hSCeil₁))
  have hS : 1 ≤ (η/5)*((2*s:ℕ):ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ he).mp ((Nat.le_ceil _).trans (by exact_mod_cast (show ⌈1/(η/5)⌉₊ ≤ 2*s by omega)))
  letI : NeZero p := ⟨by omega⟩
  letI : NeZero (2*s) := ⟨by omega⟩
  let δ := δ₃/4
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ₁ : δ ≤ 1 := by dsimp only [δ]; linarith only [hδ₃One]
  let shadowErr := μ^2/64
  have hShadowErr : 0 < shadowErr := by dsimp only [shadowErr]; positivity
  have hShadowSmall : 16*shadowErr ≤ μ^2/2 := by dsimp only [shadowErr]; linarith only [sq_nonneg μ]
  obtain ⟨rate,redRate,hRate,hRed,hReuse,hLoad,hRedSmall,hShadow⟩ :=
    exists_osthus_staden_balancing_rates p β μ shadowErr (γ*β/4) redLimit hβ hμ hShadowErr (by positivity) hLimit
  obtain ⟨τAdapt,εAdapt,εBase,excLimit,ξ,loss,err,hτAdapt,hτAdapt₁,hH0Floor,
    hεAdapt,hεAdapt₁,hFloor,hηAdapt,hScaleAdapt,hηAdapt₁,hεBase,hBaseSmall,hExcLimit,
    hξ,hξ₁,hBad,hSupply,hLoss,hLoss₁,hAdapt,hH0Trim,hClip,hFill,hSpecialCap,hH1Lower,hH1Upper,
    hErr,hErr₁,hGood,hTrim,hThin,hH0Err,hThinSmall,hExcMargins⟩ :=
    exists_osthus_staden_lower_scales s p α β γ d₀ δ (η/5) redRate
      hs hp hα hβ hγ hγ₅ hd₀ hδ hδ₁ he hRed
  let b := (2*s)*(p*2)
  have hb : 0 < b := Nat.mul_pos (by omega) (Nat.mul_pos hPrime.pos (by decide))
  let kMin := max 1 (max ⌈(2*(p:ℝ))*β/γ⌉₊ ⌈β/ξ⌉₊)
  have hkMin : 1 ≤ kMin := le_max_left _ _
  have hkSlack : ⌈(2*(p:ℝ))*β/γ⌉₊ ≤ kMin := (le_max_left _ _).trans (le_max_right _ _)
  have hkScale : ⌈β/ξ⌉₊ ≤ kMin := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨exc,K,hExc,hExcLe,hExcSmall,hK,hHost⟩ :=
    exists_osthus_staden_primary_host_with_cycle.{u} ν τ α dense μ (2*d₀) β γ ξ err excLimit kMin b
      hν hν₁ hτ hα hα₁ hμ hμν hμτ hτα hDense hDenseν (by positivity) hd₀ν hβ
      (by linarith only [hβd]) hβDense hγ hγDense hPrimaryLoss hPrimaryDegree hCopyDegree
      hξ hξ₁ hBad hErr hErr₁ (by linarith only [hThin,hErr]) hExcLimit hb
  obtain ⟨hExcSize,hFinalLoss,hExceptional,hCoreCap⟩ := hExcMargins exc hExc.le hExcLe
  obtain ⟨hostRed,cellRed,hRedLayers⟩ := exists_osthus_staden_red_layers_from_primary_sizes.{u,u}
    K s p α β γ ξ loss exc εBase redRate hs hp (hPrime.odd_of_ne_two (by omega))
    hα hα₁ hβ hβSmall hγ (by linarith only [hγSmall,hα]) hγ₅.le hξ hLoss
    hExc.le hεBase.le hRed hExcSize hDirections hExceptional hCoreCap
    (by simpa only [Nat.mul_assoc] using hClip) hFill hSupply hSpecialCap
    (by simpa only [Nat.mul_assoc] using hH1Lower) (by simpa only [Nat.mul_assoc] using hH1Upper)
  obtain ⟨cellPack,hPack⟩ := exists_osthus_staden_hamilton_pack_from_red_layers.{u,u}
    K s p mClose (by omega) hp β γ μ (2*τ) (α/2) err shadowErr redRate rate redLimit δ
    hβ hβ₁ hγ hγβ hμ hμτ ht₀ ht₀α hErr.le hThinSmall hShadowErr hShadowSmall hRed
    hRate hLimit hReuse hLoad hRedSmall hShadow fraction δ₃ dMerge εMerge νMerge τMerge γMerge
    hFraction hFractionOne hδ.le hδ₃ hδ₃One le_rfl hνMerge hWidth hεMerge hτγ hγMerge hMerge
    hMergeReg hMergeDensity (fun m hm => hClose p m hpClose hm)
  obtain ⟨cellCount,hCount⟩ := osthus_staden_approximate_conclusion_from_refined_pack.{u,u}
    α β γ η s p kMin hα hβ hη hγMain hγLocal
    (hβMain.trans (by
      have h := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ (kMin:ℝ) by exact_mod_cast hkMin)
        (mul_nonneg he.le hα.le)
      nlinarith only [h])) hS hP
  let cellMin := max cellRed (max cellPack cellCount)
  let L := ⌈(K:ℝ)/β⌉₊
  obtain ⟨sizeMin,hBridges⟩ := exists_osthus_staden_bridged_layers_from_primary_reserves.{u,u}
    s p K L cellMin hs hPrime (by omega) hK err loss εAdapt εBase τAdapt (δ/2) δ γ β d₀
    hErr hErr₁ hLoss hLoss₁ hGood hTrim hεAdapt₁ hεBase hBaseSmall hτAdapt hτAdapt₁ hAdapt
    hFloor hηAdapt hηAdapt₁ hScaleAdapt (by ring_nf; exact le_rfl) hδ₁ hγ hγ₅.le
    hβ hβ₁ hd₀ hThin hH0Err hH0Trim hH0Floor hβDegree
  obtain ⟨hostMin,hHostAtSize⟩ := hHost sizeMin
  refine ⟨max 1 (max hostRed hostMin),?_⟩
  intro V _ G r hN hDegree hRob hReg _hLoop
  have hNpos : 0 < Fintype.card V := Nat.zero_lt_one.trans_le ((le_max_left _ _).trans hN)
  letI : Nonempty V := Fintype.card_pos_iff.mp hNpos
  have hNR : 0 < (Fintype.card V:ℝ) := by exact_mod_cast hNpos
  let a := (r:ℝ)/(Fintype.card V:ℝ)
  have ha : α ≤ a := (le_div_iff₀ hNR).mpr
    ((mul_le_mul_of_nonneg_right (min_le_left _ _) hNR.le).trans hDegree)
  have ha₁ : a ≤ 1 := by
    apply (div_le_iff₀ hNR).mpr
    rw [one_mul]
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    have h : r ≤ Fintype.card V := (hReg v).2 ▸ DirectedArcSelection.outDegree_le G v
    exact_mod_cast h
  have hr : (r:ℝ) = a*(Fintype.card V:ℝ) := (div_mul_cancel₀ _ hNR.ne').symm
  have hRob' : IsRealRobust G ν τ := real_robust_mono G (min_le_left _ _) le_rfl hRob
  obtain ⟨I,inst,f,H,m₀,hIKmin,hIpos,hIK,hHG,hOrder,hCountI,hLoopQ,hDen,hRobS,hIn,hOut,hCopy,
    _hLoopM,hkPos,hkL,C,B,F,pick,hCycle,_hCS,hCQ,hSize,hBadB,hPick,_hArcF,hInject⟩ :=
    hHostAtSize G r a ((le_max_right _ _).trans ((le_max_right _ _).trans hN)) ha ha₁ hr hRob' hReg
  letI := inst
  letI : Nonempty I := Fintype.card_pos_iff.mp hIpos
  let k := ⌊(a-γ)*(Fintype.card I:ℝ)/β⌋₊
  have hSlack : (2*(p:ℝ))*β ≤ γ*(Fintype.card I:ℝ) := by
    rw [mul_comm γ]
    exact (div_le_iff₀ hγ).mp ((Nat.le_ceil _).trans (by exact_mod_cast hkSlack.trans hIKmin))
  have hScale : 1 ≤ ξ*(Fintype.card I:ℝ)/β := by
    apply (le_div_iff₀ hβ).mpr
    rw [one_mul,mul_comm ξ]
    exact (div_le_iff₀ hξ).mp ((Nat.le_ceil _).trans (by exact_mod_cast hkScale.trans hIKmin))
  have hkReal : (k:ℝ) ≤ (Fintype.card I:ℝ)/β := by
    have hγa : γ ≤ a := by linarith only [hγSmall,hα,ha]
    exact (Nat.floor_le (div_nonneg (mul_nonneg (sub_nonneg.mpr hγa) (Nat.cast_nonneg _)) hβ.le)).trans
      (div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith only [ha₁,hγ])) hβ.le)
  obtain ⟨mBase,m,hm,_hm₂,hmBase,hBaseEq,hSizeUpper,hDrop,g,E,hExcept,hCluster,hTypes,base,R,A,D,
    hHalf,src,dst,erase,hTags,hDir,hFresh,hErase,P,hRes⟩ :=
    hBridges B F pick C hSize hIK hkL hHG (by linarith only [hExcSmall]) hBadB hLoopQ
      (fun i j hij => by simpa only [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hDen i j hij)
      hPick hInject hCycle hCQ
  have hmRed : cellRed ≤ m := (le_max_left _ _).trans hm
  have hmPack : cellPack ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hmCount : cellCount ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hmBaseUpper : mBase ≤ 2*m := by
    apply Nat.le_of_mul_le_mul_left _ hb
    calc
      b*mBase = B.size := by simpa only [b,Nat.mul_assoc] using hBaseEq.symm
      _ ≤ 2*((2*s)*(p*(2*m))) := hSizeUpper
      _ = b*(2*m) := by dsimp only [b]; ac_rfl
  obtain ⟨hHalfSize,red,redCap,hRedCap,hRedCapRate,hRedProps⟩ :=
    hRedLayers B base A D C erase src dst ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
      hmRed hHG hkPos hIpos hIK ha ha₁ hr hReg rfl hSlack hScale hmBase hBaseEq hSizeUpper
      hDrop hExcept hCluster (fun j u => (hErase j u).1) hFresh hDir hTypes
      (fun t u q => (le_max_right _ _).trans (hHalf t u q)) P hRes
  obtain ⟨Pack,hPackCycles,hPackArc,hPackDis⟩ :=
    hPack B base A D (denseReduced H f dense) hCopy hHG hRobS hIn hOut hOrder hCountI
      hIK hkReal hBaseEq hmBaseUpper C src dst erase (fun j u => (hErase j u).1) _
      (fun t u q => (le_max_left _ _).trans (hHalf t u q)) hHalfSize hmPack hTags hDir
      P red redCap hRedProps hRedCap hRedCapRate
  let t₀ : Fin k := ⟨0,hkPos⟩
  have hκ : ⌊(1-γ)*d*((2*m:ℕ):ℝ)⌋₊ = ⌊(1-γ)*(1-5*γ)*β*((2*m:ℕ):ℝ)⌋₊ := by
    apply congrArg (fun x : ℝ => ⌊x⌋₊)
    dsimp only [d]
    ring
  exact hCount G (g t₀) m r k _ a hmCount hIKmin ha hr.symm rfl hκ
    (fun i => (hCluster t₀ i).1)
    ((hExcept t₀).trans (mul_le_mul_of_nonneg_right hFinalLoss hNR.le)) Pack hPackCycles hPackArc hPackDis

/-- The exact directed Hamilton decomposition used by CMS §5. -/
theorem kuhn_osthus_directed_decomposition (α : ℝ) (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ ν : ℝ, 0 < ν → ∃ N : ℕ, ∀ {V : Type u} [Fintype V]
        (G : Digraph V) (r : ℕ), N ≤ Fintype.card V →
        α*(Fintype.card V:ℝ) ≤ (r:ℝ) → IsRealRobust G ν τ →
        (∀ v, outDegree G v = r ∧ inDegree G v = r) → (∀ v, ¬ G.Adj v v) →
        Nonempty (DirectedHamiltonDecomposition G r) :=
  kuhn_osthus_directed_decomposition_of_approximate osthus_staden_theorem_1_1_existence α hα

/-- CMS Theorem 5.5, Hamilton decomposition of regular robust expanders
of even degree. -/
theorem cms_theorem_5_5 (α : ℝ) (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
        N ≤ Fintype.card V → α*(Fintype.card V:ℝ) ≤ 2*(k:ℝ) → RobustExpansion.IsRealRobust G ν τ →
        (∀ v, G.degree v = 2*k) → Nonempty (HamiltonDecomposition G k) :=
  cms_theorem_5_5_of_approximate osthus_staden_theorem_1_1_existence α hα

end OverfullWork.DirectedRobustExpansion
