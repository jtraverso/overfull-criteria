module

public import OverfullWork.OsthusStadenRedLayersFromBridges
public import OverfullWork.OsthusStadenRedBudgetsFromSizes
public import OverfullWork.OsthusStadenSpecialPopulationFromPrimaryLoss

@[expose] public section


/-! Construct the red layers on actual bridged slices with one common
order threshold and the red cap required by the balancing theorem. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u v

set_option maxHeartbeats 3400000 in
/-- The primary size estimates pay the core and special budgets
simultaneously. Both splitting tolerances and the order threshold
are chosen before the numbers of factors and exceptional requests. -/
theorem exists_osthus_staden_red_layers_from_primary_sizes
    (Kmax s p : ℕ) [NeZero (2*s)] [NeZero p]
    (α β γ ξ loss exc εBase redRate : ℝ)
    (hs : 4 ≤ s) (hp : 3 ≤ p) (hpOdd : Odd p)
    (hα : 0 < α) (hα₁ : α ≤ 1)
    (hβ : 0 < β) (hβSmall : β ≤ α/4) (hγ : 0 < γ) (hγSmall : γ ≤ α/4)
    (hγ₁ : 5*γ ≤ 1) (hξ : 0 < ξ) (hLoss : 0 < loss) (hExc : 0 ≤ exc)
    (hε : 0 ≤ εBase) (hRed : 0 < redRate) (hExcSize : exc+2*loss ≤ 1/2)
    (hDirections : 1 ≤ (γ/8)*(s:ℝ)) (hExceptional : exc+8*εBase ≤ (γ/8)*α)
    (hCoreCap : 288*exc*β*(p:ℝ) ≤ α*(redRate/4))
    (hClip : 288*loss*((((2*s)*p*2):ℕ):ℝ) ≤ (γ/8)*α)
    (hFill : 4*loss ≤ ξ) (hSupply : 320*(p:ℝ)*ξ ≤ γ*α)
    (hSpecialCap : 2*(3*loss)*β ≤ ξ*(redRate/16))
    (hH1Lower : (s:ℝ)*(8*εBase/((((2*s)*p*2):ℕ):ℝ)+9*loss) ≤ γ*α/(180*(p:ℝ)))
    (hH1Upper : (s:ℝ)*(8*εBase) ≤ γ*α/(3*(p:ℝ))) :
    ∃ hostMin cellMin : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      {r m₀ b mBase m degree : ℕ} {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
      {η a : ℝ} (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc)
      {E : Fin r → I → Digraph V} {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I}
      {τ ε δ : ℝ}
      (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster B.partition i) (2*s) p mBase εBase εBase εBase)
      {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster (g t) i) (2*s) p m τ τ τ}
      (A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ ε ((1-5*γ)*β) R)
      (D : PrimaryRedSelection (p := p) A.coordinates) (C : Equiv.Perm I)
      (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
      (src dst : RefinedFactorIndex r (2*s) p → I → RefinedVertex I (2*s) p),
      hostMin ≤ Fintype.card V → cellMin ≤ m →
      H ≤ G → 0 < r → 0 < Fintype.card I → Fintype.card I ≤ Kmax →
      α ≤ a → a ≤ 1 → (degree:ℝ) = a*(Fintype.card V:ℝ) →
      (∀ x, inDegree G x = degree ∧ outDegree G x = degree) →
      r = ⌊(a-γ)*(Fintype.card I:ℝ)/β⌋₊ →
      (2*(p:ℝ))*β ≤ γ*(Fintype.card I:ℝ) → 1 ≤ ξ*(Fintype.card I:ℝ)/β →
      m ≤ mBase → B.size = (2*s)*(p*(2*mBase)) → B.size ≤ 2*((2*s)*(p*(2*m))) →
      ((B.size-(2*s)*(p*(2*m)):ℕ):ℝ) ≤ 2*loss*(B.size:ℝ) →
      (∀ t, ((exceptional (g t)).card:ℝ) ≤ (exc+2*loss)*(Fintype.card V:ℝ)) →
      (∀ t i, (cluster (g t) i).card = (2*s)*(p*(2*m)) ∧ cluster (g t) i ⊆ cluster B.partition i) →
      (∀ j u, erase j u ∈ primaryPCells (R j.1) u) →
      Function.Injective (fun q : RefinedFactorIndex r (2*s) p × RefinedVertex I (2*s) p => erase q.1 q.2) →
      (∀ j i, D.selectedPCell false j ((A.factor j).symm (src j i)) ∧ D.selectedPCell true j (dst j i)) →
      let capTypes := ⌈2*(2*ξ*(Fintype.card I:ℝ)/β)+4*loss*(r:ℝ)+1⌉₊
      (∀ x, B.partition x ≠ none → ((univ : Finset (Fin r)).filter (fun t => g t x = none)).card ≤ capTypes) →
      let halfLoss := 4*(B.size-(2*s)*(p*(2*m)))
      (∀ t u q, (primaryHalfCell base u q \ primaryHalfCell (R t) u q).card ≤ halfLoss) →
      let d := (1-5*γ)*β
      let κ := ⌊(1-γ)*d*((2*m:ℕ):ℝ)⌋₊
      let cell := fun (j : RefinedFactorIndex r (2*s) p) => primaryPCells (R j.1)
      let trim := fun j u => (cell j u).erase (erase j u)
      let ordinary := fun j => univ.biUnion (trim j)
      let halfIn := fun (j : RefinedFactorIndex r (2*s) p) i =>
        primaryHalfCell (R j.1) ((A.factor j).symm (src j i)) (redPhase p j.1.val).2
      let halfOut := fun (j : RefinedFactorIndex r (2*s) p) i =>
        primaryHalfCell (R j.1) (dst j i) (redPhase p j.1.val).2
      ∀ (P : TrimmedPhysicalBridgeLayers G (unwoundSlice E A.label A.factor) A.factor C
          cell erase src dst halfIn halfOut κ (2*m) δ d),
        P.UsesBridgeReserves (primaryThinDigraphs B 1) (primaryThinDigraphs B 0) →
        halfLoss+1 ≤ m/4 ∧ ∃ (F : RefinedFactorIndex r (2*s) p → Digraph V) (redCap : ℝ),
          0 ≤ redCap ∧ redCap ≤ redRate*(m:ℝ) ∧
          OsthusStadenRedLayerProperties G (primaryThinDigraphs B 4) (unwoundSlice E A.label A.factor)
            F A.factor ordinary trim D.vertices (fun j i => erase j (src j i))
            P.incoming P.outgoing κ redCap δ d := by
  obtain ⟨splitCore,splitSpecial,hSplitCore,hSplitSpecial,N,hN⟩ :=
    exists_osthus_staden_red_budgets_from_sizes Kmax s p α β γ ξ loss exc εBase redRate
      hs hp hα hα₁ hβ hβSmall hγ hγSmall hγ₁ hξ hLoss hExc hε hRed hDirections hExceptional hCoreCap
      hClip hFill hSupply hSpecialCap hH1Lower hH1Upper
  let L := ⌈(Kmax:ℝ)/β⌉₊
  let bound := ⌈2*(2*ξ*(Kmax:ℝ)/β)+4*loss*(L:ℝ)+1⌉₊
  let Ind := Fin (L+1) × Fin (bound+1)
  choose need hNeed using fun i : Ind =>
    exists_osthus_staden_red_layers_from_bridges.{u,v} i.1.val s p i.2.val hs hp hpOdd
      splitCore splitSpecial hSplitCore hSplitSpecial
  refine ⟨(univ : Finset Ind).sup need,N,?_⟩
  intro V _ I _ r m₀ b mBase m degree G H f M η a B E g σ τ ε δ base R A D C erase src dst
    hSize hm hHost hRpos hIpos hI ha ha₁ hDegree hReg hr hSlack hScale hBase hBaseSize hSizeUpper hDrop hExcept
    hCells hErase hFresh hRedShape capTypes hTypes halfLoss hNear d κ cell trim ordinary halfIn halfOut P hRes
  let K := Fintype.card I
  let n := Fintype.card V
  let Z := exceptional B.partition
  have hR : (r:ℝ) ≤ (K:ℝ)/β := by
    have hγa : γ ≤ a := by linarith only [hγSmall,hα,ha]
    rw [hr]
    exact (Nat.floor_le (div_nonneg (mul_nonneg (sub_nonneg.mpr hγa) (Nat.cast_nonneg _)) hβ.le)).trans
      (div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith only [ha₁,hγ])) hβ.le)
  have hRmax : r ≤ L := by
    have h := hR.trans (div_le_div_of_nonneg_right (show (K:ℝ) ≤ (Kmax:ℝ) by exact_mod_cast hI) hβ.le)
    exact_mod_cast h.trans (Nat.le_ceil ((Kmax:ℝ)/β))
  have hTypesMax : capTypes ≤ bound := by
    apply Nat.ceil_mono
    have h₁ : (K:ℝ) ≤ (Kmax:ℝ) := by exact_mod_cast hI
    have h₂ : (r:ℝ) ≤ (L:ℝ) := by exact_mod_cast hRmax
    have hFirst := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2*ξ by positivity)) hβ.le
    have hSecond := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 4*loss by positivity)
    linarith only [hFirst,hSecond]
  let id : Ind := (⟨r,by omega⟩,⟨capTypes,by omega⟩)
  have hApply : need id ≤ n := (Finset.le_sup (f := need) (mem_univ _)).trans hSize
  let ell := ((2*s)*p*2:ℕ)
  let volume := (((2*s)*p*K:ℕ):ℝ)
  have hOriginal (i : I) : (cluster B.partition i).card = B.size := by
    rw [←B.retained_cells i,card_map,card_univ,Fintype.card_fin]
  have hBaseEq : B.size = ell*mBase := by rw [hBaseSize]; simp only [ell,Nat.mul_assoc]
  have hOrdEq : (2*s)*(p*(2*m)) = ell*m := by simp only [ell,Nat.mul_assoc]
  have hMlo : ell*m ≤ B.size := hBaseEq ▸ Nat.mul_le_mul_left _ hBase
  have hMhi : B.size ≤ 2*(ell*m) := hOrdEq ▸ hSizeUpper
  have hOrder : n = Z.card+B.size*K := order_eq B.partition B.size hOriginal
  have hVol : (K:ℝ)*(B.size:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (show K*B.size ≤ n by rw [Nat.mul_comm]; omega)
  let t₀ : Fin r := ⟨0,hRpos⟩
  have hPart : (n:ℝ) = ((exceptional (g t₀)).card:ℝ) + volume*((2*m:ℕ):ℝ) := by
    have h := order_eq (g t₀) _ (fun i => (hCells t₀ i).1)
    have h' : (n:ℝ) = ((exceptional (g t₀)).card:ℝ)+((((2*s)*(p*(2*m))):ℕ):ℝ)*(K:ℝ) := by exact_mod_cast h
    dsimp only [volume]
    push_cast at h' ⊢
    linarith only [h']
  have hOrd : volume*((2*m:ℕ):ℝ) ≤ (n:ℝ) := by
    linarith only [hPart,Nat.cast_nonneg (α := ℝ) (exceptional (g t₀)).card]
  have hSize₂ : (n:ℝ) ≤ 2*(volume*((2*m:ℕ):ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hExcSize (Nat.cast_nonneg (α := ℝ) n)
    linarith only [hPart,hExcept t₀,h]
  have hHalfLoss : (halfLoss:ℝ) ≤ 8*loss*(B.size:ℝ) := by
    dsimp only [halfLoss]
    rw [Nat.cast_mul,Nat.cast_ofNat]
    linarith only [hDrop]
  obtain ⟨hSpecialPop,hHalfSmall,hCoreDegree,hH1Lo,hH1Hi,hSpecialDegree,hSpecialLoad,hLoad⟩ :=
    hN r K m n B.size Z.card halfLoss a hm hIpos hI ha ha₁ hr hSlack hScale B.exceptional_le
      hOrd hSize₂ hMlo hMhi hVol hHalfLoss
  have hκEq : κ = ⌊(1-γ)*(1-5*γ)*β*((2*m:ℕ):ℝ)⌋₊ := by
    dsimp only [κ,d]
    congr 1
    ring
  rw [←hκEq] at hCoreDegree hSpecialDegree
  have hSmall : 8*εBase ≤ 1/9 := by
    have h := mul_le_of_le_one_right (show 0 ≤ γ/8 by positivity) hα₁
    linarith only [h,hExceptional,hExc,hγ₁]
  have hHalf (t : Fin r) (i : PrimaryHalfIndex I (2*s) p) :
      ((primaryHalfOfIndex base i) \ primaryHalfOfIndex (R t) i).card ≤ halfLoss := hNear t _ _
  have hSpecialLoad' (j : RefinedFactorIndex r (2*s) p) :
      ((specialExceptions Z cell erase (bridgeCenters erase src) j).card:ℝ) /
          ((capTypes*((2*s-1)*(p-1))+1:ℕ):ℝ)+splitSpecial*(n:ℝ) ≤ (redRate/4)*(m:ℝ) := by
    apply hSpecialLoad
    have h := special_population_bound_from_primary_loss A B.partition B.size (2*loss) loss
      hOriginal hCells hDrop (by positivity) hSpecialPop erase (bridgeCenters erase src) j
    change _ ≤ _ at h
    linarith only [h]
  have hCoreDegree' : (κ:ℝ) ≤ ((s-1:ℕ):ℝ)*(1-8*εBase)*
      ((degree:ℝ)-(Z.card:ℝ)-(8*εBase)*((K:ℝ)*((ell*mBase:ℕ):ℝ))) /
        ((ell:ℝ)*(exceptionalPhaseBankSize r (2*s) p:ℝ)) -
      (K:ℝ)*((s-1:ℕ):ℝ)*(splitCore*(n:ℝ)+((halfLoss+1:ℕ):ℝ)/(exceptionalPhaseBankSize r (2*s) p:ℝ)) := by
    rw [hDegree,←hBaseEq]
    exact hCoreDegree
  have hDeg : ∀ x, B.partition x = none → (degree:ℝ) ≤ inDegree G x ∧ (degree:ℝ) ≤ outDegree G x :=
    fun x _ => by rw [(hReg x).1,(hReg x).2]; exact ⟨le_rfl,le_rfl⟩
  obtain ⟨F,hF⟩ := hNeed id B base R A D C erase src dst κ halfLoss (degree:ℝ) ((redRate/4)*(m:ℝ))
    hApply hHost (fun t i => (hCells t i).2) hErase hFresh hRedShape hTypes hε hSmall hHalf hDeg
    hCoreDegree' hH1Lo hH1Hi hSpecialDegree hSpecialLoad' P hRes
  exact ⟨hHalfSmall,F,_,by positivity,hLoad,hF⟩

end OverfullWork.DirectedRobustExpansion
