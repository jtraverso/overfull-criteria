module

public import OverfullWork.OsthusStadenBridgesFromPrimarySlices

@[expose] public section


/-! Unwind the prepared factors and construct their physical bridges
with the same global deletion and exceptional-incidence bounds. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u v

set_option maxHeartbeats 2800000 in
/-- The prepared primary factors yield all the refined slices with
their red geometry and bridge stars. The number of removed vertices
in each refinement and the number of omissions of any ordinary
vertex are carried forward for §5.6–§5.9. -/
theorem exists_osthus_staden_bridged_layers_from_primary_reserves
    (s p K L mMin : ℕ) (hs : 4 ≤ s) (hp : p.Prime) (hp₂ : 2 < p) [NeZero p] [NeZero (2*s)]
    (hK : 0 < K)
    (err loss ε εbase τ η δ γ β d₀ : ℝ)
    (hErr : 0 < err) (hErr₁ : err ≤ 1) (hLoss : 0 < loss) (hLoss₁ : loss ≤ 1/4)
    (hGood : 8*err ≤ loss) (hTrim : 4*(err+loss) ≤ ε) (hε₁ : ε ≤ 1)
    (hεbase : 0 < εbase) (hBaseSmall : εbase ≤ τ/4) (hτ : 0 < τ) (hτ₁ : τ ≤ 1/16)
    (hAdapt : 16*loss*(((2*s)*(p*2):ℕ):ℝ) ≤ τ^2/16)
    (hFloor : 4*τ ≤ (1-5*γ)*β-ε) (hη : max (2*ε) (ε+4*τ) ≤ η) (hη₁ : η ≤ 1)
    (hScale : (((2*s)*p:ℕ):ℝ)*ε ≤ η)
    (hδ : 2*η ≤ δ) (hδ₁ : δ ≤ 1)
    (hγ : 0 < γ) (hγ₁ : 5*γ ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1) (hd₀ : 0 < d₀)
    (hThin : 4*err ≤ γ*β) (hH0Err : 4*err*(((2*s)*(p*2):ℕ):ℝ) ≤ β)
    (hH0Trim : 8*loss ≤ γ*d₀) (hH0Floor : 32*τ ≤ γ*d₀) (hH0Degree : 32*β ≤ γ*d₀) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      {G H : Digraph V} {f : V → Option I} {m₀ r : ℕ} {a exc badBound : ℝ}
      (B : OsthusStadenPrimaryReserveData H f
        (reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β)
        m₀ ((2*s)*(p*2)) β γ err a exc)
      (σ : Fin r → Equiv.Perm I)
      (pick : Fin r → I → ReducedCopy
        (reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β))
      (C : Equiv.Perm I),
      N ≤ B.size → Fintype.card I ≤ K → r ≤ L → H ≤ G →
      exc ≤ 1/2 → B.MainCopyIncidenceBound badBound →
      (∀ i, ¬ (quotient H f).Adj i i) →
      (∀ i j, (quotient H f).Adj i j → d₀+β ≤ density H (cluster f i) (cluster f j)) →
      (∀ t i, (pick t i).1 = (i,σ t i)) →
      Function.Injective (fun q : Fin r × I => pick q.1 q.2) →
      (∀ i j, C.SameCycle i j) → (∀ i, (quotient H f).Adj i (C i)) →
      let J := RefinedFactorIndex r (2*s) p
      let d := (1-5*γ)*β
      ∃ mBase m : ℕ, mMin ≤ m ∧ 2 ≤ m ∧ m ≤ mBase ∧ B.size = (2*s)*(p*(2*mBase)) ∧
        B.size ≤ 2*((2*s)*(p*(2*m))) ∧
        ((B.size-(2*s)*(p*(2*m)):ℕ):ℝ) ≤ 2*loss*(B.size:ℝ) ∧
        ∃ g : Fin r → V → Option I, ∃ E : Fin r → I → Digraph V,
          (∀ t, ((exceptional (g t)).card:ℝ) ≤ (exc+2*loss)*(Fintype.card V:ℝ)) ∧
          (∀ t i, (cluster (g t) i).card = (2*s)*(p*(2*m)) ∧ cluster (g t) i ⊆ cluster B.partition i) ∧
          let capTypes := ⌈2*badBound+4*loss*(r:ℝ)+1⌉₊
          (∀ x, B.partition x ≠ none → ((univ : Finset (Fin r)).filter (fun t => g t x = none)).card ≤ capTypes) ∧
          let profiles := arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E)
          ∃ base : ∀ i, PrimaryNestedRefinement profiles (cluster B.partition i) (2*s) p mBase εbase εbase εbase,
          ∃ R : ∀ t i, PrimaryNestedRefinement profiles (cluster (g t) i) (2*s) p m τ τ τ,
          ∃ A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ η d R,
          ∃ D : PrimaryRedSelection (p := p) A.coordinates,
            let halfLoss := 4*(B.size-(2*s)*(p*(2*m)))
            let κ := ⌊(1-γ)*d*((2*m:ℕ):ℝ)⌋₊
            (∀ t u q, max (primaryHalfCell (R t) u q \ primaryHalfCell base u q).card
                (primaryHalfCell base u q \ primaryHalfCell (R t) u q).card ≤ halfLoss) ∧
            ∃ (src dst : J → I → RefinedVertex I (2*s) p) (erase : J → RefinedVertex I (2*s) p → V),
              let cells := fun (j : J) u => primaryPCells (R j.1) u
              let halfIn := fun (j : J) i =>
                primaryHalfCell (R j.1) ((A.factor j).symm (src j i)) (redPhase p j.1.val).2
              let halfOut := fun (j : J) i =>
                primaryHalfCell (R j.1) (dst j i) (redPhase p j.1.val).2
              (∀ j i, (src j i).1.1 = i ∧ (dst j i).1.1 = C i) ∧
              (∀ j i, D.selectedPCell false j ((A.factor j).symm (src j i)) ∧ D.selectedPCell true j (dst j i)) ∧
              Function.Injective (fun q : J × RefinedVertex I (2*s) p => erase q.1 q.2) ∧
              (∀ j u, erase j u ∈ cells j u ∧ erase j u ∈ primaryPCells base u) ∧
              ∃ P : TrimmedPhysicalBridgeLayers G (unwoundSlice E A.label A.factor) A.factor C
                cells erase src dst halfIn halfOut κ (2*m) δ d,
                P.UsesBridgeReserves (primaryThinDigraphs B 1) (primaryThinDigraphs B 0) := by
  let b := (2*s)*(p*2)
  let d := (1-5*γ)*β
  have hd : 0 ≤ d := mul_nonneg (by linarith only [hγ₁]) hβ.le
  have hd₁ : d ≤ 1 := (mul_le_of_le_one_left hβ.le (by linarith only [hγ])).trans hβ₁
  have hb : 0 < b := Nat.mul_pos (by omega) (Nat.mul_pos hp.pos (by decide))
  have hηPos : 0 < η := by
    have h := (le_max_right (2*ε) (ε+4*τ)).trans hη
    linarith only [h,hτ,hLoss,hErr,hTrim]
  have hδPos : 0 < δ := by linarith only [hδ,hηPos]
  obtain ⟨Amin,hAmin⟩ := exists_osthus_staden_slices_from_primary_factors_with_incidence_bound.{u,v}
    s p K L (by omega) hp hp₂ hK err loss ε εbase τ η d hErr hErr₁ hLoss hLoss₁ hGood hTrim hε₁
    hεbase hBaseSmall hτ (by linarith only [hτ₁]) hAdapt hFloor hη hη₁ hScale
  let maxLayers := L*((2*s-1)*(p-1))
  let mFloor := max mMin (max 2 (max (2*maxLayers) ⌈2/δ⌉₊))
  refine ⟨max Amin (2*(b*mFloor)),?_⟩
  intro V _ I _ G H f m₀ r a exc badBound B σ pick C hSize hI hr hHost hExc hBad hLoop hDen
    hPick hInj hCSpan hC J d'
  let Q := quotient H f
  let M := reducedMultiplicity Q (fun i j => density H (cluster f i) (cluster f j)) β
  have hLoopM (i : I) : M i i = 0 := if_neg (hLoop i)
  have hσ := primary_factor_successor_in_support Q _ β σ pick hPick
  let fillCap := max 1 ⌈4*loss*(r:ℝ)⌉₊
  have hFill : 0 < fillCap := Nat.zero_lt_one.trans_le (le_max_left _ _)
  have hFillLo : 4*loss*(r:ℝ) ≤ (fillCap:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈4*loss*(r:ℝ)⌉₊))
  have hFillHi : (fillCap:ℝ) ≤ 4*loss*(r:ℝ)+1 := by
    rw [show fillCap = _ from rfl,Nat.cast_max]
    exact max_le (by simp; positivity) (Nat.ceil_lt_add_one (by positivity)).le
  obtain ⟨mBase,m,hm,hMBase,hBaseEq,hHalf,hDrop,g,E,hExcept,hCells,hTypes,base,R,_,hNear,hHalfNear,⟨A⟩⟩ :=
    hAmin B σ pick ((le_max_left _ _).trans hSize) hI hr hHost hExc rfl hd hd₁ hPick hInj hLoopM
      fillCap badBound hFill hFillLo hBad
  have hM : mFloor ≤ m := by
    have h := ((le_max_right _ _).trans hSize).trans hHalf
    rw [show (2*s)*(p*(2*m)) = b*m by simp only [b,Nat.mul_assoc]] at h
    exact Nat.le_of_mul_le_mul_left (by omega : b*mFloor ≤ b*m) hb
  have hm₂ : 2 ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hMin : mMin ≤ m := (le_max_left _ _).trans hM
  have hMaxLayers : 2*maxLayers ≤ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hCeil : ⌈2/δ⌉₊ ≤ m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hM))
  have hκRoom : 2 ≤ δ*(m:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hδPos).mp ((Nat.le_ceil _).trans (by exact_mod_cast hCeil))
  have hRoom : η*((2*m:ℕ):ℝ)+1 ≤ δ*((2*m-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*m),Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat]
    have h := mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [h,hδ₁,hκRoom]
  let halfLoss := 4*(B.size-(2*s)*(p*(2*m)))
  have hHalfR : (B.size:ℝ) ≤ 2*((b:ℝ)*(m:ℝ)) := by
    exact_mod_cast (show B.size ≤ 2*(b*m) by simpa only [b,Nat.mul_assoc] using hHalf)
  have hAdapt' : 16*loss*(b:ℝ) ≤ 1/2 := by
    have hτSq : τ^2 ≤ 1 := by
      have hτ' : τ ≤ 1 := by linarith only [hτ₁]
      nlinarith only [mul_le_mul hτ' hτ' hτ.le (by norm_num : (0:ℝ) ≤ 1)]
    linarith only [hAdapt,hτSq]
  have hHalfSmall : 2*halfLoss ≤ m := by
    have h₁ := mul_le_mul_of_nonneg_left hHalfR (show 0 ≤ 16*loss by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hAdapt' (Nat.cast_nonneg (α := ℝ) m)
    have h₃ := mul_le_mul_of_nonneg_left hDrop (show (0:ℝ) ≤ 8 by norm_num)
    exact_mod_cast (show ((2*halfLoss:ℕ):ℝ) ≤ (m:ℝ) by
      simp only [halfLoss,Nat.cast_mul,Nat.cast_ofNat]
      nlinarith only [h₁,h₂,h₃])
  have hCapacity : Fintype.card J+halfLoss ≤ m := by
    have hJ : Fintype.card J ≤ maxLayers := by
      have hCard : Fintype.card J = r*((2*s-1)*(p-1)) :=
        (Fintype.card_congr (show J ≃ RefinedFactorIndex r (2*s) p from Equiv.refl _)).trans
          (card_refined_factor_index r (2*s) p)
      rw [hCard]
      exact Nat.mul_le_mul_right _ hr
    omega
  have hDel (t : Fin r) (i : I) :
      (((cluster B.partition i) \ cluster (g t) i).card:ℝ) ≤ γ*d₀*(B.size:ℝ)/4 := by
    have hBaseSize : (cluster B.partition i).card = B.size := by
      rw [←B.retained_cells i,card_map,card_univ,Fintype.card_fin]
    rw [card_sdiff_of_subset (hCells t i).2,hBaseSize,(hCells t i).1]
    exact hDrop.trans (by nlinarith only [mul_le_mul_of_nonneg_right hH0Trim (Nat.cast_nonneg (α := ℝ) B.size)])
  have hBadSize : 4*(err/β)*(B.size:ℝ) ≤ 2*(m:ℝ) := by
    have h₁ : 4*(err/β)*(b:ℝ) ≤ 1 := by
      calc
        _ = (4*err*(b:ℝ))/β := by ring
        _ ≤ 1 := (div_le_iff₀ hβ).mpr (by simpa only [one_mul] using hH0Err)
    have h₂ := mul_le_mul_of_nonneg_left hHalfR (show 0 ≤ 4*(err/β) by positivity)
    nlinarith only [h₂,mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg (α := ℝ) m)]
  have hNear' (t : Fin r) (u : RefinedVertex I (2*s) p) :
      ((primaryPCells (R t) u) \ primaryPCells base u).card ≤ halfLoss := by
    have h := (le_max_right _ _).trans
      (hNear t u.1.1 ((ZMod.finEquiv (2*s)).symm u.1.2) ((ZMod.finEquiv p).symm u.2))
    simpa only [primaryPCells,halfLoss,←hBaseEq] using h.trans
      (Nat.mul_le_mul_right _ (by decide : 3 ≤ 4))
  have hHalfNear' (t : Fin r) (u : RefinedVertex I (2*s) p) (q : Bool) :
      max (primaryHalfCell (R t) u q \ primaryHalfCell base u q).card
        (primaryHalfCell base u q \ primaryHalfCell (R t) u q).card ≤ halfLoss := by
    have h := hHalfNear t u.1.1 ((ZMod.finEquiv (2*s)).symm u.1.2) ((ZMod.finEquiv p).symm u.2)
      (if q then 1 else 0)
    rw [max_comm]
    simpa only [primaryHalfCell,halfLoss,hBaseEq] using h
  let κ := ⌊(1-γ)*d*((2*m:ℕ):ℝ)⌋₊
  have hκ : (κ:ℝ) < (1-8*τ)*(γ*d₀/4)*(m:ℝ) := by
    have hScale₀ : (1-γ)*d ≤ β := by
      exact (mul_le_of_le_one_left hd (by linarith only [hγ])).trans
        (mul_le_of_le_one_left hβ.le (by linarith only [hγ]))
    have hκUpper := Nat.floor_le (show 0 ≤ (1-γ)*d*((2*m:ℕ):ℝ) by
      exact mul_nonneg (mul_nonneg (by linarith only [hγ,hγ₁]) hd) (Nat.cast_nonneg _))
    have hκ₁ := mul_le_mul_of_nonneg_right hScale₀ (Nat.cast_nonneg (α := ℝ) (2*m))
    have hτ' : (1:ℝ)/2 ≤ 1-8*τ := by linarith only [hτ₁]
    have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
    have hPay := mul_le_mul_of_nonneg_right hτ' (show 0 ≤ (γ*d₀/4)*(m:ℝ) by positivity)
    have hβpay := mul_le_mul_of_nonneg_right hH0Degree hmR.le
    have hStrict : 0 < γ*d₀*(m:ℝ) := by positivity
    change (κ:ℝ) ≤ _ at hκUpper
    push_cast at hκUpper hκ₁
    nlinarith only [hκUpper,hκ₁,hPay,hβpay,hStrict]
  obtain ⟨D⟩ := exists_primary_red_selection A (by omega : 1 < p) (hp.odd_of_ne_two (by omega))
    (factor_has_no_fixed_points_of_loopless_multiplicity M σ pick hPick hLoopM)
  obtain ⟨src,dst,erase,hTags,hRed,_,hFresh,hErase,P,hRes⟩ :=
    exists_osthus_staden_bridged_primary_slices_with_reserves B E g σ τ η δ d εbase (err/β) d₀
      R base A D C κ halfLoss (by omega : 3 ≤ s) hHost hCSpan hC hσ hDen hβ hγ.le hErr hErr₁
      hd₀.le (by positivity) hThin (by rw [div_mul_cancel₀ _ hβ.ne'])
      (fun t i => (hCells t i).2) hDel hNear' hCapacity hBadSize hτ.le
      (by linarith only [hτ₁]) (by linarith only [hH0Floor]) hκ hd hd₁ hδ hδ₁ hRoom
  refine ⟨mBase,m,hMin,hm₂,hMBase,hBaseEq,hHalf,hDrop,g,E,hExcept,hCells,?_,
    base,R,A,D,hHalfNear',src,dst,erase,hTags,hRed,hFresh,hErase,P,hRes⟩
  intro x hx
  have hBound := (hTypes x hx).trans (show 2*badBound+(fillCap:ℝ) ≤
    2*badBound+4*loss*(r:ℝ)+1 by linarith only [hFillHi])
  exact_mod_cast hBound.trans (Nat.le_ceil (2*badBound+4*loss*(r:ℝ)+1))

end OverfullWork.DirectedRobustExpansion
