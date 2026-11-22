module

public import OverfullWork.OsthusStadenBalancingBudgetsUniform
public import OverfullWork.OsthusStadenBalancingOnPhysicalLayers

@[expose] public section


/-! Apply the uniform integer estimates to the actual red cells and
the copies of H2 attached to the same regular host. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u v

/-- The incoming and outgoing red labels have two disjoint fibres of
size (s-1) over every primary label. -/
theorem PrimaryRedSelection.card_all_red_cells {I : Type*} [Fintype I] {r s p : ℕ} [NeZero (2*s)]
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)}
    (D : PrimaryRedSelection (p := p) C) (j : RefinedFactorIndex r (2*s) p) :
    letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
    Fintype.card ↥(D.allPCells true j ∪ D.allPCells false j) = Fintype.card I*(2*(s-1)) := by
  letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
  have hDis : Disjoint (D.allPCells true j) (D.allPCells false j) := disjoint_left.mpr fun z hz hz' =>
    D.pCell_unique_direction j z ⟨(D.mem_allPCells_iff true j z).mp hz,
      (D.mem_allPCells_iff false j z).mp hz'⟩
  have hCard (q : Bool) : (D.allPCells q j).card = Fintype.card I*(s-1) := by
    rw [card_eq_sum_card_fiberwise (f := fun x => x.1.1) (t := (univ : Finset I)) (fun _ _ => mem_univ _)]
    simp [D.allPCells_fibre,D.pCells_card]
  rw [Fintype.card_coe,card_union_of_disjoint hDis,hCard true,hCard false,two_mul,Nat.mul_add]

set_option maxHeartbeats 2700000 in
/-- All balancing arcs can be installed in H2 when the actual
exceptional load is at most the rate paid by the upper scales. Only a
bound on the primary cluster count is needed to fix the cell threshold. -/
theorem exists_osthus_staden_balancing_from_primary_sizes
    (K s p : ℕ) [NeZero (2*s)] [NeZero p] (hs : 2 ≤ s) (hp : 3 ≤ p)
    (β γ ν t₀ α thinErr shadowErr redRate rate redLimit : ℝ)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hγ : 0 < γ) (hγβ : γ*β ≤ 1/2)
    (hν : 0 < ν) (hντ : ν ≤ t₀) (hτ : t₀ ≤ 1/4) (hAlpha : 8*t₀ ≤ α)
    (hThin : 0 ≤ thinErr) (hThinSmall : (((2*s)*p:ℕ):ℝ)*thinErr ≤ γ*β/8)
    (hErr : 0 < shadowErr) (hErrSmall : 16*shadowErr ≤ ν^2/2)
    (hRed : 0 < redRate) (hRate : 0 < rate) (hLimit : 0 < redLimit)
    (hReuse : 128*rate ≤ β*(γ*β/4)) (hLoad : 32*rate ≤ redLimit) (hRedSmall : 4*redRate ≤ redLimit)
    (hShadow : 40*(p:ℝ)*redRate ≤ shadowErr*rate*(ν^2/2)^2) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      {r m mBase m₀ b : ℕ}
      {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ} {a exc : ℝ}
      (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ thinErr a exc)
      {E : Fin r → I → Digraph V} {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I}
      {τ εBase ε δ d : ℝ}
      (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster B.partition i) (2*s) p mBase εBase εBase εBase)
      {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster (g t) i) (2*s) p m τ τ τ}
      (A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ ε d R)
      (D : PrimaryRedSelection (p := p) A.coordinates)
      (Q : Digraph I) (hCopy : ∀ i k, Q.Adj i k → 0 < M i k) (hHost : H ≤ G)
      (hRobust : IsRealRobust Q ν t₀)
      (hIn : ∀ i, α*(Fintype.card I:ℝ) ≤ (inDegree Q i:ℝ))
      (hOut : ∀ i, α*(Fintype.card I:ℝ) ≤ (outDegree Q i:ℝ))
      (hOrder : 2 ≤ t₀*(Fintype.card I:ℝ)) (hCount : 8 ≤ α*(Fintype.card I:ℝ))
      (hI : Fintype.card I ≤ K) (hr : (r:ℝ) ≤ (Fintype.card I:ℝ)/β)
      (hBaseSize : B.size = (2*s)*(p*(2*mBase))) (hBase : mBase ≤ 2*m)
      (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
      (hErase : ∀ j u, erase j u ∈ primaryPCells (R j.1) u)
      (halfLoss : ℕ)
      (hHalf : ∀ t u (q : Bool), (primaryHalfCell (R t) u q \ primaryHalfCell base u q).card ≤ halfLoss)
      (hHalfSize : halfLoss+1 ≤ m/4) (hSize : N ≤ m),
      letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
      let L := RefinedFactorIndex r (2*s) p
      let U := RefinedVertex I (2*s) p
      let cell := fun (j : L) (u : U) => (primaryPCells (R j.1) u).erase (erase j u)
      let ordinary := fun j => univ.biUnion (cell j)
      let eligible := fun (j : L) (u : U) =>
        balancingHalfCell base (R j.1) (erase j) u (redPhase p j.1.val).2
      let label := fun (j : L) => trimPCellLabel (A.label j.1) (erase j)
      let incoming := D.allPCells true
      let outgoing := D.allPCells false
      let send := fun (j : L) => shadowSend (A.factor j) (incoming j) (outgoing j)
      let receive := fun (j : L) => shadowReceive (A.factor j) (incoming j) (outgoing j)
      ∀ {F : L → Digraph V} {κ : ℕ} {redCap : ℝ}
        {center : L → I → V} {IStar OStar : L → I → Finset V},
        OsthusStadenRedLayerProperties G (primaryThinDigraphs B 4) (unwoundSlice E A.label A.factor)
          F A.factor ordinary cell D.vertices center IStar OStar κ redCap δ d →
        0 ≤ redCap → redCap ≤ redRate*(m:ℝ) →
        ∃ (P : L → Finset (V × V)) (balancedCap : ℝ),
          0 ≤ balancedCap ∧
          balancedCap ≤ redLimit*(m:ℝ) ∧
          (∀ j e, e ∈ P j → ∃ x y, e.1 ∈ eligible j x ∧ e.2 ∈ eligible j y ∧
            x ∈ Set.range (send j) ∧ y ∈ Set.range (receive j)) ∧
          (∀ j, Disjoint (Set.range (send j)) (Set.range (receive j))) ∧
          OsthusStadenBalancedLayerProperties G (fun j => F j ⊔ digraphOfArcs (P j))
            (fun j => trimLayerArcs (F j) (ordinary j))
            (fun j => physicalExceptionalArcs (F j) (ordinary j) ∪ P j)
            ordinary cell label A.factor κ balancedCap δ d := by
  let densityMargin := γ*β/4
  let εH2 := γ*β/8
  let dH2 := 3*γ*β/8
  have hDensity : 0 < densityMargin := by dsimp only [densityMargin]; positivity
  obtain ⟨N,hN⟩ := exists_osthus_staden_uniform_balancing_budgets (K*(2*s)*p) p
    β ν shadowErr densityMargin redRate rate redLimit hβ hβ₁ hν hErr hDensity hRed hRate hLimit
    hReuse hLoad hRedSmall hShadow
  refine ⟨max N 8,?_⟩
  intro V _ I _ r m mBase m₀ b G H f M a exc B E g σ τ εBase ε δ d base R A D Q hCopy hHost hRobust
    hIn hOut hOrder hCount hI hr hBaseSize hBase erase hErase halfLoss hHalf hHalfSize hSize
  letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
  intro L U cell ordinary eligible label incoming outgoing send receive F κ redCap center IStar OStar hRedLayer hCap hCapSize
  have hIpos : 0 < Fintype.card I := by
    by_contra! h
    norm_num [Nat.eq_zero_of_le_zero h] at hCount
  have hU : Fintype.card U = Fintype.card I*(2*s)*p := by simp [U,RefinedVertex,ZMod.card]
  have hL : Fintype.card L = r*((2*s-1)*(p-1)) :=
    (Fintype.card_congr (show L ≃ RefinedFactorIndex r (2*s) p from Equiv.refl _)).trans
      (card_refined_factor_index r (2*s) p)
  have hUR : 0 < Fintype.card U := by rw [hU]; exact Nat.mul_pos (Nat.mul_pos hIpos (by omega)) (by omega)
  have hUK : Fintype.card U ≤ K*(2*s)*p := by rw [hU]; gcongr
  let shadow := Fintype.card I*(2*(s-1))
  have hSpos : 0 < shadow := Nat.mul_pos hIpos (by omega)
  have hURShadow : Fintype.card U ≤ 2*p*shadow := by
    rw [hU]
    calc
      _ ≤ Fintype.card I*(2*(2*(s-1)))*p := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by dsimp only [shadow]; ring
  have hFactor : (Fintype.card L:ℝ) ≤ (Fintype.card U:ℝ)/β := by
    rw [hU,hL,Nat.cast_mul r]
    have hCoeff : (((2*s-1)*(p-1):ℕ):ℝ) ≤ (((2*s)*p:ℕ):ℝ) :=
      by exact_mod_cast Nat.mul_le_mul (Nat.sub_le (2*s) 1) (Nat.sub_le p 1)
    calc
      _ ≤ ((Fintype.card I:ℝ)/β)*(((2*s)*p:ℕ):ℝ) :=
        mul_le_mul hr hCoeff (Nat.cast_nonneg _) (by positivity)
      _ = _ := by push_cast; ring
  obtain ⟨c,bound,cap,loss,cutoff,used,hDemandRate,hShadowCap,hCutPos,hCutoff,hCapPos,hDemand,
    hKeep,hPrev,hSlack,hNeed,hLoad'⟩ :=
    hN m (Fintype.card U) shadow (Fintype.card L) halfLoss redCap ((le_max_left _ _).trans hSize)
      hUR hUK hSpos hURShadow hFactor hHalfSize hCap hCapSize
  have hRegScale : (B.size:ℝ)*thinErr ≤ ((2*mBase:ℕ):ℝ)*εH2 := by
    have hCast : (B.size:ℝ) = (((2*s)*p:ℕ):ℝ)*((2*mBase:ℕ):ℝ) := by
      exact_mod_cast (show B.size = ((2*s)*p)*(2*mBase) by rw [hBaseSize]; ac_rfl)
    rw [hCast]
    change (((2*s)*p:ℕ):ℝ)*thinErr ≤ εH2 at hThinSmall
    nlinarith only [mul_le_mul_of_nonneg_right hThinSmall (Nat.cast_nonneg (α := ℝ) (2*mBase))]
  have hε : εH2 ≤ 1/16 := by dsimp only [εH2]; linarith only [hγβ]
  have hLarge : (B.size:ℝ)*thinErr ≤ ((2*mBase:ℕ):ℝ) :=
    hRegScale.trans (mul_le_of_le_one_right (Nat.cast_nonneg _) (by linarith only [hε]))
  have hTol : 2*thinErr ≤ εH2 := by
    have hCoef : (2:ℝ) ≤ (((2*s)*p:ℕ):ℝ) := by
      exact_mod_cast (show 2 ≤ (2*s)*p from (show 2 ≤ 2*s by omega).trans
        (Nat.le_mul_of_pos_right _ (by omega)))
    exact (mul_le_mul_of_nonneg_right hCoef hThin).trans hThinSmall
  have hFit : ((2*mBase:ℕ):ℝ)*εH2 ≤ (cutoff:ℝ) := by
    have hBaseR : (mBase:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hBase
    have hm₈ : 8 ≤ m := (le_max_right _ _).trans hSize
    have hFloor : ((m:ℝ)/3) ≤ ((m/2:ℕ):ℝ) := by
      have h : m ≤ 3*(m/2) := by omega
      have h' : (m:ℝ) ≤ 3*((m/2:ℕ):ℝ) := by exact_mod_cast h
      linarith only [h']
    rw [hCutoff,Nat.cast_mul,Nat.cast_ofNat]
    have h₁ := mul_le_mul_of_nonneg_right hBaseR (show 0 ≤ εH2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [h₁,h₂,hFloor,Nat.cast_nonneg (α := ℝ) m]
  have hCoeff : dH2-εH2 = densityMargin := by dsimp only [dH2,εH2,densityMargin]; ring
  have hShadowCard (j : L) : Fintype.card ↥(incoming j ∪ outgoing j) = shadow := D.card_all_red_cells j
  have hShadowSize (j : L) : 8 ≤ α*(Fintype.card ↥(incoming j ∪ outgoing j):ℝ) := by
    have hOrd : Fintype.card I ≤ shadow := Nat.le_mul_of_pos_right _ (by omega)
    have hα : 0 ≤ α := by linarith only [hAlpha,hν,hντ]
    rw [hShadowCard j]
    exact hCount.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hOrd) hα)
  obtain ⟨P,_,_,hP,_,hRange,hBalanced⟩ :=
    exists_osthus_staden_balanced_layers_from_robust_support B base A D hp hs Q hCopy hHost
      ν t₀ α shadowErr hν hντ hτ hOrder hRobust hIn hOut hAlpha hErr.le hErrSmall erase hErase
      bound c cap loss halfLoss cutoff used εH2 dH2 hHalf hLarge hRegScale hTol
      (by dsimp only [dH2,εH2] at hTol ⊢; linarith only [hTol,mul_pos hγ hβ])
      hCutPos hCapPos hDemand hKeep hFit hPrev (hCoeff.symm ▸ hDensity.le)
      (by simpa only [hCoeff] using hSlack) (by simpa only [hCoeff] using hNeed)
      hRedLayer hDemandRate hShadowSize (fun j => by rw [hShadowCard j]; exact hShadowCap)
  exact ⟨P,_,by positivity,hLoad',hP,hRange,hBalanced⟩

end OverfullWork.DirectedRobustExpansion
