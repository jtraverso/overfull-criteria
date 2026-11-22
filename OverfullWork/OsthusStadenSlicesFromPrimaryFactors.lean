module

public import OverfullWork.OsthusStadenUnwoundPrimarySlices

@[expose] public section


/-! Assemble §5.3 from the primary factors and their physical reserves. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u v

/-- The five physical reserves on the retained base cells. -/
def primaryThinDigraphs {V I : Type*} [Fintype V] [Fintype I]
    {H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
    {m₀ b : ℕ} {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc) (j : Fin 5) : Digraph V :=
  directedPairUnion (fun e : ReducedCopy M => (B.kept e.1.1).trans (B.base e.1.1))
    (fun e : ReducedCopy M => (B.kept e.1.2).trans (B.base e.1.2)) (B.thin j)

set_option maxHeartbeats 1600000 in
/-- Construct all aligned base and adapted cells, and then all disjoint
initial slices. The threshold depends on bounds on the number of
primary clusters and primary factors. -/
theorem exists_osthus_staden_slices_from_primary_factors_with_incidence_bound
    (s p K L : ℕ) (hs : 0 < s) (hp : p.Prime) (hp₂ : 2 < p) [NeZero p] [NeZero (2*s)]
    (hK : 0 < K)
    (ε₀ loss ε εbase τ η d : ℝ)
    (hε₀ : 0 < ε₀) (hε₀₁ : ε₀ ≤ 1) (hLoss : 0 < loss) (hLoss₁ : loss ≤ 1/4)
    (hGood : 8*ε₀ ≤ loss) (hTrim : 4*(ε₀+loss) ≤ ε) (hε₁ : ε ≤ 1)
    (hεbase : 0 < εbase) (hBaseSmall : εbase ≤ τ/4) (hτ : 0 < τ) (hτ₁ : τ ≤ 1/8)
    (hAdapt : 16*loss*(((2*s)*(p*2):ℕ):ℝ) ≤ τ^2/16)
    (hFloor : 4*τ ≤ d-ε) (hη : max (2*ε) (ε+4*τ) ≤ η) (hη₁ : η ≤ 1)
    (hScale : (((2*s)*p:ℕ):ℝ)*ε ≤ η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
      {m₀ r : ℕ} {β γ a exc : ℝ}
      (B : OsthusStadenPrimaryReserveData H f M m₀ ((2*s)*(p*2)) β γ ε₀ a exc)
      (σ : Fin r → Equiv.Perm I) (pick : Fin r → I → ReducedCopy M),
      N ≤ B.size → Fintype.card I ≤ K → r ≤ L → H ≤ G →
      exc ≤ 1/2 → (1-5*γ)*β = d → 0 ≤ d → d ≤ 1 →
      (∀ t i, (pick t i).1 = (i,σ t i)) →
      Function.Injective (fun q : Fin r × I => pick q.1 q.2) →
      (∀ i, M i i = 0) →
      ∀ (fillCap : ℕ) (badBound : ℝ), 0 < fillCap → 4*loss*(r:ℝ) ≤ (fillCap:ℝ) →
      B.MainCopyIncidenceBound badBound →
      ∃ mBase m : ℕ, 0 < m ∧ m ≤ mBase ∧ B.size = (2*s)*(p*(2*mBase)) ∧
        B.size ≤ 2*((2*s)*(p*(2*m))) ∧
        ((B.size-(2*s)*(p*(2*m)):ℕ):ℝ) ≤ 2*loss*(B.size:ℝ) ∧
        ∃ g : Fin r → V → Option I, ∃ E : Fin r → I → Digraph V,
          (∀ t, ((exceptional (g t)).card:ℝ) ≤ (exc+2*loss)*(Fintype.card V:ℝ)) ∧
          (∀ t i, (cluster (g t) i).card = (2*s)*(p*(2*m)) ∧ cluster (g t) i ⊆ cluster B.partition i) ∧
          (∀ x, B.partition x ≠ none →
            (((univ : Finset (Fin r)).filter (fun t => g t x = none)).card:ℝ) ≤ 2*badBound+fillCap) ∧
          let profiles := arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E)
          ∃ R : ∀ i, PrimaryNestedRefinement profiles (cluster B.partition i) (2*s) p mBase εbase εbase εbase,
          ∃ S : ∀ t i, PrimaryNestedRefinement profiles (cluster (g t) i) (2*s) p m τ τ τ,
            let D := (2*s)*(p*(2*mBase))-(2*s)*(p*(2*m))
            (∀ t i j, max ((R i).first.cells j \ (S t i).first.cells j).card
              ((S t i).first.cells j \ (R i).first.cells j).card ≤ 2*D) ∧
            (∀ t i j k, max (((R i).second j).cells k \ ((S t i).second j).cells k).card
              (((S t i).second j).cells k \ ((R i).second j).cells k).card ≤ 3*D) ∧
            (∀ t i j k h, max (((R i).halves j k).cells h \ ((S t i).halves j k).cells h).card
              (((S t i).halves j k).cells h \ ((R i).halves j k).cells h).card ≤ 4*D) ∧
            Nonempty (UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ η d S) := by
  let b := (2*s)*(p*2)
  have hs' : 0 < 2*s := by omega
  have hb : 0 < b := Nat.mul_pos hs' (Nat.mul_pos hp.pos (by decide))
  let C : ℝ := 4*(6+(L:ℝ)*(K:ℝ))*(b:ℝ)*(K:ℝ)
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨N₁,hN₁⟩ := exists_adapted_primary_factors_with_incidence_bound ε₀ loss ε b
    hε₀ hε₀₁ hLoss hLoss₁ hb hGood hTrim hε₁
  obtain ⟨N₂,hN₂⟩ := exists_aligned_primary_refinements.{u,v,max u v} C εbase τ hC hεbase hBaseSmall
    hτ (by linarith only [hτ₁]) (2*s) p hs' hp.pos
  refine ⟨max N₁ (b*N₂),?_⟩
  intro V _ I _ G H f M m₀ r β γ a exc B σ pick hN hCard hr hHG hExc hdEq hd hd₁ hPick hInj hLoop fillCap badBound hCap hCapSize hBadMain
  obtain ⟨mOrd,hmOrd,hDiv,hOrdLe,hHalf,hDrop,g,E,hCell,_,hExcept,hLe,hDis,hThin,hPair,hTypeCount⟩ :=
    hN₁ B ((le_max_left _ _).trans hN) (by rwa [hdEq]) (by rwa [hdEq])
      σ pick hPick hInj fillCap badBound hCap hCapSize hBadMain
  obtain ⟨mBase,hBase⟩ := B.size_dvd
  obtain ⟨m,hM⟩ := hDiv
  have hm : 0 < m := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hM
    omega
  have hMLe : m ≤ mBase := Nat.le_of_mul_le_mul_left (hM ▸ hBase ▸ hOrdLe) hb
  have hNBase : N₂ ≤ mBase :=
    Nat.le_of_mul_le_mul_left ((le_max_right N₁ (b*N₂)).trans hN |>.trans_eq hBase) hb
  have hBaseEq : B.size = (2*s)*(p*(2*mBase)) := by
    rw [hBase]
    simp only [b,Nat.mul_assoc]
  have hMEq : mOrd = (2*s)*(p*(2*m)) := by
    rw [hM]
    simp only [b,Nat.mul_assoc]
  have hBaseCells (i : I) : (cluster B.partition i).card = B.size := by
    rw [←B.retained_cells i,card_map,card_univ,Fintype.card_fin]
  have hNOrd : (Fintype.card V:ℝ) ≤ 2*(B.size:ℝ)*(Fintype.card I:ℝ) := by
    have hEq : (Fintype.card V:ℝ) =
        ((exceptional B.partition).card:ℝ)+(B.size:ℝ)*(Fintype.card I:ℝ) := by
      exact_mod_cast order_eq B.partition B.size hBaseCells
    have hBudget := B.exceptional_le.trans (mul_le_mul_of_nonneg_right hExc (Nat.cast_nonneg _))
    linarith only [hEq,hBudget]
  let profiles := arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E)
  have hPcard : Fintype.card ((Option (Fin 5) ⊕ (Fin r × I)) × Bool × V)
      = (6+r*Fintype.card I)*(2*Fintype.card V) := by simp
  have hProfiles : (Fintype.card ((Option (Fin 5) ⊕ (Fin r × I)) × Bool × V):ℝ) ≤ C*(mBase:ℝ) := by
    have hI : (Fintype.card I:ℝ) ≤ K := by exact_mod_cast hCard
    have hR : (r:ℝ) ≤ L := by exact_mod_cast hr
    have hRI := mul_le_mul hR hI (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hTerms : 6+(r:ℝ)*(Fintype.card I:ℝ) ≤ 6+(L:ℝ)*(K:ℝ) := by linarith only [hRI]
    have hN' : (Fintype.card V:ℝ) ≤ 2*(b:ℝ)*(K:ℝ)*(mBase:ℝ) := by
      have hI' := mul_le_mul_of_nonneg_left hI (show 0 ≤ 2*(B.size:ℝ) by positivity)
      have he : (B.size:ℝ) = (b:ℝ)*(mBase:ℝ) := by exact_mod_cast hBase
      rw [he] at hI' hNOrd
      nlinarith only [hI',hNOrd]
    rw [hPcard]
    push_cast
    calc
      _ ≤ (6+(L:ℝ)*(K:ℝ))*(2*(Fintype.card V:ℝ)) :=
        mul_le_mul_of_nonneg_right hTerms (by positivity)
      _ ≤ (6+(L:ℝ)*(K:ℝ))*(2*(2*(b:ℝ)*(K:ℝ)*(mBase:ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN' (by norm_num)) (by positivity)
      _ = _ := by dsimp only [C]; ring
  have hAdaptBudget :
      4*(((2*s)*(p*(2*mBase))-(2*s)*(p*(2*m)):ℕ):ℝ) ≤ (τ^2/16)*(m:ℝ) := by
    rw [←hBaseEq,←hMEq]
    have hHalfR : (B.size:ℝ) ≤ 2*(mOrd:ℝ) := by exact_mod_cast hHalf
    have hLost := mul_le_mul_of_nonneg_left hHalfR (show 0 ≤ 2*loss by positivity)
    have hM' : (mOrd:ℝ) = (b:ℝ)*(m:ℝ) := by exact_mod_cast hM
    have hBudget := mul_le_mul_of_nonneg_right hAdapt (Nat.cast_nonneg m : (0:ℝ) ≤ _)
    rw [hM'] at hLost
    nlinarith only [hDrop,hLost,hBudget]
  obtain ⟨R,S,hS₁,hS₂,hS₃⟩ := hN₂ profiles B.partition g mBase m hNBase hMLe
    (fun i => (hBaseCells i).trans hBaseEq)
    (fun t i => ⟨(hCell t i).1.trans hMEq,(hCell t i).2⟩) hProfiles hAdaptBudget
  refine ⟨mBase,m,hm,hMLe,hBaseEq,hMEq ▸ hHalf,hMEq ▸ hDrop,g,E,hExcept,
    fun t i => ⟨(hCell t i).1.trans hMEq,(hCell t i).2⟩,
    hTypeCount,R,S,hS₁,hS₂,hS₃,?_⟩
  apply exists_unwound_primary_slices hs hp hp₂ G (primaryThinDigraphs B) E g σ
    (factor_has_no_fixed_points_of_loopless_multiplicity M σ pick hPick hLoop)
    ε τ η d hτ.le hτ₁ hFloor hη hη₁ hScale S
  · exact fun t i => (hLe t i).trans hHG
  · exact fun t t' h i j => hDis t i t' j (fun he => h (congrArg Prod.fst he))
  · exact hThin
  · simpa only [hdEq] using hPair

/-- The aligned refinements and disjoint initial slices. -/
theorem exists_osthus_staden_slices_from_primary_factors
    (s p K L : ℕ) (hs : 0 < s) (hp : p.Prime) (hp₂ : 2 < p) [NeZero p] [NeZero (2*s)]
    (hK : 0 < K)
    (ε₀ loss ε εbase τ η d : ℝ)
    (hε₀ : 0 < ε₀) (hε₀₁ : ε₀ ≤ 1) (hLoss : 0 < loss) (hLoss₁ : loss ≤ 1/4)
    (hGood : 8*ε₀ ≤ loss) (hTrim : 4*(ε₀+loss) ≤ ε) (hε₁ : ε ≤ 1)
    (hεbase : 0 < εbase) (hBaseSmall : εbase ≤ τ/4) (hτ : 0 < τ) (hτ₁ : τ ≤ 1/8)
    (hAdapt : 16*loss*(((2*s)*(p*2):ℕ):ℝ) ≤ τ^2/16)
    (hFloor : 4*τ ≤ d-ε) (hη : max (2*ε) (ε+4*τ) ≤ η) (hη₁ : η ≤ 1)
    (hScale : (((2*s)*p:ℕ):ℝ)*ε ≤ η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
      {m₀ r : ℕ} {β γ a exc : ℝ}
      (B : OsthusStadenPrimaryReserveData H f M m₀ ((2*s)*(p*2)) β γ ε₀ a exc)
      (σ : Fin r → Equiv.Perm I) (pick : Fin r → I → ReducedCopy M),
      N ≤ B.size → Fintype.card I ≤ K → r ≤ L → H ≤ G →
      exc ≤ 1/2 → (1-5*γ)*β = d → 0 ≤ d → d ≤ 1 →
      (∀ t i, (pick t i).1 = (i,σ t i)) →
      Function.Injective (fun q : Fin r × I => pick q.1 q.2) →
      (∀ i, M i i = 0) →
      ∃ mBase m : ℕ, 0 < m ∧ m ≤ mBase ∧ B.size = (2*s)*(p*(2*mBase)) ∧
        ∃ g : Fin r → V → Option I, ∃ E : Fin r → I → Digraph V,
          (∀ t, ((exceptional (g t)).card:ℝ) ≤ (exc+2*loss)*(Fintype.card V:ℝ)) ∧
          let profiles := arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E)
          ∃ R : ∀ i, PrimaryNestedRefinement profiles (cluster B.partition i) (2*s) p mBase εbase εbase εbase,
          ∃ S : ∀ t i, PrimaryNestedRefinement profiles (cluster (g t) i) (2*s) p m τ τ τ,
            let D := (2*s)*(p*(2*mBase))-(2*s)*(p*(2*m))
            (∀ t i j, max ((R i).first.cells j \ (S t i).first.cells j).card
              ((S t i).first.cells j \ (R i).first.cells j).card ≤ 2*D) ∧
            (∀ t i j k, max (((R i).second j).cells k \ ((S t i).second j).cells k).card
              (((S t i).second j).cells k \ ((R i).second j).cells k).card ≤ 3*D) ∧
            (∀ t i j k h, max (((R i).halves j k).cells h \ ((S t i).halves j k).cells h).card
              (((S t i).halves j k).cells h \ ((R i).halves j k).cells h).card ≤ 4*D) ∧
            Nonempty (UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ η d S) := by
  obtain ⟨N,hN⟩ := exists_osthus_staden_slices_from_primary_factors_with_incidence_bound.{u,v}
    s p K L hs hp hp₂ hK ε₀ loss ε εbase τ η d hε₀ hε₀₁ hLoss hLoss₁ hGood hTrim hε₁
    hεbase hBaseSmall hτ hτ₁ hAdapt hFloor hη hη₁ hScale
  refine ⟨N,?_⟩
  intro V _ I _ G H f M m₀ r β γ a exc B σ pick hSize hI hr hSub hExc hdEq hd hd₁ hPick hInj hLoop
  let cap := max 1 r
  have hCap : 0 < cap := (Nat.zero_lt_succ 0).trans_le (le_max_left _ _)
  have hCapSize : 4*loss*(r:ℝ) ≤ (cap:ℝ) :=
    (mul_le_of_le_one_left (Nat.cast_nonneg r) (by linarith only [hLoss₁])).trans
      (by exact_mod_cast (le_max_right 1 r))
  have hBadMain : B.MainCopyIncidenceBound (Fintype.card (ReducedCopy M):ℝ) := by
    intro s i x
    exact_mod_cast card_le_univ _
  obtain ⟨mBase,m,hm,hMLe,hBaseEq,_,_,g,E,hExcept,_,_,hRefine⟩ :=
    hN B σ pick hSize hI hr hSub hExc hdEq hd hd₁ hPick hInj hLoop cap _ hCap hCapSize hBadMain
  exact ⟨mBase,m,hm,hMLe,hBaseEq,g,E,hExcept,hRefine⟩

end OverfullWork.DirectedRobustExpansion
