module

public import OverfullWork.CMSOperation42InitialNormalization

@[expose] public section


/-! From an actual near-tight odd witness to a terminal state of
Operation 4.2. The input robustness is spent on the normalized core,
which is unchanged by the initial cleanup and loses at most one
neighbour per matching round. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion OddCutDeficit
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u

set_option maxHeartbeats 5000000 in
theorem cms_operation_4_2_from_near_tight_odd_cut (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 512*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (b A K : ℕ),
      let n := Fintype.card V
      let B := b+2*(A+K)
      let r := ⌈ν*(n:ℝ)⌉₊
      let t := ⌈τ*(n:ℝ)⌉₊
      Odd X.card → Xᶜ.card ≤ K → N+3+K ≤ n → 2*K ≤ n →
      ¬G.EdgeColorable G.maxDegree → ¬G.HasOverfullSubgraph →
      (∀ u v,G.Adj u v → G.maxDegree ≤ G.degree u+G.degree v+A) →
      ClassTwoMatchingRun.budget G X ≤ G.maxDegree+b →
      IsRealRobust G (8*ν) (τ/4) →
      ((B/2+K:ℕ):ℝ) ≤ ν*(n:ℝ) →
      8*((K+3:ℕ):ℝ) ≤ ν*(n:ℝ) → 16*((K+3:ℕ):ℝ) ≤ τ*(n:ℝ) →
      α*(n:ℝ)+((B+K+3+B/2:ℕ):ℝ) ≤ (G.maxDegree:ℝ) →
      4*(B+K+2)+1+B/2 ≤ G.maxDegree →
      B+2*(A+K)+2+B/2 ≤ G.maxDegree →
      G.maxDegree ≤ (r-1)*(r-1) → 2*B+2*t+1+B/2 ≤ G.maxDegree →
      (∀ v,G.degree v = G.maxDegree) ∨
        ∃ (H Q : SimpleGraph V) (Z : Finset V) (j : ℕ),
          H ≤ G ∧ H.maxDegree = G.maxDegree ∧ Odd Z.card ∧ Zᶜ.card ≤ K ∧
          SafeFixedCoreRun Z H Q j ∧ OrderedFixedCoreState Q Z (A+K) ∧
          IsMatchingRemovalStop Q Z ∧ IsRealRobust Q ν τ ∧
          Q.maxDegree+j = G.maxDegree ∧ ClassTwoMatchingRun.budget Q Z+2*j ≤ Q.maxDegree+B ∧
          2*j ≤ B := by
  obtain ⟨N,hN⟩ := cms_operation_4_2_reaches_stopping_graph.{u} ν τ α hν hντ hτα hα
  refine ⟨N,?_⟩
  intro V _ _ G _ X b A K n B r t hOdd hSmall hn hHalf hNC hNo hVAL hBudget hRob
    hBν hSmallν hSmallτ hDens hRoom hGap hRate hPair
  have hτ : 0 < τ := hν.trans_le hντ
  have hA : b+2*(A+K)+1 ≤ G.maxDegree := by dsimp only [B] at hRoom; omega
  rcases exists_matching_removal_start_of_near_tight_odd_cut G X hOdd b A K hSmall
      hNC hNo hVAL hBudget hA with hReg | ⟨H,Z,_,hLe,hMax,hCore,hOddZ,hK,hInd,hBudgetH,a⟩
  · exact Or.inl hReg
  right
  let Y := Zᶜ
  let m := Z.card
  let R := ⌈(4*ν)*(m:ℝ)⌉₊
  let T := ⌈(τ/2)*(m:ℝ)⌉₊
  have hY : Y.card ≤ K := hK
  have hSum : m+Y.card = n := card_add_card_compl Z
  have hYR : (Y.card:ℝ) ≤ K := by exact_mod_cast hK
  have hZν : 8*(Y.card:ℝ) ≤ (8*ν)*(n:ℝ) := by
    have hN : 0 ≤ ν*(n:ℝ) := by positivity
    push_cast at hSmallν
    nlinarith only [hYR,hSmallν,hN]
  have hZτ : 4*(Y.card:ℝ) ≤ (τ/4)*(n:ℝ) := by
    push_cast at hSmallτ
    linarith only [hYR,hSmallτ]
  have hCoreRob := induced_graph_robust_of_small_complement G Z (8*ν) (τ/4)
    (by positivity) (by linarith only [hντ,hτα,hα]) (by positivity)
    (by linarith only [hτα,hα]) hRob hZν hZτ
  have hRobH : IsRobustAt (H.induce (Z : Set V)) R T := by
    have heν : 8*ν/2 = 4*ν := by ring
    have heτ : 2*(τ/4) = τ/2 := by ring
    rw [heν,heτ] at hCoreRob
    have he : Fintype.card (↥(Z : Set V)) = Z.card := Fintype.card_coe _
    have h₀ := CanonicalRegularization.integer_robust_of_real (G.induce (Z : Set V))
      (4*ν) (τ/2) (by positivity) hCoreRob
    rw [he] at h₀
    exact robust_at_of_eq _ _ hCore.symm _ _ h₀
  have hνR : ν*(n:ℝ) ≤ ((R-(B/2+Y.card):ℕ):ℝ) := by
    have hHalfM : (n:ℝ) ≤ 2*(m:ℝ) := by
      exact_mod_cast (show n ≤ 2*m by omega)
    have hFloor := Nat.le_ceil ((4*ν)*(m:ℝ))
    change (4*ν)*(m:ℝ) ≤ (R:ℝ) at hFloor
    have hScale := mul_le_mul_of_nonneg_left hHalfM hν.le
    have hBν' : ((B/2+Y.card:ℕ):ℝ) ≤ ν*(n:ℝ) := by
      exact (by exact_mod_cast Nat.add_le_add_left hY (B/2) :
        ((B/2+Y.card:ℕ):ℝ) ≤ ((B/2+K:ℕ):ℝ)).trans hBν
    have hLe : (B/2+Y.card:ℕ) ≤ R := by
      exact_mod_cast (show ((B/2+Y.card:ℕ):ℝ) ≤ (R:ℝ) by nlinarith only [hBν',hFloor,hScale,hν])
    rw [Nat.cast_sub hLe]
    nlinarith only [hBν',hFloor,hScale]
  have hτT : ((T+Y.card:ℕ):ℝ) ≤ τ*(n:ℝ) := by
    have hCeil := Nat.ceil_lt_add_one (show 0 ≤ (τ/2)*(m:ℝ) by positivity)
    change (T:ℝ) < (τ/2)*(m:ℝ)+1 at hCeil
    have hLe : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show m ≤ n by omega)
    have hScale := mul_le_mul_of_nonneg_left hLe (by positivity : 0 ≤ τ/2)
    rw [Nat.cast_add]
    push_cast at hSmallτ
    linarith only [hCeil,hScale,hSmallτ,hYR]
  have hSmallν' : 8*((Y.card+3:ℕ):ℝ) ≤ ν*(n:ℝ) := by
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hY 3) (by norm_num)).trans hSmallν
  have hSmallτ' : 4*((Y.card+3:ℕ):ℝ) ≤ τ*(n:ℝ) := by
    push_cast at hSmallτ ⊢
    linarith only [hSmallτ,hYR,Nat.cast_nonneg (α := ℝ) Y.card]
  have hDens' : α*(n:ℝ)+((B+Y.card+3+B/2:ℕ):ℝ) ≤ (H.maxDegree:ℝ) := by
    rw [hMax]
    have h : B+Y.card+3+B/2 ≤ B+K+3+B/2 := by omega
    exact (add_le_add_right (by exact_mod_cast h) _).trans hDens
  have hSize : N+3 ≤ Z.card := by change N+3 ≤ m; omega
  have hRoom' : 4*(B+K+2)+1+B/2 ≤ H.maxDegree := by rwa [hMax]
  have hGap' : B+2*(A+K)+2+B/2 ≤ H.maxDegree := by rwa [hMax]
  have hRate' : H.maxDegree ≤ (r-1)*(r-1) := by rwa [hMax]
  have hPair' : 2*B+2*t+1+B/2 ≤ H.maxDegree := by rwa [hMax]
  obtain ⟨Q,j,p,aQ,hEnd,hRobQ,hMaxQ,hBook,hLen,_⟩ :=
    hN H Z B K (A+K) R T hSize hOddZ hK (by omega) hInd hBudgetH a hRobH hνR hτT
      hSmallν' hSmallτ' hDens' hRoom' hGap' hRate' hPair'
  exact ⟨H,Q,Z,j,hLe,hMax,hOddZ,hK,p,aQ,hEnd,hRobQ,hMaxQ.trans hMax,by omega,hLen⟩

end OverfullWork.CMSMatchingRemoval
