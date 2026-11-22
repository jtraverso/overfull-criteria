module

public import OverfullWork.CMSOperation42OrderedContinuation

@[expose] public section


/-! A complete matching-removal run from a normalized, separated core.
All numeric margins are imposed once. The prefix length bound then
supplies robustness and the numerical hypotheses at every current graph. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph OddCutDeficit RobustExpansion
open NormalizedAlmostStoppingRun NearTightOddSetGeometry
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u

set_option maxHeartbeats 5500000 in
theorem cms_operation_4_2_reaches_stopping_graph (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 512*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (B K L R T : ℕ),
      let Y := Xᶜ
      let n := Fintype.card V
      let r := ⌈ν*(n:ℝ)⌉₊
      let t := ⌈τ*(n:ℝ)⌉₊
      N+3 ≤ X.card → Odd X.card → Y.card ≤ K → Y.card ≤ L →
      G.IsIndepSet (↑Y : Set V) → ClassTwoMatchingRun.budget G X ≤ G.maxDegree+B →
      OrderedFixedCoreState G X L → IsRobustAt (G.induce (X : Set V)) R T →
      ν*(n:ℝ) ≤ ((R-(B/2+Y.card):ℕ):ℝ) → ((T+Y.card:ℕ):ℝ) ≤ τ*(n:ℝ) →
      8*((Y.card+3:ℕ):ℝ) ≤ ν*(n:ℝ) → 4*((Y.card+3:ℕ):ℝ) ≤ τ*(n:ℝ) →
      α*(n:ℝ)+((B+Y.card+3+B/2:ℕ):ℝ) ≤ (G.maxDegree:ℝ) →
      4*(B+K+2)+1+B/2 ≤ G.maxDegree → B+2*L+2+B/2 ≤ G.maxDegree →
      G.maxDegree ≤ (r-1)*(r-1) → 2*B+2*t+1+B/2 ≤ G.maxDegree →
      ∃ H : SimpleGraph V,∃ j : ℕ,SafeFixedCoreRun X G H j ∧
        OrderedFixedCoreState H X L ∧ IsMatchingRemovalStop H X ∧ IsRealRobust H ν τ ∧
        H.maxDegree+j = G.maxDegree ∧
        ClassTwoMatchingRun.budget H X+3*j = ClassTwoMatchingRun.budget G X ∧
        2*j ≤ B ∧ ∀ x ∈ X,(∀ v ∈ X,G.degree x ≤ G.degree v) →
          j ≤ (∑ y ∈ Y,G.degree y)-G.degree x := by
  obtain ⟨N,hN⟩ := cms_operation_4_2_continue_ordered.{u} ν τ α hν hντ hτα hα
  refine ⟨N,?_⟩
  intro V _ _ G _ X B K L R T Y n r t hSize hOdd hK hL hInd hBudget a₀ hRob hνR hτT hSmall hSmallτ
    hDens hRoom hGap hRate hPair
  classical
  have hX : X.Nonempty := card_pos.mp (by omega)
  have hMin (H : SimpleGraph V) [DecidableRel H.Adj] :
      ∃ x ∈ X,∀ v ∈ X,H.degree x ≤ H.degree v :=
    X.exists_min_image (fun v => H.degree v) hX
  let pick (H : SimpleGraph V) [DecidableRel H.Adj] : V := (hMin H).choose
  have hp (H : SimpleGraph V) [DecidableRel H.Adj] : pick H ∈ X := (hMin H).choose_spec.1
  have hpMin (H : SimpleGraph V) [DecidableRel H.Adj] :
      ∀ v ∈ X,H.degree (pick H) ≤ H.degree v := (hMin H).choose_spec.2
  let e (H : SimpleGraph V) [DecidableRel H.Adj] : ℕ :=
    (∑ w ∈ Y,H.degree w)-H.degree (pick H)
  have hNext {H : SimpleGraph V} [DecidableRel H.Adj] {j : ℕ}
      (p : SafeFixedCoreRun X G H j) (a : OrderedFixedCoreState H X L)
      (hStop : ¬IsMatchingRemovalStop H X) :
      ∃ J : SimpleGraph V,SafeFixedCoreStep X H J ∧ OrderedFixedCoreState J X L ∧ e J+1 ≤ e H := by
    have hLen := p.length_le_half_slack hOdd hInd a₀.no_overfull B hBudget
    have hBook := p.budget_and_maximum hX
    have hRobH := p.uniform_robust_source hOdd hInd a₀.no_overfull B hBudget R T hRob ν τ hνR hτT
    have hIndH : H.IsIndepSet (Xᶜ : Set V) :=
      by simpa only [coe_compl] using FixedCoreBudgetTransport.independent_of_le G H Xᶜ hInd p.le
    let c : Certificate H B K :=
      { set := X
        odd := hOdd
        complement_small := hK
        budget := by unfold ClassTwoMatchingRun.budget at hBook hBudget; omega
        ordered := a.ordered
        light_pairs := by
          intro y hy z hz hyz
          have h := a.pairs y hy z hz hyz
          omega
        independent := by simpa only [coe_compl] using hIndH }
    have hDensH : α*(n:ℝ)+((B+Y.card+3:ℕ):ℝ) ≤ (H.maxDegree:ℝ) := by
      have hj : (j:ℝ) ≤ (B/2:ℕ) := by exact_mod_cast (show j ≤ B/2 by omega)
      have hm : (H.maxDegree:ℝ)+j = (G.maxDegree:ℝ) := by exact_mod_cast hBook.2
      rw [Nat.cast_add] at hDens
      linarith only [hDens,hj,hm]
    have hRateH : H.maxDegree ≤ (r-1)*(r-1) := by omega
    have hPairH : 2*B+2*t+1 ≤ H.maxDegree := by omega
    obtain ⟨J,hs,aJ,hDecrease⟩ := hN H c hSize hL a hStop hRobH hSmall hSmallτ hDensH
      (by omega) (by omega) hRateH hPairH (pick H) (hp H) (hpMin H)
    exact ⟨J,hs,aJ,hDecrease (pick J) (hp J)⟩
  have finish (m : ℕ) : ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (j : ℕ),
      e H = m → j+m ≤ e G → SafeFixedCoreRun X G H j → OrderedFixedCoreState H X L →
      ∃ J k,SafeFixedCoreRun X G J k ∧ OrderedFixedCoreState J X L ∧
        IsMatchingRemovalStop J X ∧ k ≤ e G := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro H dH j hm hj p a
      cases Subsingleton.elim dH (fun x y => Classical.propDecidable (H.Adj x y))
      by_cases hStop : IsMatchingRemovalStop H X
      · exact ⟨H,j,p,a,hStop,by omega⟩
      · obtain ⟨J,hs,aJ,hDec⟩ := hNext p a hStop
        exact ih (e J) (by omega) J (j+1) rfl (by omega) (SafeFixedCoreRun.step p hs) aJ
  obtain ⟨H,j,p,a,hEnd,hj⟩ := finish (e G) G 0 rfl (by simp) SafeFixedCoreRun.refl a₀
  obtain ⟨hDrop,hMax⟩ := p.budget_and_maximum hX
  have hRobH := p.uniform_robust_source hOdd hInd a₀.no_overfull B hBudget R T hRob ν τ hνR hτT
  have hLen := p.length_le_half_slack hOdd hInd a₀.no_overfull B hBudget
  refine ⟨H,j,p,a,hEnd,hRobH,hMax,hDrop,hLen,?_⟩
  intro x hx hMinX
  have he := (hpMin G x hx).antisymm (hMinX _ (hp G))
  dsimp only [e] at hj
  rwa [he] at hj

end OverfullWork.CMSMatchingRemoval
