module

public import OverfullWork.CMSOperation42CoreRobustness
public import OverfullWork.CMSRegularizationDenseBase

@[expose] public section


/-! One safe round of the paper's matching-removal operation,
with robust core matching, actual cleanup and preservation of
no-overfullness and the fixed-core degree budget. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion CanonicalRegularization
open NormalizedAlmostStoppingRun CleanedSourceVAL
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u

set_option maxHeartbeats 1800000 in
theorem cms_operation_4_2_safe_round (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 512*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      {B K : ℕ} (c : Certificate G B K) (x : V),
      let X := c.set
      let Y := Xᶜ
      let n := Fintype.card V
      let r := ⌈ν*(n:ℝ)⌉₊
      let t := ⌈τ*(n:ℝ)⌉₊
      N+3 ≤ X.card → x ∈ X → G.degree x < G.maxDegree →
      (G.degree x < ∑ u ∈ Y,G.degree u) →
      (∀ v ∈ X,v ≠ x → G.maxDegree < G.degree x+G.degree v) →
      IsReady G Y → ¬G.EdgeColorable G.maxDegree → ¬G.HasOverfullSubgraph →
      IsRealRobust G ν τ →
      8*((Y.card+3:ℕ):ℝ) ≤ ν*(n:ℝ) → 4*((Y.card+3:ℕ):ℝ) ≤ τ*(n:ℝ) →
      α*(n:ℝ)+(B+Y.card+3:ℕ) ≤ (G.maxDegree:ℝ) →
      2*B+3*K+4 ≤ G.maxDegree → G.maxDegree ≤ (r-1)*(r-1) → 2*B+2*t+1 ≤ G.maxDegree →
      ∃ s : ClassTwoCleanupRound.CleanRound G X,
        s.anchor = x ∧ ¬s.graph.HasOverfullSubgraph := by
  obtain ⟨N,hN⟩ := cms_operation_4_2_clean_round.{u} ν τ α hν hντ hτα hα
  refine ⟨N,?_⟩
  intro V _ _ G _ B K c x X Y n r t hSize hx hxD hLarge hNonstop hReady hNC hNo hRob
    hSmall hSmallτ hDens hRoom hRate hPair
  have hInd : G.IsIndepSet (Y : Set V) := by simpa only [Y,X,coe_compl] using c.independent
  have hActive := ClassTwoGlobalNoOverfull.two_active_of_large_centre G c x hx hLarge
  have hHigh (v : V) (hv : v ∈ X) (hvx : v ≠ x) :
      α*(n:ℝ)+(Y.card+3:ℕ) ≤ (G.degree v:ℝ) := by
    have h := LargeCentreCriticalGeometry.other_degree_lower G c hx hLarge hv hvx
    have hNat : G.maxDegree ≤ G.degree v+B := by omega
    have hh : (G.maxDegree:ℝ) ≤ (G.degree v:ℝ)+B := by exact_mod_cast hNat
    push_cast at hDens ⊢
    linarith only [hDens,hh]
  obtain ⟨s,hAnchor⟩ := hN G X x hSize c.odd hx hxD hInd hReady hNC hRob
    hSmall hSmallτ hHigh hActive c.light_pairs (by omega)
  have hRobI : IsRobustAt G r t := integer_robust_of_real G ν τ hν.le hRob
  have hLayer (v : V) : s.round.matching.degree v ≤ 1 := s.round.degree_le_one v
  have hRes := RobustExpansion.isRobustAt_sdiff G s.round.matching r 1 t hRobI hLayer
  refine ⟨s,hAnchor,?_⟩
  apply cleaned_round_no_overfull_of_robust G c hReady s _ hNo _ hRoom (r-1) t _ hRate hPair
  · simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,hAnchor] using hLarge
  · simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card,hAnchor] using hNonstop
  · exact robust_at_of_eq _ _ (dG := SimpleGraph.Sdiff.adjDecidable V G s.round.matching) rfl _ _ hRes

end OverfullWork.CMSMatchingRemoval
