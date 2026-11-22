module

public import OverfullWork.CMSOperation42SafeRound
public import OverfullWork.MaximumCoreResidualConstraints

@[expose] public section


/-! A robust replacement round when the minimum core degree has
reached the maximum degree. Three independent cross edges then
cover an odd core together with a perfect matching on its remainder. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion OddCutDeficit NearTightOddSetGeometry
open NormalizedAlmostStoppingRun CleanedSourceVAL
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u

theorem robust_overfull_omits_at_most_one_of_maximum_core {V : Type*}
    [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (r t : ℕ) (hRob : IsRobustAt H r t)
    (hRate : H.maxDegree ≤ r*r) (hPair : 2*t ≤ H.maxDegree)
    (hCore : ∀ v ∈ X,H.degree v = H.maxDegree)
    (S : Finset V) (hOdd : Odd S.card) (hOver : H.maxDegree*(S.card/2) < internalEdges H S) :
    (X \ S).card ≤ 1 := by
  have hSize : H.maxDegree < S.card := by
    by_contra! h
    have hBound := Nat.mul_le_mul_right (S.card/2) h
    have hCap := internalEdges_le_card_mul_half H S hOdd
    omega
  have hCut : cutEdges H S < H.maxDegree := by
    have h := (odd_internal_bound_iff_cut_deficit H H.maxDegree H.degree_le_maxDegree S hOdd).not.mp
      (not_le.mpr hOver)
    omega
  have hShort : Sᶜ.card < t := by
    by_contra! hn
    have hComp := card_add_card_compl S
    have h := robust_cut_lower_simple H S r t hRob (by omega) (by omega)
    omega
  apply card_le_one.mpr
  intro a ha b hb
  by_contra hab
  have haS := mem_compl.mpr (mem_sdiff.mp ha).2
  have hbS := mem_compl.mpr (mem_sdiff.mp hb).2
  have hComp : ({a,b}:Finset V) ⊆ Sᶜ := insert_subset haS (singleton_subset_iff.mpr hbS)
  have hBound := CMSTrimmingRound.selected_degrees_le_cut_add_of_loss H H S {a,b} hComp 0 (fun _ => by simp)
  rw [sum_pair hab,card_pair hab,Nat.add_zero,hCore a (mem_sdiff.mp ha).1,hCore b (mem_sdiff.mp hb).1] at hBound
  omega

set_option maxHeartbeats 2000000 in
theorem cms_operation_4_2_maximum_core_safe_round (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 512*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ} (c : Certificate G B K),
      let X := c.set
      let Y := Xᶜ
      let n := Fintype.card V
      let r := ⌈ν*(n:ℝ)⌉₊
      let t := ⌈τ*(n:ℝ)⌉₊
      N+3 ≤ X.card →
      (∀ v ∈ X,G.degree v = G.maxDegree) →
      G.maxDegree < ∑ v ∈ Y,G.degree v →
      IsReady G Y → ¬G.EdgeColorable G.maxDegree → IsRealRobust G ν τ →
      8*((Y.card+3:ℕ):ℝ) ≤ ν*(n:ℝ) → 4*((Y.card+3:ℕ):ℝ) ≤ τ*(n:ℝ) →
      α*(n:ℝ)+(Y.card+3:ℕ) ≤ (G.maxDegree:ℝ) →
      4*(B+K+2)+1 ≤ G.maxDegree → 2*t+1 ≤ G.maxDegree →
      G.maxDegree ≤ (r-1)*(r-1) →
      ∃ U ⊆ Y,U.card = 3 ∧
        (∀ u ∈ U,∀ v ∈ Y,v ∉ U → G.degree v ≤ G.degree u) ∧
        ∃ q : MaximumCoreThreeCrossRound.Round G X U,¬(G \ q.matching).HasOverfullSubgraph := by
  have hτ : 0 < τ := hν.trans_le hντ
  have hαPos : 0 < α := by linarith only [hτα,hτ]
  have hν₁ : ν ≤ 1 := by linarith only [hντ,hτα,hα,hτ]
  have hτHalf : τ ≤ 1/2 := by linarith only [hτα,hα]
  obtain ⟨N,hN⟩ := exists_matching_on_even_robust_core.{u} (ν/2) (2*τ) α (by positivity)
    (by linarith only [hντ,hτ]) (by linarith only [hτα]) hα
  refine ⟨max N 1,?_⟩
  intro V _ _ G _ B K c X Y n r t hSize hCore hLarge hReady hNC hRob hSmallν hSmallτ
    hDens hSmall hPair hRate
  have hAct := MaximumCoreTripleChoice.three_active G c hCore hLarge
  obtain ⟨U,hU,hThree,hPos,hTop⟩ := ThreeLargestVertices.exists_selection Y (fun v => G.degree v) hAct
  have hInd : G.IsIndepSet (Y : Set V) := by simpa only [Y,X,coe_compl] using c.independent
  have hHall := MaximumNeighbourCleanup.hall_of_final_inequality G Y hReady.1 hReady.2
  obtain ⟨q⟩ := MaximumCoreThreeCrossRound.exists_round_of_core_matchings G hNC X U c.odd
    hInd hHall hReady.1 hU hThree hPos (by
      intro a b v ha hb hv hab hav hbv S hCard hEven
      have hSizeS : max N 1 ≤ S.card := by omega
      have hComp : Sᶜ.card = Y.card+3 := by
        have h₁ := card_add_card_compl S
        have h₂ := card_add_card_compl X
        change X.card+Y.card = n at h₂
        omega
      apply hN G S ((le_max_left _ _).trans hSizeS) hEven
      · apply induced_graph_robust_of_small_complement G S ν τ hν.le hν₁ hτ.le hτHalf hRob
        · rwa [hComp]
        · rwa [hComp]
      · have hSub : S ⊆ X := (erase_subset _ _).trans ((erase_subset _ _).trans (erase_subset _ _))
        obtain ⟨z,hz⟩ := card_pos.mp ((le_max_right N 1).trans hSizeS)
        have : Nonempty S := ⟨⟨z,hz⟩⟩
        have hDeg (w : S) : α*(S.card:ℝ) ≤ ((G.induce (S : Set V)).degree w:ℝ) := by
          have hw := degree_le_induced_add_complement G S w
          rw [hComp,hCore w.val (hSub w.property)] at hw
          have hR : (G.maxDegree:ℝ) ≤ ((G.induce (S : Set V)).degree w:ℝ)+(Y.card+3:ℕ) := by
            exact_mod_cast hw
          have hS : (S.card:ℝ) ≤ n := by exact_mod_cast card_le_univ S
          have hh := mul_le_mul_of_nonneg_left hS hαPos.le
          linarith only [hh,hR,hDens]
        obtain ⟨w,hw⟩ := (G.induce (S : Set V)).exists_minimal_degree_vertex
        simpa only [hw] using hDeg w)
  refine ⟨U,hU,hThree,hTop,q,?_⟩
  have hRI : IsRobustAt G r t := CanonicalRegularization.integer_robust_of_real G ν τ hν.le hRob
  have hR := RobustExpansion.isRobustAt_sdiff G q.matching r 1 t hRI q.degree_le_one
  have hResid : IsRobustAt (G \ q.matching) (r-1) t :=
    robust_at_of_eq _ _ (dG := SimpleGraph.Sdiff.adjDecidable V G q.matching) rfl _ _ hR
  have hMax : (G \ q.matching).maxDegree = G.maxDegree-1 := q.residual_maxDegree
  have hCore' (v : V) (hv : v ∈ X) : (G \ q.matching).degree v = (G \ q.matching).maxDegree := by
    have h : (G \ q.matching).degree v + q.matching.degree v = G.degree v := by
      simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le G q.matching q.le_original v
    rw [q.core_degrees v hv,hCore v hv] at h
    omega
  apply MaximumCoreThreeCrossRound.round_no_overfull_of_omission_bound
    G c hReady hCore hLarge U hU hThree hTop q hSmall
  intro S hOdd hOver
  exact robust_overfull_omits_at_most_one_of_maximum_core (G \ q.matching) X
    (r-1) t hResid (by omega) (by omega) hCore' S hOdd hOver

end OverfullWork.CMSMatchingRemoval
