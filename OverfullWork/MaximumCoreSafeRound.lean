module

public import OverfullWork.MaximumCoreOddCutCriterion

@[expose] public section


/-! A constructed three-cross round preserving global no-overfullness. -/
namespace OverfullWork.MaximumCoreThreeCrossRound
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun CleanedSourceVAL
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 32000000

theorem source_total_ge_add_two (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
    (c : Certificate G B K) (hCore : ∀ v ∈ c.set, G.degree v=G.maxDegree)
    (hLarge : G.maxDegree < ∑ y ∈ c.setᶜ, G.degree y) :
    G.maxDegree+2 ≤ ∑ y ∈ c.setᶜ, G.degree y := by
  have hX : (∑ v ∈ c.set, G.degree v)=G.maxDegree*c.set.card := by
    rw [sum_congr rfl (fun v hv => hCore v hv)]
    simp [Nat.mul_comm]
  have hSum := sum_add_sum_compl c.set (fun v => G.degree v)
  rw [hX,G.sum_degrees_eq_twice_card_edges] at hSum
  obtain ⟨t,ht⟩ := c.odd
  have hExpand : G.maxDegree*c.set.card=2*(G.maxDegree*t)+G.maxDegree := by rw [ht];ring
  rw [hExpand] at hSum
  omega

theorem round_no_overfull_of_omission_bound (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
    (c : Certificate G B K) (hReady : IsReady G c.setᶜ)
    (hCore : ∀ v ∈ c.set, G.degree v=G.maxDegree)
    (hLarge : G.maxDegree < ∑ y ∈ c.setᶜ, G.degree y)
    (U : Finset V) (hU : U ⊆ c.setᶜ) (hThree : U.card=3)
    (hTop : ∀ u ∈ U, ∀ v ∈ c.setᶜ, v ∉ U → G.degree v ≤ G.degree u)
    (r : Round G c.set U)
    (hSmall : 4*(B+K+2)+1 ≤ G.maxDegree)
    (hOmit : ∀ S : Finset V,Odd S.card →
      (G\r.matching).maxDegree*(S.card/2) < internalEdges (G\r.matching) S →
      (c.set \ S).card ≤ 1) :
    ¬(G\r.matching).HasOverfullSubgraph := by
  let R := G\r.matching
  have hMax : R.maxDegree=G.maxDegree-1 := r.residual_maxDegree
  have hPoint : ∀ v, R.degree v+r.matching.degree v=G.degree v := by
    intro v
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
  have hRCore : ∀ v ∈ c.set, R.degree v=R.maxDegree := by
    intro v hv
    have hh := hPoint v
    rw [r.core_degrees v hv,hCore v hv] at hh
    omega
  have hInd : G.IsIndepSet (↑(c.setᶜ):Set V) := by simpa only [coe_compl] using c.independent
  have hRInd := FixedCoreBudgetTransport.independent_of_le G R c.setᶜ hInd (sdiff_le : R ≤ G)
  have hTotal := r.merged_degree_add_three hU hThree
  change (∑ v ∈ c.setᶜ, R.degree v)+3=∑ v ∈ c.setᶜ, G.degree v at hTotal
  have hSourceTotal := source_total_ge_add_two G c hCore hLarge
  have hBudget : (∑ v ∈ c.setᶜ, G.degree v) ≤ G.maxDegree+B := by have hh := c.budget;omega
  have hRTotal : R.maxDegree ≤ ∑ v ∈ c.setᶜ, R.degree v := by omega
  have hRUpper : (∑ v ∈ c.setᶜ, R.degree v) ≤ R.maxDegree+B := by omega
  have hPositive : ∀ u ∈ U, 2 ≤ G.degree u := by
    intro u hu
    have hP := hPoint u
    rw [r.complementary_degrees u (hU hu),if_pos hu] at hP
    exact active_degree_at_least_two G c.setᶜ hReady u (hU hu) (by omega)
  have hRPoint : ∀ v ∈ c.setᶜ, R.degree v+(if v ∈ U then 1 else 0)=G.degree v := by
    intro v hv
    have hh := hPoint v
    rwa [r.complementary_degrees v hv] at hh
  have hPairs := TopThreePairReserve.pair_bound c.setᶜ U (fun v => G.degree v) (fun v => R.degree v)
    G.maxDegree (by omega) hU hThree hPositive hTop hReady.1 c.light_pairs hRPoint hTotal hSourceTotal
  have hLeaves : ∀ v ∈ c.set,
      ((Plantholt.nbIn R c.setᶜ v).filter (fun u => R.degree u=1)).card ≤ 1 := by
    intro v _
    apply card_le_one.mpr
    intro a ha b hb
    by_contra hab
    obtain ⟨haNb,haOne⟩ := mem_filter.mp ha
    obtain ⟨hbNb,hbOne⟩ := mem_filter.mp hb
    have haY := (mem_filter.mp haNb).2
    have hbY := (mem_filter.mp hbNb).2
    have hva : G.Adj v a := ((mem_neighborFinset R v a).mp (mem_filter.mp haNb).1).1
    have hvb : G.Adj v b := ((mem_neighborFinset R v b).mp (mem_filter.mp hbNb).1).1
    have haTwo : G.degree a=2 := by
      have hPa := hPoint a
      have hOne := r.degree_le_one a
      have hMin := active_degree_at_least_two G c.setᶜ hReady a haY
        ((G.degree_pos_iff_exists_adj a).mpr ⟨v,hva.symm⟩)
      omega
    exact degree_two_forbids_nonmaximum_common_neighbour G c.setᶜ hReady a b v haY haTwo
      (hReady.1 b hbY) (Ne.symm hab) hva.symm hvb.symm
  apply MaximumCoreOddCutCriterion.no_overfull_of_omission_bound R c.set c.odd hRCore hRInd B
    hRTotal hRUpper (by omega)
  · intro y hy z hz hyz
    have hh := hPairs y hy z hz hyz
    rw [←hMax] at hh
    exact hh
  · exact hLeaves
  · exact hOmit

theorem round_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
    (c : Certificate G B K) (hReady : IsReady G c.setᶜ)
    (hCore : ∀ v ∈ c.set, G.degree v=G.maxDegree)
    (hLarge : G.maxDegree < ∑ y ∈ c.setᶜ, G.degree y)
    (U : Finset V) (hU : U ⊆ c.setᶜ) (hThree : U.card=3)
    (hTop : ∀ u ∈ U, ∀ v ∈ c.setᶜ, v ∉ U → G.degree v ≤ G.degree u)
    (r : Round G c.set U)
    (hDense : Fintype.card V+B+K+5 ≤ 2*G.maxDegree)
    (hSmall : 4*(B+K+2)+1 ≤ G.maxDegree) :
    ¬(G\r.matching).HasOverfullSubgraph := by
  apply round_no_overfull_of_omission_bound G c hReady hCore hLarge U hU hThree hTop r hSmall
  have hMax := r.residual_maxDegree
  apply MaximumCoreOddCutCriterion.overfull_omits_at_most_one (G\r.matching) c.set K c.complement_small
  · intro v hv
    have h : (G\r.matching).degree v+r.matching.degree v=G.degree v := by
      simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
    rw [r.core_degrees v hv,hCore v hv] at h
    omega
  · omega
  · omega

theorem exists_safe_round (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
    (c : Certificate G B K) (hNC : ¬G.EdgeColorable G.maxDegree) (hReady : IsReady G c.setᶜ)
    (hCore : ∀ v ∈ c.set, G.degree v=G.maxDegree)
    (hLarge : G.maxDegree < ∑ y ∈ c.setᶜ, G.degree y)
    (hDense : Fintype.card V+B+K+5 ≤ 2*G.maxDegree)
    (hSmall : 4*(B+K+2)+1 ≤ G.maxDegree) :
    ∃ U : Finset V, U ⊆ c.setᶜ ∧ U.card=3 ∧
      (∀ u ∈ U, ∀ v ∈ c.setᶜ, v ∉ U → G.degree v ≤ G.degree u) ∧
      ∃ r : Round G c.set U, ¬(G\r.matching).HasOverfullSubgraph := by
  have hActive := MaximumCoreTripleChoice.three_active G c hCore hLarge
  obtain ⟨U,hU,hThree,hPos,hTop⟩ := ThreeLargestVertices.exists_selection c.setᶜ (fun v => G.degree v) hActive
  have hInd : G.IsIndepSet (↑(c.setᶜ):Set V) := by simpa only [coe_compl] using c.independent
  have hHall := MaximumNeighbourCleanup.hall_of_final_inequality G c.setᶜ hReady.1 hReady.2
  obtain ⟨r⟩ := exists_round G hNC c.set U c.odd hCore hInd hHall hReady.1 hU hThree hPos (by
    have hy := c.complement_small
    omega)
  exact ⟨U,hU,hThree,hTop,r,round_no_overfull G c hReady hCore hLarge U hU hThree hTop r hDense hSmall⟩

end OverfullWork.MaximumCoreThreeCrossRound
