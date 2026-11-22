module

public import OverfullWork.MaximumMatchingAugmentation
public import OverfullWork.MaximumMatchingTutte
public import OneFactor.Factors

@[expose] public section


/-! # Removing a matching that covers all vertices of maximum degree

The maximum degree drops by exactly one, and a colouring of the residue
with that many colours extends by one matching colour. Preservation of
no-overfullness under the removal is deliberately not asserted.
-/
namespace OverfullWork.MaximumMatching
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degree_sdiff_add_of_le (G M : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel M.Adj] (hMG : M≤G) (v : V) :
    (G\M).degree v+M.degree v=G.degree v := by
  rw [←card_neighborFinset_eq_degree,neighborFinset_sdiff]
  have hs : M.neighborFinset v⊆G.neighborFinset v := by
    intro w hw
    exact (mem_neighborFinset G v w).mpr (hMG ((mem_neighborFinset M v w).mp hw))
  simpa only [card_neighborFinset_eq_degree] using card_sdiff_add_card_eq_card hs

theorem maxDegree_sdiff_of_matching_cover (G M : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel M.Adj]
    (hD : 0<G.maxDegree) (hMG : M≤G)
    (hcover : ∀v,G.degree v=G.maxDegree → ∃!w,M.Adj v w) :
    (G\M).maxDegree=G.maxDegree-1 := by
  have hdeg (v : V) := degree_sdiff_add_of_le G M hMG v
  have hup : (G\M).maxDegree≤G.maxDegree-1 := by
    apply (G\M).maxDegree_le_of_forall_degree_le
    intro v
    by_cases hv : G.degree v=G.maxDegree
    · have hm : M.degree v=1 := degree_eq_one_iff_existsUnique_adj.mpr (hcover v hv)
      have hh := hdeg v
      omega
    · have hh := hdeg v
      have hd := G.degree_le_maxDegree v
      omega
  have hn : Nonempty V := by
    by_contra h
    have : IsEmpty V := not_nonempty_iff.mp h
    have hz : G.maxDegree=0 := G.maxDegree_of_subsingleton
    omega
  obtain ⟨v,hv⟩ := G.exists_maximal_degree_vertex
  have hm : M.degree v=1 := degree_eq_one_iff_existsUnique_adj.mpr (hcover v hv.symm)
  have hh := hdeg v
  have hr := (G\M).degree_le_maxDegree v
  omega

theorem colourable_of_matching_residue (G M : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel M.Adj]
    (hD : 0<G.maxDegree) (hMG : M≤G) (hmatch : OneFactor.IsMatchingGraph M)
    (hc : (G\M).EdgeColorable (G.maxDegree-1)) : G.EdgeColorable G.maxDegree := by
  have hd : Disjoint (G\M) M := disjoint_sdiff_self_left
  have hh := OneFactor.colorable_sup_matching hd hmatch hc
  have he : (G\M)⊔M=G := sdiff_sup_cancel hMG
  have hn : G.maxDegree-1+1=G.maxDegree := by omega
  change ((G\M)⊔M).EdgeColorable (G.maxDegree-1+1) at hh
  rw [he,hn] at hh
  exact hh

theorem critical_residue_not_colourable (G M : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel M.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hD : 0<G.maxDegree)
    (hMG : M≤G) (hmatch : OneFactor.IsMatchingGraph M)
    (hcover : ∀v,G.degree v=G.maxDegree → ∃!w,M.Adj v w) :
    ¬(G\M).EdgeColorable (G\M).maxDegree := by
  rw [maxDegree_sdiff_of_matching_cover G M hD hMG hcover]
  exact fun hc => hcrit.2.1 (colourable_of_matching_residue G M hD hMG hmatch hc)

/-- No-overfull supplies an actual matching with an exact one-degree drop. -/
theorem exists_exact_degree_lowering_matching (G : SimpleGraph V)
    [DecidableRel G.Adj] (hD : 0<G.maxDegree) (hno : ¬G.HasOverfullSubgraph) :
    ∃M : SimpleGraph V,M≤G ∧ OneFactor.IsMatchingGraph M ∧
      (G\M).maxDegree=G.maxDegree-1 := by
  obtain ⟨M,hMG,hm,hcover⟩ := exists_matching_covering_maximum_of_no_overfull G hD hno
  exact ⟨M,hMG,hm,maxDegree_sdiff_of_matching_cover G M hD hMG hcover⟩

/-- A hypothetical critical obstruction has a genuinely smaller-degree
uncolourable residue. No-overfullness of that residue remains unproved. -/
theorem exists_uncolourable_smaller_residue_of_critical (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcrit : Overfull.IsDeltaCritical G)
    (hD : 0<G.maxDegree) (hno : ¬G.HasOverfullSubgraph) :
    ∃M : SimpleGraph V,M≤G ∧ OneFactor.IsMatchingGraph M ∧
      (G\M).maxDegree=G.maxDegree-1 ∧ ¬(G\M).EdgeColorable (G\M).maxDegree := by
  obtain ⟨M,hMG,hm,hcover⟩ := exists_matching_covering_maximum_of_no_overfull G hD hno
  exact ⟨M,hMG,hm,maxDegree_sdiff_of_matching_cover G M hD hMG hcover,
    critical_residue_not_colourable G M hcrit hD hMG hm hcover⟩

end OverfullWork.MaximumMatching
