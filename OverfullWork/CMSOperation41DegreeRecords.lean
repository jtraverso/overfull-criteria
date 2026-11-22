module

public import OverfullWork.CMSLayoutMultigraph
public import OverfullWork.DirectedConfigurationDegrees

@[expose] public section


/-! Degree records after the simultaneous realization of the fixed
core layouts in CMS Operation 4.1. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset SimpleGraph DirectedRobustExpansion
open scoped Classical

variable {V I J : Type*} [Fintype V] [DecidableEq V]

theorem hostEdges_degree_of_orientation {G : SimpleGraph V} {D U : Digraph V}
    (hD : IsOrientationOf D G) (hU : U ≤ D) (v : V) :
    (hostEdges G U).degree v = outDegree U v + inDegree U v := by
  let out := (univ : Finset V).filter (U.Adj v)
  let ins := (univ : Finset V).filter (fun w => U.Adj w v)
  have hDisjoint : Disjoint out ins := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact hD.2.2 v w ⟨hU (mem_filter.mp hw).2,hU (mem_filter.mp hw').2⟩
  have hEq : (hostEdges G U).neighborFinset v = out ∪ ins := by
    ext w
    rw [mem_neighborFinset,mem_union]
    simp only [out,ins,mem_filter,mem_univ,true_and]
    constructor
    · exact And.right
    · intro h
      exact ⟨h.elim (fun hh => hD.1 _ _ (hU hh)) (fun hh => (hD.1 _ _ (hU hh)).symm),h⟩
  rw [←card_neighborFinset_eq_degree,hEq,card_union_of_disjoint hDisjoint]
  rfl

theorem Layout.fixedMultigraph_degree (L : Layout V I) (v : V) :
    L.fixedMultigraph.degree v =
      (∑ i ∈ L.fixed, if v = L.source i then 1 else 0)+
      (∑ i ∈ L.fixed, if v = L.target i then 1 else 0) := by
  rw [MultiGraph.degree,←sum_add_distrib]
  simp only [fixedMultigraph,card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  have hne : L.source i ≠ L.target i := (L.ends i).2.2
  let e := s(L.source i,L.target i)
  by_cases h : v ∈ e
  · have hmem : e ∈ (univ : Finset (Sym2 V)).filter (fun e => v ∈ e) := mem_filter.mpr ⟨mem_univ _,h⟩
    rw [sum_eq_single e]
    · rcases Sym2.mem_iff.mp h with h | h
      · simp [e,h,hne]
      · simp [e,h,hne.symm]
    · intro a _ ha
      exact if_neg (Ne.symm ha)
    · exact fun hh => False.elim (hh hmem)
  · have hl : v ≠ L.source i := by intro he; apply h; simp [e,he]
    have hr : v ≠ L.target i := by intro he; apply h; simp [e,he]
    simp only [hl,hr,if_false,Nat.zero_add]
    apply sum_eq_zero
    intro a ha
    apply if_neg
    intro he
    change e = a at he
    apply h
    rw [he]
    exact (mem_filter.mp ha).2

theorem CMSPacking.multigraph_degree {G : SimpleGraph V}
    {K : J → Type*} [∀ i, Fintype (K i)] {L : ∀ j, Layout V (K j)}
    (P : CMSPacking K G L) (j : J) (v : V) :
    (P.multigraph j).degree v = if v ∈ (L j).boundary then
      (L j).endpointLoad false v + (L j).endpointLoad true v +
        (L j).fixedMultigraph.degree v else 2 := by
  rw [CMSPacking.multigraph,MultiGraph.degree_addCopies,MultiGraph.degree_ofSimpleGraph,
    hostEdges_degree_of_orientation P.isOrientation (P.configuration j).used_le]
  obtain ⟨hi,ho⟩ := (P.configuration j).semidegrees_used v
  rw [hi,ho]
  by_cases hV : v ∈ (L j).boundary
  · simp only [if_pos hV,Layout.endpointLoad,Bool.false_eq_true,if_false,if_true]
    congr 2 <;> apply sum_congr rfl <;> intro i hi <;> split <;> simp_all
  · have hFrom (i : K j) : v ≠ (L j).source i := fun h => hV (h ▸ ((L j).ends i).1)
    have hTo (i : K j) : v ≠ (L j).target i := fun h => hV (h ▸ ((L j).ends i).2.1)
    simp [hV,(L j).fixedMultigraph_degree,hFrom,hTo]

end OverfullWork.DirectedSpanningConfiguration
