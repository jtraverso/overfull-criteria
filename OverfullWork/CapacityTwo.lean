module

public import OverfullWork.Saturation

@[expose] public section


/-!
# A sufficient complement-capacity condition for degree gap two

First cover the vertices deficient by two with a perfect matching in the
complement on that vertex set. A separate edge-budget condition ensures
that this operation does not cross the whole-graph overfull bound.
The previous almost-regular gate then applies.

Existence of the first matching is proved under a concrete Dirac condition,
using the already checked Tutte/Dirac matching theorem. No assertion is
made that absence of overfull subgraphs alone implies these hypotheses.
-/

namespace OverfullWork.CapacityTwo

open SimpleGraph Finset
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.Compl.adjDecidable SimpleGraph.fintypeEdgeSetSup

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

def deepDeficit (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter (fun v => G.degree v + 1 < G.maxDegree)

/-- A computable presentation of the registered neighbour-set operation. -/
theorem nbIn_eq_filter (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    Plantholt.nbIn G S v = univ.filter (fun u => G.Adj v u ∧ u ∈ S) := by
  ext u
  simp [Plantholt.nbIn]

theorem degree_union (G M : SimpleGraph V) (hdisj : Disjoint G M) (v : V) :
    (G ⊔ M).degree v = G.degree v + M.degree v := by
  rw [degree, neighborFinset_sup, card_union_of_disjoint
    (disjoint_neighborFinset_of_disjoint G M v hdisj)]
  rfl

theorem edge_count_union (G M : SimpleGraph V) (hdisj : Disjoint G M) :
    (G ⊔ M).edgeFinset.card = G.edgeFinset.card + M.edgeFinset.card := by
  rw [edgeFinset_sup, card_union_of_disjoint (disjoint_edgeFinset.mpr hdisj)]

/-- Transfer any perfect matching on the deeply deficient vertices to a
colouring, provided the scalar edge budget can pay for the added edges. -/
theorem edgeColourable_of_deep_matching
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : SimpleGraph V)
    (hn : Odd (Fintype.card V))
    (hgap : G.maxDegree - G.minDegree ≤ 2)
    (hMsub : M ≤ Gᶜ)
    (hMdegree : ∀ v, M.degree v = if v ∈ deepDeficit G then 1 else 0)
    (hbudget : 2 * G.edgeFinset.card + (deepDeficit G).card ≤
      G.maxDegree * (Fintype.card V - 1))
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree) :
    G.EdgeColorable G.maxDegree := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b => Classical.propDecidable (G.Adj a b)))
  have : Nonempty V := Fintype.card_pos_iff.mp (by obtain ⟨m, hm⟩ := hn; omega)
  have hdisj : Disjoint G M := by
    rw [SimpleGraph.disjoint_left]
    intro u v hG hM
    exact ((compl_adj G u v).mp (hMsub hM)).2 hG
  have hMcount : 2 * M.edgeFinset.card = (deepDeficit G).card := by
    rw [← M.sum_degrees_eq_twice_card_edges]
    simp_rw [hMdegree]
    simp
  have hupper (v : V) : (G ⊔ M).degree v ≤ G.maxDegree := by
    rw [degree_union G M hdisj, hMdegree]
    by_cases hv : v ∈ deepDeficit G
    · rw [if_pos hv]
      have h := (mem_filter.mp hv).2
      omega
    · rw [if_neg hv, Nat.add_zero]
      exact G.degree_le_maxDegree v
  have hlower (v : V) : G.maxDegree ≤ (G ⊔ M).degree v + 1 := by
    rw [degree_union G M hdisj, hMdegree]
    have hmin := G.minDegree_le_degree v
    by_cases hv : v ∈ deepDeficit G
    · rw [if_pos hv]
      omega
    · rw [if_neg hv]
      have h : ¬ G.degree v + 1 < G.maxDegree :=
        fun hh => hv (mem_filter.mpr ⟨mem_univ _, hh⟩)
      omega
  have hmax : (G ⊔ M).maxDegree = G.maxDegree :=
    le_antisymm (maxDegree_le_of_forall_degree_le _ _ hupper) (maxDegree_mono le_sup_left)
  have hregular : (G ⊔ M).maxDegree - (G ⊔ M).minDegree ≤ 1 := by
    obtain ⟨v, hv⟩ := (G ⊔ M).exists_minimal_degree_vertex
    have h := hlower v
    rw [← hv, ← hmax] at h
    omega
  have hbound : 2 * (G ⊔ M).edgeFinset.card ≤
      (G ⊔ M).maxDegree * (Fintype.card V - 1) := by
    rw [edge_count_union G M hdisj, hmax]
    omega
  have hdense' : 6 * (Fintype.card V + 1) ≤ 7 * (G ⊔ M).maxDegree := by rwa [hmax]
  have hc := Saturation.edgeColourable_of_dense_odd_almostRegular
    (G ⊔ M) hn hregular hbound hdense'
  rw [hmax] at hc
  exact Critical.colourable_of_copy (Copy.ofLE G (G ⊔ M) le_sup_left) hc

/-- A closed sufficient criterion with only degree, parity and edge-count
hypotheses. The Dirac condition concerns the complement on deepDeficit G. -/
theorem edgeColourable_of_complement_dirac
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V))
    (hgap : G.maxDegree - G.minDegree ≤ 2)
    (heven : Even (deepDeficit G).card)
    (hdirac : ∀ v ∈ deepDeficit G,
      (deepDeficit G).card ≤ 2 * (Plantholt.nbIn Gᶜ (deepDeficit G) v).card)
    (hbudget : 2 * G.edgeFinset.card + (deepDeficit G).card ≤
      G.maxDegree * (Fintype.card V - 1))
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree) :
    G.EdgeColorable G.maxDegree := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b => Classical.propDecidable (G.Adj a b)))
  obtain ⟨M, hMsub, hMone, hMzero⟩ :=
    Plantholt.exists_matchingOn (G := Gᶜ) heven hdirac
  apply edgeColourable_of_deep_matching G M hn hgap hMsub _ hbudget hdense
  intro v
  by_cases hv : v ∈ deepDeficit G
  · rw [if_pos hv]
    exact hMone v hv
  · rw [if_neg hv]
    exact hMzero v hv

#print axioms edgeColourable_of_deep_matching
#print axioms edgeColourable_of_complement_dirac

end OverfullWork.CapacityTwo
