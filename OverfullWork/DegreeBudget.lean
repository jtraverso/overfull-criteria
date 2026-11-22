module

public import OverfullWork.MatchingTutte

@[expose] public section


/-!
# Exact scalar budget at degree gap two

D is the set of all deficient vertices and A the set deficient by two.
The handshake identity becomes 2E + |D| + |A| = n Delta.
Consequently the matching budget is exactly |D| >= Delta, whereas the
whole-graph edge bound only gives |D| + |A| >= Delta.
-/

namespace OverfullWork.DegreeBudget

open SimpleGraph Finset
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.Compl.adjDecidable SimpleGraph.fintypeEdgeSetSup

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degree_add_two_indicators (G : SimpleGraph V) [DecidableRel G.Adj]
    (hgap : G.maxDegree - G.minDegree ≤ 2) (v : V) :
    G.degree v + (if v ∈ OddOrder.deficit G then 1 else 0) +
      (if v ∈ CapacityTwo.deepDeficit G then 1 else 0) = G.maxDegree := by
  have hmax := G.degree_le_maxDegree v
  have hmin := G.minDegree_le_degree v
  simp only [OddOrder.deficit, CapacityTwo.deepDeficit, mem_filter, mem_univ, true_and]
  split_ifs <;> omega

theorem deficit_budget_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hgap : G.maxDegree - G.minDegree ≤ 2) :
    2 * G.edgeFinset.card + (OddOrder.deficit G).card +
      (CapacityTwo.deepDeficit G).card = Fintype.card V * G.maxDegree := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  calc
    _ = ∑ v : V, (G.degree v + (if v ∈ OddOrder.deficit G then 1 else 0) +
        (if v ∈ CapacityTwo.deepDeficit G then 1 else 0)) := by
      simp [sum_add_distrib]
    _ = ∑ _v : V, G.maxDegree := sum_congr rfl (fun v _ => degree_add_two_indicators G hgap v)
    _ = _ := by simp

private theorem capacity_split (n D : ℕ) (hn : 1 ≤ n) : D * (n - 1) + D = n * D := by
  calc
    _ = D * (n - 1 + 1) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hn, Nat.mul_comm]

theorem budget_iff_many_deficient (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 1 ≤ Fintype.card V) (hgap : G.maxDegree - G.minDegree ≤ 2) :
    (2 * G.edgeFinset.card + (CapacityTwo.deepDeficit G).card ≤
      G.maxDegree * (Fintype.card V - 1)) ↔ G.maxDegree ≤ (OddOrder.deficit G).card := by
  have hid := deficit_budget_two G hgap
  have hsplit := capacity_split (Fintype.card V) G.maxDegree hn
  omega

theorem edge_bound_iff_weighted_deficit (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 1 ≤ Fintype.card V) (hgap : G.maxDegree - G.minDegree ≤ 2) :
    (2 * G.edgeFinset.card ≤ G.maxDegree * (Fintype.card V - 1)) ↔
      G.maxDegree ≤ (OddOrder.deficit G).card + (CapacityTwo.deepDeficit G).card := by
  have hid := deficit_budget_two G hgap
  have hsplit := capacity_split (Fintype.card V) G.maxDegree hn
  omega

theorem saturated_iff_exact_weighted_deficit (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 1 ≤ Fintype.card V) (hgap : G.maxDegree - G.minDegree ≤ 2) :
    (2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1)) ↔
      (OddOrder.deficit G).card + (CapacityTwo.deepDeficit G).card = G.maxDegree := by
  have hid := deficit_budget_two G hgap
  have hsplit := capacity_split (Fintype.card V) G.maxDegree hn
  omega

theorem edge_bound_of_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V)) (hno : ¬ G.HasOverfullSubgraph) :
    2 * G.edgeFinset.card ≤ G.maxDegree * (Fintype.card V - 1) := by
  have hwhole : G.edgeFinset.card ≤ G.maxDegree * (Fintype.card V / 2) := by
    by_contra h
    apply hno
    refine ⟨univ, ?_⟩
    simpa using Nat.lt_of_not_ge h
  obtain ⟨m, hm⟩ := hn
  have hhalf : Fintype.card V / 2 = m := by omega
  have hcap : G.maxDegree * (Fintype.card V - 1) = 2 * (G.maxDegree * m) := by
    rw [hm]
    have hsub : 2 * m + 1 - 1 = 2 * m := by omega
    rw [hsub]
    ring
  rw [hhalf] at hwhole
  rw [hcap]
  omega

theorem weighted_deficit_of_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V)) (hgap : G.maxDegree - G.minDegree ≤ 2)
    (hno : ¬ G.HasOverfullSubgraph) :
    G.maxDegree ≤ (OddOrder.deficit G).card + (CapacityTwo.deepDeficit G).card := by
  have hnpos : 1 ≤ Fintype.card V := by obtain ⟨m, hm⟩ := hn; omega
  exact (edge_bound_iff_weighted_deficit G hnpos hgap).mp (edge_bound_of_no_overfull G hn hno)

theorem edgeColourable_of_tutte_many_deficient (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V)) (hgap : G.maxDegree - G.minDegree ≤ 2)
    (htutte : MatchingTutte.TutteCondition Gᶜ (CapacityTwo.deepDeficit G))
    (hdef : G.maxDegree ≤ (OddOrder.deficit G).card)
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree) :
    G.EdgeColorable G.maxDegree := by
  have hnpos : 1 ≤ Fintype.card V := by obtain ⟨m, hm⟩ := hn; omega
  exact MatchingTutte.edgeColourable_of_complement_tutte G hn hgap htutte
    ((budget_iff_many_deficient G hnpos hgap).mpr hdef) hdense

theorem obstruction_dichotomy (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V)) (hgap : G.maxDegree - G.minDegree ≤ 2)
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree)
    (hnot : ¬ G.EdgeColorable G.maxDegree) :
    (OddOrder.deficit G).card < G.maxDegree ∨
      ∃ U : Set (CapacityTwo.deepDeficit G : Set V),
        (Gᶜ.induce (CapacityTwo.deepDeficit G : Set V)).IsTutteViolator U := by
  classical
  by_cases hdef : G.maxDegree ≤ (OddOrder.deficit G).card
  · right
    have hnpos : 1 ≤ Fintype.card V := by obtain ⟨m, hm⟩ := hn; omega
    exact MatchingTutte.tutte_violator_of_not_edgeColourable G hn hgap
      ((budget_iff_many_deficient G hnpos hgap).mpr hdef) hdense hnot
  · exact Or.inl (by omega)

omit [DecidableEq V] in
/-- At saturation, no edge can be added while preserving the same scalar bound. -/
theorem eq_of_saturated_supergraph (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hsub : G ≤ H)
    (hsat : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1))
    (hbound : 2 * H.edgeFinset.card ≤ G.maxDegree * (Fintype.card V - 1)) : G = H := by
  apply edgeFinset_inj.mp
  apply eq_of_subset_of_card_le (edgeFinset_mono hsub)
  omega

omit [DecidableEq V] in
/-- An already saturated graph with gap at least two cannot be repaired by
adding edges to reach the almost-regular family under the same edge bound. -/
theorem no_almostRegular_completion_of_saturated (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsat : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1))
    (hgap : 1 < G.maxDegree - G.minDegree) :
    ¬ ∃ H : SimpleGraph V, G ≤ H ∧ H.maxDegree - H.minDegree ≤ 1 ∧
      2 * H.edgeFinset.card ≤ G.maxDegree * (Fintype.card V - 1) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b => Classical.propDecidable (G.Adj a b)))
  rintro ⟨H, hsub, hreg, hbound⟩
  have heq := eq_of_saturated_supergraph G H hsub hsat hbound
  subst H
  omega

#print axioms deficit_budget_two
#print axioms budget_iff_many_deficient
#print axioms obstruction_dichotomy
#print axioms no_almostRegular_completion_of_saturated

end OverfullWork.DegreeBudget
