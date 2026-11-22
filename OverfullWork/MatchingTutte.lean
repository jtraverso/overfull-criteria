module

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE-plantholt.

The subtype-to-ambient lifting construction follows
Plantholt.Tools.exists_matchingOn; the Tutte interfaces below are new.
-/
public import OverfullWork.CapacityTwo

@[expose] public section


/-!
# Exact Tutte criterion for a matching supported on a prescribed set

This replaces the sufficient Dirac hypothesis by the necessary and
sufficient odd-component condition for the same matching operation.
It does not claim that no-overfullness implies the Tutte condition.
-/

namespace OverfullWork.MatchingTutte

open SimpleGraph Finset
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.Compl.adjDecidable SimpleGraph.fintypeEdgeSetSup

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No odd-component obstruction in the graph induced on S. -/
def TutteCondition (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ U : Set (S : Set V), ¬ (G.induce (S : Set V)).IsTutteViolator U

theorem matchingOn_iff_perfectMatching_induce (G : SimpleGraph V) (S : Finset V) :
    (∃ M : SimpleGraph V, Plantholt.IsMatchingOn G M S) ↔
      ∃ P : (G.induce (S : Set V)).Subgraph, P.IsPerfectMatching := by
  classical
  constructor
  · rintro ⟨M, hMG, hMone, hMzero⟩
    let P : (G.induce (S : Set V)).Subgraph :=
      (G.induce (S : Set V)).toSubgraph (M.induce (S : Set V))
        (by intro u v huv; exact hMG huv)
    refine ⟨P, Subgraph.isPerfectMatching_iff.mpr ?_⟩
    intro v
    obtain ⟨w, hw, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp (hMone v.1 v.2)
    have hwS : w ∈ S := by
      by_contra hwS
      have hp := (M.degree_pos_iff_exists_adj w).mpr ⟨v.1, hw.symm⟩
      rw [hMzero w hwS] at hp
      omega
    refine ⟨⟨w, hwS⟩, hw, ?_⟩
    intro u hu
    apply Subtype.ext
    exact huniq u.1 hu
  · rintro ⟨P, hP⟩
    let M : SimpleGraph V :=
      { Adj := fun u v => ∃ hu : u ∈ S, ∃ hv : v ∈ S, P.Adj ⟨u, hu⟩ ⟨v, hv⟩
        symm.symm := by
          rintro u v ⟨hu, hv, h⟩
          exact ⟨hv, hu, P.adj_symm h⟩
        loopless := ⟨fun _ ⟨_, _, h⟩ => (P.adj_sub h).ne rfl⟩ }
    have hMG : M ≤ G := by
      rintro u v ⟨hu, hv, h⟩
      exact P.adj_sub h
    refine ⟨M, hMG, fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨w, hw, huniq⟩ := hP.1 (hP.2 ⟨v, hv⟩)
      rw [← card_neighborFinset_eq_degree, card_eq_one]
      refine ⟨w.1, ?_⟩
      ext u
      simp only [mem_neighborFinset, mem_singleton]
      constructor
      · rintro ⟨_, hu, h⟩
        exact congrArg Subtype.val (huniq ⟨u, hu⟩ h)
      · rintro rfl
        exact ⟨hv, w.2, hw⟩
    · rw [← card_neighborFinset_eq_degree, card_eq_zero]
      ext u
      simp only [mem_neighborFinset, notMem_empty, iff_false]
      rintro ⟨hv', _, _⟩
      exact hv hv'

theorem matchingOn_iff_tutte (G : SimpleGraph V) (S : Finset V) :
    (∃ M : SimpleGraph V, Plantholt.IsMatchingOn G M S) ↔ TutteCondition G S :=
  (matchingOn_iff_perfectMatching_induce G S).trans SimpleGraph.tutte

omit [DecidableEq V] in
theorem even_card_of_tutteCondition (G : SimpleGraph V) (S : Finset V)
    (h : TutteCondition G S) : Even S.card := by
  obtain ⟨P, hP⟩ := (SimpleGraph.tutte (G := G.induce (S : Set V))).mpr h
  simpa using hP.even_card

theorem tutteCondition_of_dirac (G : SimpleGraph V) (S : Finset V)
    (heven : Even S.card)
    (hdirac : ∀ v ∈ S, S.card ≤ 2 * (Plantholt.nbIn G S v).card) :
    TutteCondition G S :=
  (matchingOn_iff_tutte _ _).mp (Plantholt.exists_matchingOn G heven hdirac)

theorem no_matchingOn_iff_tutte_violator (G : SimpleGraph V) (S : Finset V) :
    (¬ ∃ M : SimpleGraph V, Plantholt.IsMatchingOn G M S) ↔
      ∃ U : Set (S : Set V), (G.induce (S : Set V)).IsTutteViolator U := by
  classical
  rw [matchingOn_iff_tutte]
  simp [TutteCondition]

omit [Fintype V] [DecidableEq V] in
theorem tutteCondition_iff_component_bound (G : SimpleGraph V) (S : Finset V) :
    TutteCondition G S ↔ ∀ U : Set (S : Set V),
      ((⊤ : (G.induce (S : Set V)).Subgraph).deleteVerts U).coe.oddComponents.ncard ≤
        U.ncard := by
  simp only [TutteCondition, IsTutteViolator, not_lt]

/-- The preceding gate applies whenever the exact Tutte condition holds.
Parity of the deficient set follows from Tutte and is not a separate premise. -/
theorem edgeColourable_of_complement_tutte (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V))
    (hgap : G.maxDegree - G.minDegree ≤ 2)
    (htutte : TutteCondition Gᶜ (CapacityTwo.deepDeficit G))
    (hbudget : 2 * G.edgeFinset.card + (CapacityTwo.deepDeficit G).card ≤
      G.maxDegree * (Fintype.card V - 1))
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree) :
    G.EdgeColorable G.maxDegree := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b => Classical.propDecidable (G.Adj a b)))
  obtain ⟨M, hMsub, hMone, hMzero⟩ := (matchingOn_iff_tutte _ _).mpr htutte
  apply CapacityTwo.edgeColourable_of_deep_matching G M hn hgap hMsub _ hbudget hdense
  intro v
  by_cases hv : v ∈ CapacityTwo.deepDeficit G
  · rw [if_pos hv]
    exact hMone v hv
  · rw [if_neg hv]
    exact hMzero v hv

/-- Any colouring obstruction surviving the degree and budget bounds must
give a genuine odd-component witness to failure of this matching method. -/
theorem tutte_violator_of_not_edgeColourable (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V))
    (hgap : G.maxDegree - G.minDegree ≤ 2)
    (hbudget : 2 * G.edgeFinset.card + (CapacityTwo.deepDeficit G).card ≤
      G.maxDegree * (Fintype.card V - 1))
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree)
    (hnot : ¬ G.EdgeColorable G.maxDegree) :
    ∃ U : Set (CapacityTwo.deepDeficit G : Set V),
      (Gᶜ.induce (CapacityTwo.deepDeficit G : Set V)).IsTutteViolator U := by
  classical
  by_contra h
  have htutte : TutteCondition Gᶜ (CapacityTwo.deepDeficit G) := by
    intro U hU
    exact h ⟨U, hU⟩
  exact hnot (edgeColourable_of_complement_tutte G hn hgap htutte hbudget hdense)

#print axioms matchingOn_iff_tutte
#print axioms no_matchingOn_iff_tutte_violator
#print axioms edgeColourable_of_complement_tutte
#print axioms tutte_violator_of_not_edgeColourable

end OverfullWork.MatchingTutte
