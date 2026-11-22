module

public import OverfullWork.FournierCoreCriterion
public import OverfullWork.FourLayers
public import OverfullWork.CycleSplitTransport

@[expose] public section


/-! # Deterministic degree splitting with discrepancy two -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- A pair of submultigraphs with additive degree discrepancy at most two. -/
def BalancedTwo (A B : MultiGraph V) : Prop :=
  ∀ v, A.degree v ≤ B.degree v + 2 ∧ B.degree v ≤ A.degree v + 2

/-- Compensate the only possible imbalance of a cycle against the previous split. -/
theorem balancedTwo_add_piece {A B P Q : MultiGraph V} (x : V)
    (hAB : BalancedTwo A B) (hPQ : BalancedTwo P Q)
    (heq : ∀ v, v ≠ x → P.degree v = Q.degree v) :
    BalancedTwo (A.addCopies P) (B.addCopies Q) ∨
      BalancedTwo (A.addCopies Q) (B.addCopies P) := by
  by_cases h : A.degree x ≤ B.degree x
  · by_cases h' : Q.degree x ≤ P.degree x
    · left
      intro v
      rw [degree_addCopies, degree_addCopies]
      have ha := hAB v
      have hp := hPQ v
      by_cases hv : v = x
      · subst v; omega
      · have he := heq v hv; omega
    · right
      intro v
      rw [degree_addCopies, degree_addCopies]
      have ha := hAB v
      have hp := hPQ v
      by_cases hv : v = x
      · subst v; omega
      · have he := heq v hv; omega
  · by_cases h' : P.degree x ≤ Q.degree x
    · left
      intro v
      rw [degree_addCopies, degree_addCopies]
      have ha := hAB v
      have hp := hPQ v
      by_cases hv : v = x
      · subst v; omega
      · have he := heq v hv; omega
    · right
      intro v
      rw [degree_addCopies, degree_addCopies]
      have ha := hAB v
      have hp := hPQ v
      by_cases hv : v = x
      · subst v; omega
      · have he := heq v hv; omega

/-- The multigraph consisting of a single nonloop edge. -/
def edgeUnit (x y : V) (hxy : x ≠ y) : MultiGraph V where
  mult e := if e = s(x,y) then 1 else 0
  loopless e he := by
    have hne : e ≠ s(x,y) := by
      intro h
      subst e
      exact hxy (Sym2.mk_isDiag_iff.mp he)
    simp [hne]

theorem degree_edgeUnit (x y : V) (hxy : x ≠ y) (v : V) :
    (edgeUnit x y hxy).degree v = if v = x ∨ v = y then 1 else 0 := by
  simp [degree, edgeUnit, Sym2.mem_iff]

/-- A single leaf edge may be put on the side opposing its neighbour's deficit. -/
theorem balancedTwo_add_leaf {A B : MultiGraph V} (x y : V) (hxy : x ≠ y)
    (hAB : BalancedTwo A B) (hxA : A.degree x = 0) (hxB : B.degree x = 0) :
    BalancedTwo (A.addCopies (edgeUnit x y hxy)) B ∨
      BalancedTwo A (B.addCopies (edgeUnit x y hxy)) := by
  by_cases hy : A.degree y ≤ B.degree y
  · left
    intro v
    rw [degree_addCopies, degree_edgeUnit]
    have ha := hAB v
    by_cases hvx : v = x
    · subst v; simp only [hxA, hxB, true_or, if_true]; omega
    · by_cases hvy : v = y
      · subst v; simp only [hxy.symm, false_or, true_or, if_true]; omega
      · simp only [hvx, hvy, false_or, if_false]; omega
  · right
    intro v
    rw [degree_addCopies, degree_edgeUnit]
    have ha := hAB v
    by_cases hvx : v = x
    · subst v; simp only [hxA, hxB, true_or, if_true]; omega
    · by_cases hvy : v = y
      · subst v; simp only [hxy.symm, false_or, true_or, if_true]; omega
      · simp only [hvx, hvy, false_or, if_false]; omega

/-- Removing a contained simple piece and adding it back conserves every edge copy. -/
theorem simple_sdiff_add (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) :
    (ofSimpleGraph (G \ H)).addCopies (ofSimpleGraph H) = ofSimpleGraph G := by
  apply ext_mult
  intro e
  have hsub : e ∈ H.edgeSet → e ∈ G.edgeSet := fun he => edgeSet_mono hHG he
  change (if e ∈ (G \ H).edgeSet then 1 else 0) +
      (if e ∈ H.edgeSet then 1 else 0) = (if e ∈ G.edgeSet then 1 else 0)
  simp only [edgeSet_sdiff, Set.mem_sdiff]
  split_ifs <;> tauto

/-- A forest with an edge has a nonisolated leaf. -/
theorem exists_nonisolated_leaf (G : SimpleGraph V) [DecidableRel G.Adj]
    (hforest : G.IsAcyclic) (hne : G ≠ ⊥) :
    ∃ x y, G.Adj x y ∧ G.degree x = 1 := by
  classical
  obtain ⟨a, b, hab⟩ := G.ne_bot_iff_exists_adj.mp hne
  haveI : Nonempty G.support := ⟨⟨a, hab.mem_support_left⟩⟩
  obtain ⟨v, hv⟩ := OverfullWork.FournierCore.exists_degree_le_one_of_acyclic
    (G.induce G.support) (hforest.induce G.support)
  rw [degree_induce_support] at hv
  have hp : 0 < G.degree v.val := (G.degree_pos_iff_mem_support v.val).mpr v.property
  obtain ⟨y, hy⟩ := (G.degree_pos_iff_exists_adj v.val).mp hp
  exact ⟨v.val, y, hy, by omega⟩

/-- Deleting one present edge and adding its unit multigraph back is exact. -/
theorem simple_delete_add_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (hxy : G.Adj x y) :
    (ofSimpleGraph (G.deleteEdges {s(x,y)})).addCopies (edgeUnit x y hxy.ne) =
      ofSimpleGraph G := by
  apply ext_mult
  intro e
  have heG : s(x,y) ∈ G.edgeSet := (mem_edgeSet G).mpr hxy
  change (if e ∈ (G.deleteEdges {s(x,y)}).edgeSet then 1 else 0) +
    (if e = s(x,y) then 1 else 0) = (if e ∈ G.edgeSet then 1 else 0)
  simp only [edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
  split_ifs <;> simp_all

/-- Reassemble two split pieces, allowing the second pair to have been exchanged. -/
theorem reassemble_split {A B P Q M N : MultiGraph V}
    (hAB : A.addCopies B = M) (hPQ : P.addCopies Q = N) :
    (A.addCopies P).addCopies (B.addCopies Q) = M.addCopies N := by
  apply ext_mult
  intro e
  have ha := congrArg (fun K : MultiGraph V => K.mult e) hAB
  have hp := congrArg (fun K : MultiGraph V => K.mult e) hPQ
  change A.mult e + P.mult e + (B.mult e + Q.mult e) = M.mult e + N.mult e
  change A.mult e + B.mult e = M.mult e at ha
  change P.mult e + Q.mult e = N.mult e at hp
  omega

/-- The structural cycle-removal interface used by the induction below. -/
def HasCyclePiece (G : SimpleGraph V) : Prop :=
  ∃ H : SimpleGraph V, H ≤ G ∧ H ≠ ⊥ ∧
    ∃ x, ∃ P Q : MultiGraph V, P.addCopies Q = ofSimpleGraph H ∧
      (∀ v, v ≠ x → P.degree v = Q.degree v) ∧ BalancedTwo P Q

/-- Induction on the number of edges, with a cycle piece or a forest leaf
removed at each step. The cycle interface is supplied by an explicit construction. -/
theorem exists_halves_of_cycle_pieces
    (hpieces : ∀ G : SimpleGraph V, ¬ G.IsAcyclic → HasCyclePiece G)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ A B : MultiGraph V, A.addCopies B = ofSimpleGraph G ∧ BalancedTwo A B := by
  classical
  suffices ∀ n (K : SimpleGraph V) [DecidableRel K.Adj], K.edgeSet.ncard = n →
      ∃ A B : MultiGraph V, A.addCopies B = ofSimpleGraph K ∧ BalancedTwo A B by
    simpa using this G.edgeSet.ncard G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K instK hcard
    letI : DecidableRel K.Adj := instK
    by_cases hbot : K = ⊥
    · subst K
      refine ⟨ofSimpleGraph ⊥, ofSimpleGraph ⊥, ?_, ?_⟩
      · apply ext_mult; intro e; simp [ofSimpleGraph, addCopies]
      · intro v
        simp [degree_ofSimpleGraph]
    by_cases hforest : K.IsAcyclic
    · obtain ⟨x, y, hxy, hx⟩ := exists_nonisolated_leaf K hforest hbot
      let R := K.deleteEdges {s(x,y)}
      letI : DecidableRel R.Adj := inferInstance
      have hlt : R.edgeSet.ncard < n := by
        rw [← hcard]
        apply Set.ncard_lt_ncard (ht := Set.toFinite K.edgeSet)
        apply edgeSet_strict_mono
        apply lt_of_le_of_ne (K.deleteEdges_le {s(x,y)})
        intro he
        have hR : ¬ R.Adj x y := by simp [R]
        exact hR (by simpa only [R, he] using hxy)
      obtain ⟨A, B, hAB, hbal⟩ := ih R.edgeSet.ncard hlt R rfl
      have hsum : (ofSimpleGraph R).addCopies (edgeUnit x y hxy.ne) = ofSimpleGraph K :=
        simple_delete_add_edge K x y hxy
      have hzero : (ofSimpleGraph R).degree x = 0 := by
        rw [degree_ofSimpleGraph]
        have hd := congrArg (fun M : MultiGraph V => M.degree x) hsum
        simp only [degree_addCopies, degree_edgeUnit, degree_ofSimpleGraph, hx] at hd
        simp only [true_or, if_true] at hd
        omega
      have hdegrees := congrArg (fun M : MultiGraph V => M.degree x) hAB
      rw [degree_addCopies, hzero] at hdegrees
      have hAx : A.degree x = 0 := by omega
      have hBx : B.degree x = 0 := by omega
      rcases balancedTwo_add_leaf x y hxy.ne hbal hAx hBx with hleft | hright
      · refine ⟨A.addCopies (edgeUnit x y hxy.ne), B, ?_, hleft⟩
        apply ext_mult
        intro e
        have ha := congrArg (fun M : MultiGraph V => M.mult e) hAB
        have hs := congrArg (fun M : MultiGraph V => M.mult e) hsum
        dsimp only [addCopies] at ha hs ⊢
        omega
      · refine ⟨A, B.addCopies (edgeUnit x y hxy.ne), ?_, hright⟩
        apply ext_mult
        intro e
        have ha := congrArg (fun M : MultiGraph V => M.mult e) hAB
        have hs := congrArg (fun M : MultiGraph V => M.mult e) hsum
        dsimp only [addCopies] at ha hs ⊢
        omega
    · obtain ⟨H, hHK, hHbot, x, P, Q, hPQ, heq, hPQbal⟩ := hpieces K hforest
      let R := K \ H
      letI : DecidableRel R.Adj := inferInstance
      have hlt : R.edgeSet.ncard < n := by
        rw [← hcard]
        apply Set.ncard_lt_ncard (ht := Set.toFinite K.edgeSet)
        apply edgeSet_strict_mono
        apply lt_of_le_of_ne sdiff_le
        intro he
        have hd : Disjoint K H := sdiff_eq_left.mp he
        have hH0 : H = ⊥ := (disjoint_self.mp ((hd.mono_left hHK)))
        exact hHbot hH0
      obtain ⟨A, B, hAB, hbal⟩ := ih R.edgeSet.ncard hlt R rfl
      have hsum : (ofSimpleGraph R).addCopies (ofSimpleGraph H) = ofSimpleGraph K :=
        simple_sdiff_add K H hHK
      rcases balancedTwo_add_piece x hbal hPQbal heq with hleft | hright
      · exact ⟨A.addCopies P, B.addCopies Q, (reassemble_split hAB hPQ).trans hsum, hleft⟩
      · have hQP : Q.addCopies P = ofSimpleGraph H := by
          apply ext_mult
          intro e
          have hh := congrArg (fun M : MultiGraph V => M.mult e) hPQ
          dsimp only [addCopies] at hh ⊢
          omega
        exact ⟨A.addCopies Q, B.addCopies P, (reassemble_split hAB hQP).trans hsum, hright⟩

/-- Every finite simple graph can be split deterministically into two layers
whose degrees differ by at most two at every vertex. -/
theorem exists_deterministic_simple_halves (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ A B : MultiGraph V, A.addCopies B = ofSimpleGraph G ∧
      ∀ v, A.degree v ≤ B.degree v + 2 ∧ B.degree v ≤ A.degree v + 2 := by
  apply exists_halves_of_cycle_pieces (G := G)
  intro K hcyc
  obtain ⟨H, hHK, hHbot, x, P, Q, hPQ, hoff, hp, hq⟩ :=
    OverfullWork.DeterministicSplit.exists_cycle_split_of_not_isAcyclic K hcyc
  refine ⟨H, hHK, hHbot, x, P, Q, hPQ, hoff, ?_⟩
  intro v
  by_cases hv : v = x
  · subst v; exact ⟨hp, hq⟩
  · rw [hoff v hv]
    omega

end SimpleGraph.MultiGraph
