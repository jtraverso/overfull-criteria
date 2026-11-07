/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OverfullCriteria.Basic

/-!
# Proofs of the statements in `OverfullCriteriaChallenge.lean`

From `OneFactor.overfull_criterion67` (jtraverso/plantholt-overfull-criterion,
PALOMAR-2026-11-04-000016) and `Overfull.overfull_of_critical`, `Overfull.overfull_of_critical_cc`,
`Overfull.overfull_of_critical_ccjs` (jtraverso/overfull-critical-graphs, PALOMAR-2026-11-04-000009),
with the glue lemmas of `OverfullCriteria.Basic`.
-/

@[expose] public section

namespace OverfullCriteria

open SimpleGraph Finset

universe u

/-- **Overfull criterion (Plantholt 2004 with `c = 6/7`).** -/
theorem class_two_iff_overfull_subgraph {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hev : Even (Fintype.card V))
    (hdeg : 12 * Fintype.card V ≤ 7 * (3 * G.minDegree - G.maxDegree)) :
    ¬ G.lineGraph.Colorable G.maxDegree ↔
      ∃ H : G.Subgraph, Odd H.verts.ncard ∧ 3 ≤ H.verts.ncard ∧
        G.maxDegree * (H.verts.ncard - 1) < 2 * H.edgeSet.ncard := by
  rw [OneFactor.overfull_criterion67 G hev hdeg, not_not]
  rfl

/-- **Critical graphs of small minimum degree are overfull (Chen–Cao; Cao–Chen–Jing–Shan).** -/
theorem critical_overfull {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hclass : ¬ G.lineGraph.Colorable G.maxDegree)
    (hcrit : ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).lineGraph.Colorable G.maxDegree)
    (hcond : 2 * Fintype.card V + 5 * G.minDegree ≤ 3 * G.maxDegree + 6 ∨
      3 * Fintype.card V + 7 * G.minDegree ≤ 4 * G.maxDegree + 10 ∨
      (3 * Fintype.card V + 7 * G.minDegree ≤ 4 * G.maxDegree + 17 ∧
        27 ≤ Fintype.card V + G.minDegree)) :
    Odd (Fintype.card V) ∧ G.maxDegree * (Fintype.card V / 2) < #G.edgeFinset ∧
      ∃ H : G.Subgraph, Odd H.verts.ncard ∧ 3 ≤ H.verts.ncard ∧
        G.maxDegree * (H.verts.ncard - 1) < 2 * H.edgeSet.ncard := by
  have hG : Overfull.IsDeltaCritical G := ⟨hconn, hclass, hcrit⟩
  have hov : G.maxDegree * (Fintype.card V / 2) < #G.edgeFinset := by
    rcases hcond with h | h | ⟨h, hn⟩
    · exact Overfull.overfull_of_critical_cc hG h
    · exact Overfull.overfull_of_critical hG h
    · exact Overfull.overfull_of_critical_ccjs hG h hn
  exact ⟨odd_card_of_overfull G hov, hov, exists_overfull_subgraph_of_overfull G hov⟩

end OverfullCriteria
