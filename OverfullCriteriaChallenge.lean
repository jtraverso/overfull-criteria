/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Overfull criteria for edge colouring

The overfull criteria proved in PALOMAR-2026-11-04-000016 (Plantholt 2004, with the
Chetwynd–Hilton 1985 1-factorization theorem at `6/7`) and PALOMAR-2026-11-04-000009
(Cao–Chen–Jing–Shan 2022 and Chen–Cao), in one vocabulary and with Mathlib definitions only.

* `class_two_iff_overfull_subgraph`: a graph of even order `n` with `12 n ≤ 7 (3δ − Δ)` is of
  class two iff it has a `Δ`-overfull subgraph.
* `critical_overfull`: a `Δ`-critical graph satisfying any of the three conditions of
  Chen–Cao / CCJS has odd order, is overfull, and so has a `Δ`-overfull subgraph (itself).
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
  sorry

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
  sorry

end OverfullCriteria
