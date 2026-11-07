# Overfull criteria for edge colouring, unified (Lean 4)

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A thin wrapper. It restates, in one vocabulary and with Mathlib definitions only, the overfull
criteria proved in two registered Palomar entries:

* PALOMAR-2026-11-04-000016 v2, [plantholt-overfull-criterion](https://github.com/jtraverso/plantholt-overfull-criterion) @ f890094: Plantholt 2004, Theorem 1.2, with Chetwynd–Hilton's `6/7`.
* PALOMAR-2026-11-04-000009 v2, [overfull-critical-graphs](https://github.com/jtraverso/overfull-critical-graphs) @ b85da9a: Cao–Chen–Jing–Shan 2022, Theorem 1.2, and Chen–Cao, Theorem 1.3. This one comes in as a dependency of the Plantholt entry.

Both are pinned lake dependencies, and no code is copied from them.

## Statements (`OverfullCriteriaChallenge.lean`, namespace `OverfullCriteria`)

```lean
theorem class_two_iff_overfull_subgraph {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hev : Even (Fintype.card V))
    (hdeg : 12 * Fintype.card V ≤ 7 * (3 * G.minDegree - G.maxDegree)) :
    ¬ G.lineGraph.Colorable G.maxDegree ↔
      ∃ H : G.Subgraph, Odd H.verts.ncard ∧ 3 ≤ H.verts.ncard ∧
        G.maxDegree * (H.verts.ncard - 1) < 2 * H.edgeSet.ncard

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
        G.maxDegree * (H.verts.ncard - 1) < 2 * H.edgeSet.ncard
```

The only new proof is in `OverfullCriteria/Basic.lean`. It shows by degree sum that an overfull
graph has odd order at least 3, and that such a graph is a `Δ`-overfull subgraph of itself.

## Building

Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3`:

```
lake exe cache get
lake build
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
