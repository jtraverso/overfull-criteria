# Towards the Overfull Conjecture II in Lean

This package verifies the two main theorems of Guantao Chen, Jessica McDonald,
and Songling Shan, [Towards the Overfull Conjecture II, v1](https://arxiv.org/abs/2607.02270).

| Result | Verified statement |
| --- | --- |
| [Theorem 1.3](OverfullWork/CMSTheorem13.lean) | For sufficiently large robust expanders of linear maximum degree with weak Vizing adjacency and few large-deficit vertices, a proper edge coloring with `Δ` colors exists exactly when there is no `Δ`-overfull subgraph. |
| [Theorem 1.4](OverfullWork/CMSTheorem14.lean) | For each fixed `ε > 0`, the same criterion holds for all sufficiently large simple graphs with `Δ ≥ (1 + ε)n/2`. |

An induced subgraph on `s` vertices is `Δ`-overfull when its edge count
exceeds `Δ ⌊s/2⌋`, where `Δ` is the maximum degree of the ambient graph.
Each color class is a matching, so this edge count precludes a proper
`Δ`-edge-coloring.

The proof of 1.3 uses the two stopping cases of the trimming operation and the
[canonical completion criterion of Theorem 4.2](OverfullWork/CMSCanonicalTheorem42.lean).
The proof of 1.4 uses Vizing adjacency and the critical average-degree bound to
apply 1.3 after extracting a critical subgraph with the same maximum degree.
The [formalization metadata](formalization.yaml) records the quantitative and
existential forms of supporting results used in the proofs.

## Verify

Use the Lean version in `lean-toolchain`.

```sh
lake exe cache get
lake build Challenge Solution
lake env lean Audit.lean
lake comparator --config comparator.cms-ii.json
```

[Challenge.lean](Challenge.lean) independently states both main results and
their defining predicates. [Solution.lean](Solution.lean) imports the verified
proofs. The Comparator configuration compares both conclusions and their
defining predicates, with the Lean and NanoDa kernel checks enabled.

The formalization reuses the source development for the
[robust-expander package](https://github.com/jtraverso/overfull-criteria/tree/ce7f10c99acd753956f214fa93f1b9f48ecba654).
The manuscript states the full Overfull Conjecture for `Δ > n/3` as
Conjecture 1.1. This package proves the article's partial results.
