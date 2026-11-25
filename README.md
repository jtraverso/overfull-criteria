# Shan's Towards the Overfull Conjecture in Lean

The package verifies [Songling Shan's Theorems 1.3 and 1.4 (arXiv v4)](https://arxiv.org/abs/2308.16808v4).

| Result | Verified statement |
| --- | --- |
| Theorem 1.3 | For each `0 < ε ≤ 1/14`, the overfull criterion holds for sufficiently large simple graphs with `Δ ≥ (1 − ε)n`. |
| Theorem 1.4 | A sufficiently large edge-chromatic critical graph with `Δ ≥ 13n/14` has average degree at least `Δ − 1 + 3/n`. |

The [Lean proof](OverfullWork/ShanI.lean) specializes the stronger criterion in Theorem 1.4 of [Chen–McDonald–Shan](https://arxiv.org/abs/2607.02270v1). Its Lean proof is registered as [PALOMAR-2026-11-24-000003](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-24-000003). For Shan's average-degree result, criticality forces the overfull set to be the whole vertex set and determines the edge count.

## Verification

```sh
lake exe cache get
lake build ShanIChallenge ShanISolution
lake env lean ShanIAudit.lean
lake comparator --config comparator.shan-i.json
```

[ShanIChallenge.lean](ShanIChallenge.lean) states the two theorems independently. The [Comparator configuration](comparator.shan-i.json) compares both theorem statements and the graph-coloring predicates they use.
