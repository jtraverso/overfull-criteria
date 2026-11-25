# The robust component structure of dense regular graphs in Lean

This package formalizes [Theorem 3.1 of Kühn, Lo, Osthus, and Staden](https://arxiv.org/abs/1401.0424).
Every sufficiently large dense regular graph has a partition into ordinary
and bipartite robust expander components satisfying conditions (D1)–(D7).
The finite refinement schedule fixes a common order threshold before the graph is chosen.

- [KLOSChallenge.lean](KLOSChallenge.lean) states the theorem and its defining predicates.
- [KLOSSolution.lean](KLOSSolution.lean) imports the proof in
  [KLOSRobustPartition.lean](OverfullWork/KLOSRobustPartition.lean).
- [Formalization metadata](formalization.klos-theorem-3-1.yaml) records how the Lean statement
  represents the partition and its parameters.

Use the Lean version in `lean-toolchain`.

```sh
lake exe cache get
lake build KLOSChallenge KLOSSolution
lake comparator --config comparator.klos-theorem-3-1.json
```
