# Robust expanders in Lean

This package groups seven results used in a larger formalization of the overfull criterion.

| Result | Entry point |
|---|---|
| Robust fixed-size vertex sampling, with parameter ν⁶/2⁶⁰ and failure probability at most 1/n² | `robust_vertex_sampling_explicit` |
| Hamiltonicity of sufficiently large robust outexpanders with linear minimum semidegree | `exists_hamilton_threshold` |
| Vertex-disjoint spanning linkage for prescribed endpoint pairs | `cms_lemma_3_15` |
| Edge-disjoint spanning realizations of layouts in a simple almost regular host, with a robust remainder | `cms_lemma_3_14` |
| Approximate Hamilton packing in a regular robust digraph | `osthus_staden_theorem_1_1_existence` |
| Exact Hamilton decomposition of a regular robust digraph | `kuhn_osthus_directed_decomposition` |
| Exact Hamilton decomposition of an even-regular robust graph | `cms_theorem_5_5` |

The decomposition entries prove existence. The polynomial-time assertions
in the cited papers are outside the scope of the comparator.

`Challenge.lean` states the results using Mathlib and local definitions of
the objects under comparison. `Solution.lean` imports the seven proved
endpoints. Sources and parameter conventions are recorded in
`formalization.yaml`. The Palomar configuration for this package is
`comparator.robust-expanders.json`.

Build the solution with `lake build Solution`. Run
`lake env lean Audit.lean` to inspect the solution axioms.
