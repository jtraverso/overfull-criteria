# Robust expanders in Lean

This package groups four results used in a larger formalization of the overfull criterion.

| Result | Entry point |
|---|---|
| Robust fixed-size vertex sampling, with parameter ν⁶/2⁶⁰ and failure probability at most 1/n² | `robust_vertex_sampling_explicit` |
| Hamiltonicity of sufficiently large robust outexpanders with linear minimum semidegree | `exists_hamilton_threshold` |
| Vertex-disjoint spanning linkage for prescribed endpoint pairs | `cms_lemma_3_15` |
| Edge-disjoint spanning realizations of layouts in a simple almost regular host, with a robust remainder | `cms_lemma_3_14` |

`Challenge.lean` states the results using Mathlib and local definitions of
the objects under comparison. `Solution.lean` imports the four proved
endpoints. Sources and parameter conventions are recorded in
`formalization.yaml`.

Build the solution with `lake build Solution`. Run
`lake env lean Audit.lean` to inspect the solution axioms.
