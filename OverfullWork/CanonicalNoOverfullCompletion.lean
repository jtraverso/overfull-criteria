module

public import OverfullWork.CanonicalRegularization
public import OverfullWork.CanonicalAdmissibility
public import OverfullWork.OddCutDeficit

@[expose] public section


/-! # Canonical completion with admissibility discharged by odd cuts

The ordered degrees are the coordinates of Definition 4.1. No parity,
balance, added graph or completion is assumed: these are obtained from
the original even no-overfull multigraph and the actual construction.
-/
namespace OverfullWork.CanonicalNoOverfullCompletion
open SimpleGraph Finset
open scoped Classical

theorem exists_completion_of_no_overfull {n : ℕ}
    (M : MultiGraph (Fin (n+1)×Bool)) (D : ℕ) (hD : ∀v,M.degree v≤D)
    (hpair : ∀i : Fin (n+1),M.degree (i,false)≤M.degree (i,true))
    (horder : ∀i j : Fin (n+1),i.val<j.val → M.degree (i,true)≤M.degree (j,false))
    (hno : ¬M.HasOverfullSubset D) : Nonempty (CanonicalRegularization.Completion M D) := by
  have hcard : Fintype.card (Fin (n+1)×Bool)=2*(n+1) := by
    simp [Nat.mul_comm]
  exact CanonicalRegularization.exists_completion M D hD hpair horder
    (CanonicalAdmissibility.deficit_even M D (n+1) hcard hD)
    (CanonicalAdmissibility.deficit_balanced M D (n+1) (by omega) hcard hD hno (0,false))

/-- The simple-graph interface uses exactly the original overfull
predicate. The result is a genuine regular multigraph completion. -/
theorem exists_simple_completion {n : ℕ} (G : SimpleGraph (Fin (n+1)×Bool))
    [DecidableRel G.Adj]
    (hpair : ∀i : Fin (n+1),G.degree (i,false)≤G.degree (i,true))
    (horder : ∀i j : Fin (n+1),i.val<j.val → G.degree (i,true)≤G.degree (j,false))
    (hno : ¬G.HasOverfullSubgraph) :
    Nonempty (CanonicalRegularization.Completion (MultiGraph.ofSimpleGraph G) G.maxDegree) := by
  apply exists_completion_of_no_overfull
  · intro v
    rw [MultiGraph.degree_ofSimpleGraph]
    exact G.degree_le_maxDegree v
  · simpa only [MultiGraph.degree_ofSimpleGraph] using hpair
  · simpa only [MultiGraph.degree_ofSimpleGraph] using horder
  · rintro ⟨S,hS⟩
    rw [←OddCutDeficit.internalEdges_eq_multigraph] at hS
    exact hno ⟨S,hS⟩

end OverfullWork.CanonicalNoOverfullCompletion
