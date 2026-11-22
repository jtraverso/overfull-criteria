module

public import OverfullWork.OverfullPreservation

@[expose] public section


/-!
# Verified structural and arithmetic setup for a star-multigraph criterion

The published target is Shan, arXiv:2205.08564v2, Theorem 3.1(a).
This file proves only the star structure and the elementary degree bound
for epsilon=1/2; it does not assume or prove that factorization theorem.
-/

namespace SimpleGraph.MultiGraph

variable {V : Type*}

/-- All parallel edges, if any, are incident with the distinguished point. -/
def IsStarAt (M : MultiGraph V) (x : V) : Prop :=
  ∀ u v, u ≠ x → v ≠ x → M.mult s(u,v) ≤ 1

end SimpleGraph.MultiGraph

namespace OverfullWork.MultigraphExtension

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem pointExtension_isStarAt (G : SimpleGraph V) [DecidableRel G.Adj] :
    (pointExtension G).IsStarAt none := by
  intro u v hu hv
  cases u with
  | none => exact False.elim (hu rfl)
  | some u =>
    cases v with
    | none => exact False.elim (hv rfl)
    | some v =>
      rw [preserves_original]
      split_ifs <;> omega

omit [DecidableEq V] in
/-- With extended order 2m, the current density bound gives delta(G)>=5m/4
for m>=5, the old-vertex degree threshold in case (a) at epsilon=1/2. -/
theorem old_degree_bound_for_shan_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 5 ≤ m) (hcard : Fintype.card V + 1 = 2 * m)
    (hgap : G.maxDegree - G.minDegree ≤ 2)
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree) :
    5 * m ≤ 4 * G.minDegree := by omega

#print axioms pointExtension_isStarAt
#print axioms old_degree_bound_for_shan_half

end OverfullWork.MultigraphExtension
