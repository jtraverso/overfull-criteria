module

public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Real.Basic

@[expose] public section

/-! Chen–McDonald–Shan, Towards the Overfull Conjecture II,
arXiv:2607.02270v1, Theorems 1.3 and 1.4. -/

open Finset
open scoped Classical
universe u

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def EdgeColorable (n : ℕ) : Prop := G.lineGraph.Colorable n

def HasOverfullSubgraph : Prop :=
  ∃ s : Finset V, G.maxDegree * (s.card / 2) <
    (G.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card

end SimpleGraph

namespace OverfullWork.PrunedCore

open SimpleGraph
variable {V : Type u} [Fintype V] [DecidableEq V]

def neighboursIn (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (x : V) : ℕ :=
  ((G.neighborFinset x).filter fun y => y∈T).card

end OverfullWork.PrunedCore

namespace OverfullWork.RobustExpansion

open SimpleGraph PrunedCore
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def realNeighbourhood (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : ℝ) (S : Finset V) : Finset V :=
  univ.filter fun v=>ν*(Fintype.card V:ℝ)≤(neighboursIn G S v:ℝ)

def IsRealRobust (G : SimpleGraph V) [DecidableRel G.Adj] (ν τ : ℝ) : Prop :=
  ∀S : Finset V,τ*(Fintype.card V:ℝ)≤(S.card:ℝ) →
    (S.card:ℝ)≤(1-τ)*(Fintype.card V:ℝ) →
    (S.card:ℝ)+ν*(Fintype.card V:ℝ)≤((realNeighbourhood G ν S).card:ℝ)

end OverfullWork.RobustExpansion

namespace OverfullWork.CMSTrimmingRound

open SimpleGraph RobustExpansion

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def initialExceptionalSet (G : SimpleGraph V) [DecidableRel G.Adj] (η : ℝ) : Finset V :=
  univ.filter (fun v => η*(Fintype.card V:ℝ) < (G.maxDegree:ℝ)-G.degree v)

/-- The overfull criterion for robust expanders with weak VAL and a small
set of vertices of large deficit. -/
theorem cms_theorem_1_3 (α : ℝ) (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1/2 ∧ ∀ ν : ℝ, 0 < ν →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ηMax < 1 ∧ ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          let n := Fintype.card V
          N ≤ n → α*(n:ℝ) ≤ (G.maxDegree:ℝ) → IsRealRobust G ν τ →
          (∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) →
          (∃ η : ℝ,0 < η ∧ η ≤ ηMax ∧
            ((initialExceptionalSet G η).card:ℝ) ≤ η^2*(n:ℝ)) →
          (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  sorry

end OverfullWork.CMSTrimmingRound

namespace OverfullWork.Gate8J

open SimpleGraph

/-- The overfull criterion above half the graph order by a fixed margin. -/
theorem cms_theorem_1_4 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      ((1+ε)/2)*(Fintype.card V:ℝ) ≤ (G.maxDegree:ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  sorry

end OverfullWork.Gate8J
