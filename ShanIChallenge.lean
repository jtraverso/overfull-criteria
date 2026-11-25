module

public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! Shan, Towards the Overfull Conjecture,
arXiv:2308.16808v4, Theorems 1.3 and 1.4. -/

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

namespace Overfull

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsClassTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ¬ G.lineGraph.Colorable G.maxDegree

def IsDeltaCritical (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ IsClassTwo G ∧
    ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).lineGraph.Colorable G.maxDegree

end Overfull

namespace OverfullWork.ShanI

open SimpleGraph

theorem shan_v4_theorem_1_3 (ε : ℝ) (hεpos : 0 < ε) (hε : ε ≤ 1/14) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      (1-ε)*(Fintype.card V : ℝ) ≤ (G.maxDegree : ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬ G.HasOverfullSubgraph) := by
  sorry

theorem shan_v4_theorem_1_4 :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      (13/14 : ℝ)*(Fintype.card V:ℝ) ≤ (G.maxDegree:ℝ) →
      Overfull.IsDeltaCritical G →
      (G.maxDegree:ℝ)-1+3/(Fintype.card V:ℝ) ≤
        (2*(G.edgeFinset.card:ℝ))/(Fintype.card V:ℝ) := by
  sorry

end OverfullWork.ShanI
