module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Standalone statement of Kühn–Lo–Osthus–Staden, Theorem 3.1,
arXiv:1401.0424. -/

open Finset SimpleGraph
open scoped Classical

namespace OverfullWork.PrunedCore

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def neighboursIn (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (x : V) : ℕ :=
  ((G.neighborFinset x).filter fun y => y∈T).card

end OverfullWork.PrunedCore

namespace OverfullWork.OddCutDeficit

variable {V : Type*} [Fintype V] [DecidableEq V]

def internalEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset⊆S).card

def crossingEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (V×V) := (S×ˢSᶜ).filter fun p => G.Adj p.1 p.2

def cutEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (crossingEdges G S).card

end OverfullWork.OddCutDeficit

namespace OverfullWork.KLOS

open PrunedCore OddCutDeficit

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The size and boundary conditions for a `ρ`-component. -/
def IsSparseComponent (ρ : ℝ) (U : Finset V) : Prop :=
  Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (U.card : ℝ) ∧
    (cutEdges G U : ℝ) ≤ ρ * (Fintype.card V : ℝ) ^ 2

/-- Conditions (C1)–(C3), with the boundary expressed using disjoint edge
sets. The whole component is `A ∪ B`. -/
def CloseToBipartite (ρ : ℝ) (A B : Finset V) : Prop :=
  Disjoint A B ∧ Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (A.card : ℝ) ∧
    Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (B.card : ℝ) ∧
    |(A.card : ℝ) - (B.card : ℝ)| ≤ ρ * (Fintype.card V : ℝ) ∧
    (internalEdges G A : ℝ) + internalEdges G B + cutEdges G (A ∪ B) ≤
      ρ * (Fintype.card V : ℝ) ^ 2

/-- Robust neighbours are taken inside `U`, with the threshold measured
relative to `|U|`. -/
noncomputable def robustNeighbourhoodIn (ν : ℝ) (U S : Finset V) : Finset V :=
  U.filter fun v => ν * (U.card : ℝ) ≤ (neighboursIn G S v : ℝ)

/-- Ordinary robust expansion on `U`, with the paper's normalization. -/
def ExpandsInside (ν τ : ℝ) (U : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ U → τ * (U.card : ℝ) ≤ (S.card : ℝ) →
    (S.card : ℝ) ≤ (1 - τ) * (U.card : ℝ) →
    (S.card : ℝ) + ν * (U.card : ℝ) ≤ ((robustNeighbourhoodIn G ν U S).card : ℝ)

/-- Bipartite robust expansion with the range measured on the source
side and the threshold and surplus measured on both sides together. -/
def ExpandsAcross (ν τ : ℝ) (A B : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ A → τ * (A.card : ℝ) ≤ (S.card : ℝ) →
    (S.card : ℝ) ≤ (1 - τ) * (A.card : ℝ) →
    (S.card : ℝ) + ν * ((A ∪ B).card : ℝ) ≤
      (((robustNeighbourhoodIn G ν (A ∪ B) S) ∩ B).card : ℝ)

section Reassignment

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The part whose label is `i` in the assignment `f`. -/
def assignmentPart (f : V → I) (i : I) : Finset V := univ.filter (fun v => f v = i)

end Reassignment

/-- A robust partition satisfying (D1)–(D7). The fibers of the assignment
are the parts. The finite set of labels records which fibers are bipartite. -/
structure RobustPartition (D : ℕ) (r ν τ : ℝ) where
  labels : Finset (Finset V)
  assign : V → ↥labels
  bipartite : Finset ↥labels
  nonempty_part : ∀ i, (assignmentPart assign i).Nonempty
  ordinary : ∀ i ∉ bipartite, IsSparseComponent G r (assignmentPart assign i) ∧
    ExpandsInside G ν τ (assignmentPart assign i)
  bipartite_component : ∀ i ∈ bipartite, ∃ A B : Finset V, A ∪ B = assignmentPart assign i ∧
    CloseToBipartite G r A B ∧ ExpandsAcross G ν τ A B ∧
    (∀ v ∈ A, neighboursIn G A v ≤ neighboursIn G B v) ∧
    (∀ v ∈ B, neighboursIn G B v ≤ neighboursIn G A v)
  dominance : ∀ v j, neighboursIn G (assignmentPart assign j) v ≤
    neighboursIn G (assignmentPart assign (assign v)) v
  count : ((labels.card : ℝ) + (bipartite.card : ℝ)) * D ≤
    (1 + r ^ ((1 : ℝ) / 3)) * (Fintype.card V : ℝ)
  core : ∀ i, let W := assignmentPart assign i
    ((W.filter fun v => (neighboursIn G W v : ℝ) <
      (D : ℝ) - r * (Fintype.card V : ℝ)).card : ℝ) ≤ r * (Fintype.card V : ℝ)

universe u

theorem exists_robustPartition_regular (α τ : ℝ) (f : ℝ → ℝ)
    (hα : 0 < α) (hτ : 0 < τ)
    (hf : ∀ x : ℝ, 0 < x → x < 1 → 0 < f x) :
    ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
        (D : ℕ), n₀ ≤ Fintype.card W → (∀ v, H.degree v = D) →
        α * (Fintype.card W : ℝ) ≤ D →
        ∃ r ν : ℝ, 1 / (n₀ : ℝ) ≤ r ∧ r ≤ ν ∧ ν ≤ τ ∧ r ≤ f ν ∧
          1 / (n₀ : ℝ) ≤ f r ∧ Nonempty (RobustPartition H D r ν τ) := by
  sorry

end OverfullWork.KLOS
