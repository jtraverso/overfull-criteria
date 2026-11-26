module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace OverfullWork.PrunedCore

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def neighboursIn (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (x : V) : ℕ :=
  ((G.neighborFinset x).filter fun y => y∈T).card

end OverfullWork.PrunedCore

namespace OverfullWork.KLOS

open PrunedCore
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Robust neighbours are taken inside `U`, with the threshold measured
relative to `|U|`. -/
noncomputable def robustNeighbourhoodIn (ν : ℝ) (U S : Finset V) : Finset V :=
  U.filter fun v => ν * (U.card : ℝ) ≤ (neighboursIn G S v : ℝ)

/-- Ordinary robust expansion on `U`, with the paper's normalization. -/
def ExpandsInside (ν τ : ℝ) (U : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ U → τ * (U.card : ℝ) ≤ (S.card : ℝ) →
    (S.card : ℝ) ≤ (1 - τ) * (U.card : ℝ) →
    (S.card : ℝ) + ν * (U.card : ℝ) ≤ ((robustNeighbourhoodIn G ν U S).card : ℝ)

end OverfullWork.KLOS

namespace SimpleGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Un **multigrafo lazo-libre** sobre `V`: una multiplicidad en cada par no
ordenado de vértices, nula en la diagonal (no hay lazos). -/
structure MultiGraph (V : Type*) where
  /-- Multiplicidad de cada par no ordenado. -/
  mult : Sym2 V → ℕ
  /-- No hay lazos. -/
  loopless : ∀ e : Sym2 V, e.IsDiag → mult e = 0

namespace MultiGraph

variable (M : MultiGraph V)

/-- Número de aristas de `M`, contadas con multiplicidad. -/
def edgeCount : ℕ := ∑ e : Sym2 V, M.mult e

/-- Grado de `v` en `M`: suma de multiplicidades de las aristas que lo tocan. -/
def degree (v : V) : ℕ :=
  ∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e), M.mult e

/-- `M` es `k`-regular. -/
def IsRegularOfDegree (k : ℕ) : Prop := ∀ v : V, M.degree v = k

/-- El multigrafo subyacente a un grafo simple. -/
def ofSimpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] : MultiGraph V where
  mult e := if e ∈ G.edgeSet then 1 else 0
  loopless e he := by
    have h : e ∉ G.edgeSet := fun hmem => G.not_isDiag_of_mem_edgeSet hmem he
    simp [h]


def restrict (M : MultiGraph V) (S : Finset V) : MultiGraph V where
  mult e := if e.toFinset ⊆ S then M.mult e else 0
  loopless e he := by
    split_ifs
    · exact M.loopless e he
    · rfl

def edgesWithin (M : MultiGraph V) (S : Finset V) : ℕ := (M.restrict S).edgeCount

def HasOverfullSubset (M : MultiGraph V) (D : ℕ) : Prop :=
  ∃ S : Finset V, D * (S.card / 2) < M.edgesWithin S

end MultiGraph
end SimpleGraph

namespace OverfullWork.ChenShan

universe u
open SimpleGraph Finset KLOS PrunedCore

def auxiliaryOrder (n k : ℕ) : ℕ :=
  max n (k + 1) + if (max n (k + 1)) % 2 = n % 2 then 0 else 1

/-- Chen–Shan, Lemma 3.23. Fix positive δ and τ. There are ν > 0 and a
size threshold such that a prescribed degree sequence on n labeled vertices
is realized by a simple robust (ν, τ)-expander whenever every degree is
between δn and n − 1, any two degrees differ by at most one, and the degree
sum is even. Robust expansion means that each set S of size between τn
and (1 − τ)n has at least |S| + νn vertices with at least νn neighbors
in S. The article takes δ < 1 and τ < 1/2. -/
theorem exists_robust_graph_with_prescribed_degrees
    (δ τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ N : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V],
      N ≤ Fintype.card V → ∀ degrees : V → ℕ,
      (∀ v, δ * (Fintype.card V : ℝ) ≤ (degrees v : ℝ)) →
      (∀ v, degrees v < Fintype.card V) →
      (∀ v w, degrees v ≤ degrees w + 1) →
      (∑ v, degrees v) % 2 = 0 →
      ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
        (∀ v, G.degree v = degrees v) ∧ ExpandsInside G ν τ univ := by
  sorry

open scoped Classical in
/-- Chen–Shan, Lemma 3.24. Fix 0 < α < 1 and 0 < τ < α/24.
For sufficiently large n, let L be a loopless multigraph on n vertices
with maximum degree at most k, where αn ≤ k ≤ 2n. Assume no set S
induces more than k floor(|S|/2) edges counted with multiplicity. Also
assume the total deficit s = ∑ᵥ (k − deg_L(v)) is at most εn² for
the positive ε supplied by the lemma. Take the least m ≥ max(n, k + 1)
of the same parity as n. The completion is k-regular, has even order
n + m, and contains L as the graph induced on the original vertices.
All edges added across the cut or among the m auxiliary vertices are
simple. The completion still has no k-overfull set. Its auxiliary
vertices induce a simple robust (ν, τ)-expander of minimum degree at
least k − ceil(s/m). -/
theorem exists_regular_auxiliary_completion
    (α τ : ℝ) (hα : 0 < α) (hαOne : α < 1) (hτ : 0 < τ) (hRange : τ < α / 24) :
    ∃ ν ε : ℝ, 0 < ν ∧ 0 < ε ∧ ∃ N : ℕ,
      ∀ {U : Type u} [Fintype U] [DecidableEq U] (L : MultiGraph U) (k : ℕ),
      let n := Fintype.card U
      N ≤ n → α * (n : ℝ) ≤ (k : ℝ) → k ≤ 2 * n →
      (∀ u, L.degree u ≤ k) → ¬ L.HasOverfullSubset k →
      let s := ∑ u, (k - L.degree u)
      (s : ℝ) ≤ ε * (n : ℝ) ^ 2 →
      let m := auxiliaryOrder n k
      let b := ⌈(s : ℝ) / (m : ℝ)⌉₊
      ∃ P : MultiGraph (U ⊕ Fin m), ∃ G : SimpleGraph (Fin m), ∃ _ : DecidableRel G.Adj,
        P.IsRegularOfDegree k ∧ Even (Fintype.card (U ⊕ Fin m)) ∧
        (∀ u v : U, P.mult s(.inl u, .inl v) = L.mult s(u, v)) ∧
        (∀ u : U, ∀ w : Fin m, P.mult s(.inl u, .inr w) ≤ 1) ∧
        (∀ w z : Fin m, P.mult s(.inr w, .inr z) = if G.Adj w z then 1 else 0) ∧
        ¬ P.HasOverfullSubset k ∧ (∀ w, k - b ≤ G.degree w) ∧ ExpandsInside G ν τ univ := by
  sorry

open scoped Classical in
/-- Simple-graph specialization following Chen–Shan, Lemma 3.24. If L
is simple and k < n, the least permissible auxiliary order is n. The
same hypotheses on α, τ, the maximum degree, the total deficit, and
the absence of a k-overfull set therefore give a simple k-regular
completion of order 2n. The original vertices induce L. The auxiliary
vertices induce a simple robust (ν, τ)-expander of minimum degree at
least k − ceil(s/n), and the completion has no k-overfull set. -/
theorem exists_simple_auxiliary_completion
    (α τ : ℝ) (hα : 0 < α) (hαOne : α < 1) (hτ : 0 < τ) (hRange : τ < α / 24) :
    ∃ ν ε : ℝ, 0 < ν ∧ 0 < ε ∧ ∃ N : ℕ,
      ∀ {U : Type u} [Fintype U] [DecidableEq U] (L : SimpleGraph U) [DecidableRel L.Adj] (k : ℕ),
      let n := Fintype.card U
      N ≤ n → α * (n : ℝ) ≤ (k : ℝ) → k < n →
      (∀ u, L.degree u ≤ k) → ¬ (MultiGraph.ofSimpleGraph L).HasOverfullSubset k →
      let s := ∑ u, (k - L.degree u)
      (s : ℝ) ≤ ε * (n : ℝ) ^ 2 →
      let b := ⌈(s : ℝ) / (n : ℝ)⌉₊
      ∃ R : SimpleGraph (U ⊕ Fin n), ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
        (∀ x, R.degree x = k) ∧
        (∀ u v : U, R.Adj (.inl u) (.inl v) ↔ L.Adj u v) ∧
        (∀ w z : Fin n, R.Adj (.inr w) (.inr z) ↔ G.Adj w z) ∧
        ¬ (MultiGraph.ofSimpleGraph R).HasOverfullSubset k ∧
        (∀ w, k - b ≤ G.degree w) ∧ ExpandsInside G ν τ univ := by
  sorry

end OverfullWork.ChenShan
