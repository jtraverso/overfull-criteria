module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real
open scoped Classical BigOperators

section RectangularWeights

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Chen–Shan, Lemma 4.11. In a bipartite graph with minimum degree
at least c times the opposite shore size, where c > 1/2, any two sets of
signed margins with the same total admit a signed assignment supported
on the edges. Each prescribed margin has magnitude at most θ times
the opposite shore size. Each edge weight has magnitude at most
2θ/(2c − 1). -/
theorem exists_bounded_rectangular_signed_edge_weights
    (E : A → B → Prop) (r : A → ℝ) (s : B → ℝ) (c θ : ℝ)
    (hc : 1/2 < c) (hθ : 0 ≤ θ)
    (hA : ∀ a, c * (Fintype.card B : ℝ) ≤ ((univ.filter (E a)).card : ℝ))
    (hB : ∀ b, c * (Fintype.card A : ℝ) ≤ ((univ.filter (fun a => E a b)).card : ℝ))
    (hBalance : (∑ a, r a) = ∑ b, s b)
    (hr : ∀ a, |r a| ≤ θ * Fintype.card B) (hs : ∀ b, |s b| ≤ θ * Fintype.card A) :
    ∃ q : A → B → ℝ,
      (∀ a, (∑ b, q a b) = r a) ∧ (∀ b, (∑ a, q a b) = s b) ∧
      (∀ a b, |q a b| ≤ 2*θ/(2*c-1)) ∧ (∀ a b, ¬ E a b → q a b = 0) := by
  sorry

end RectangularWeights

section ReserveDegrees

variable {J : Type*} [Fintype J] {V : J → Type*} [∀ i, Fintype (V i)]

noncomputable def reserveOutDegree {A B : Type*} [Fintype B] (E : A → B → Prop)
    (a : A) : ℝ :=
  (univ.filter (E a)).card

noncomputable def reserveInDegree {A B : Type*} [Fintype A] (E : A → B → Prop)
    (b : B) : ℝ :=
  (univ.filter (fun a => E a b)).card

noncomputable def reservePairSize {A B : Type*} [Fintype A] [Fintype B] (E : A → B → Prop) : ℝ :=
  ∑ a, reserveOutDegree E a

end ReserveDegrees

section ReserveProbabilities

variable {J : Type*} [Fintype J] {V : J → Type*} [∀ i, Fintype (V i)]

/-- Chen–Shan, Lemma 4.12. The consecutive pairs of a directed
cycle of classes have minimum degree at least a c fraction of the opposite
class in each direction, with c > 1/2. Their edge counts are within relative
error θ of one positive count. At each vertex the indegree and outdegree
differ by at most θ times the smaller degree. Under the displayed smallness
conditions on θ and μ, there are sampling probabilities within
8μθ/(2c − 1) of μ on every edge. Expected indegree and outdegree agree
at each vertex, and the expected edge count is common across all pairs.
The formulation uses a permutation of the classes. -/
theorem exists_balanced_reserve_probabilities [Nonempty J]
    (next : J ≃ J) (E : (i j : J) → V i → V j → Prop)
    (c θ μ e : ℝ) (hc : 1/2 < c) (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1/4)
    (hθtight : (8/(2*c-1))*θ < 1/2) (hμ : 0 < μ) (hμupper : μ < 1/4) (he : 0 < e)
    (hOut : ∀ i a, c * (Fintype.card (V (next i)) : ℝ) ≤ reserveOutDegree (E i (next i)) a)
    (hIn : ∀ i b, c * (Fintype.card (V i) : ℝ) ≤ reserveInDegree (E i (next i)) b)
    (hSizes : ∀ i, |reservePairSize (E i (next i))-e| ≤ θ*e)
    (hBalance : ∀ i a, let out := reserveOutDegree (E i (next i)) a
      let in' := reserveInDegree (E (next.symm i) i) a
      |out-in'| ≤ θ * min out in') :
    ∃ p : (i : J) → V i → V (next i) → ℝ,
      (∀ i a b, ¬ E i (next i) a b → p i a b = 0) ∧
      (∀ i a b, E i (next i) a b →
        p i a b ∈ Set.Ioo (0 : ℝ) 1 ∧ |p i a b-μ| ≤ μ*((8/(2*c-1))*θ)) ∧
      (∀ i (a : V (next i)), (∑ b, p (next i) a b) = ∑ b, p i b a) ∧
      ∀ i, (∑ a, ∑ b, p i a b) =
        μ * (∑ j, reservePairSize (E j (next j))) / Fintype.card J := by
  sorry

end ReserveProbabilities

section TripartiteArcs

universe uA uB uW

variable {A : Type uA} {B : Type uB} {W : Type uW}

def tripartiteArc (E : A → B → Prop) (l : A → W → Prop) (r : B → W → Prop) :
    A ⊕ (B ⊕ W) → A ⊕ (B ⊕ W) → Prop
  | .inl a, .inr (.inl b) => E a b
  | .inr (.inl b), .inr (.inr w) => r b w
  | .inr (.inr w), .inl a => l a w
  | _, _ => False

noncomputable def tripartiteArcs [Fintype A] [Fintype B] [Fintype W]
    (E : A → B → Prop) (l : A → W → Prop) (r : B → W → Prop) :
    Finset ((A ⊕ (B ⊕ W)) × (A ⊕ (B ⊕ W))) :=
  univ.filter (fun e => tripartiteArc E l r e.1 e.2)

end TripartiteArcs

section ArcCounts

variable {V : Type*}

def ArcBalanced (E : Finset (V × V)) : Prop :=
  ∀ v, (E.filter (fun e => e.1 = v)).card = (E.filter (fun e => e.2 = v)).card

noncomputable def incidentDegree (G : Finset (V × V)) (v : V) : ℕ :=
  (G.filter (fun e => e.1 = v ∨ e.2 = v)).card

noncomputable def arcDivergence (G : Finset (V × V)) (v : V) : ℤ :=
  ((G.filter (fun e => e.1 = v)).card : ℤ) - (G.filter (fun e => e.2 = v)).card

end ArcCounts

section BalancedDeletion

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

/-- Chen–Shan, Lemma 4.13. For a cyclically oriented dense
tripartite graph with two equal core classes, the core pair has minimum
degree exceeding half the core size by a fixed positive fraction. The
color pairs have few missing neighbors and each vertex has imbalance
at most ξ times the core size. For sufficiently small parameters a set
of arcs can be deleted so that indegree and outdegree agree everywhere.
The deleted subgraph has maximum incident degree at most 5√ξ times
the core size. -/
theorem exists_tripartite_balancing_deletion
    (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (n : ℕ) (η ξ : ℝ) (hη : 0 < η) (hξ : 0 ≤ ξ)
    (hSmall : Real.sqrt ξ ≤ min (η/32) (1/128))
    (hA : Fintype.card A = n) (hB : Fintype.card B = n)
    (hW : (n : ℝ)/2 ≤ Fintype.card W ∧ (Fintype.card W : ℝ) ≤ 2*n)
    (hAB : ∀ a, (1/2+η)*n ≤ ((univ.filter (E a)).card : ℝ))
    (hBA : ∀ b, (1/2+η)*n ≤ ((univ.filter (fun a => E a b)).card : ℝ))
    (hAW : ∀ a, ((univ.filter (fun w => ¬ L a w)).card : ℝ) ≤ (n : ℝ)/16)
    (hBW : ∀ b, ((univ.filter (fun w => ¬ R b w)).card : ℝ) ≤ (n : ℝ)/16)
    (hWA : ∀ w, ((univ.filter (fun a => ¬ L a w)).card : ℝ) ≤ (n : ℝ)/16)
    (hWB : ∀ w, ((univ.filter (fun b => ¬ R b w)).card : ℝ) ≤ (n : ℝ)/16)
    (hImbalance : ∀ v, |(arcDivergence (tripartiteArcs E L R) v : ℝ)| ≤ ξ*n) :
    ∃ D ⊆ tripartiteArcs E L R, ArcBalanced (tripartiteArcs E L R \ D) ∧
      ∀ v, (incidentDegree D v : ℝ) ≤ 5*Real.sqrt ξ*n := by
  sorry

end BalancedDeletion

section MatchingEncoding

variable {V : Type*}

noncomputable def matchingArcs {X Y : Finset V} (f : X ≃ Y) : Finset (V × V) :=
  (univ : Finset X).biUnion fun x => {(x.1,(f x).1),((f x).1,x.1)}

end MatchingEncoding

section MatchingPacking

/-- Chen–Shan, Lemma 4.14, using Barber, Kühn, Lo, Osthus,
and Taylor. Each of at most 3bn requests consists of two disjoint equal shores.
Each associated graph has minimum degree at least half the opposite shore
size plus 81bλ^(3/2)n. Distinct requests share at most 6λ²n vertices and
a vertex belongs to at most 2bλn requests. In an ambient set of at most
3n vertices, the graphs admit pairwise edge-disjoint perfect matchings
for sufficiently large n. -/
theorem exists_bklot_bipartite_matching_packing (b : ℕ) (hb : 0 < b) (density : ℝ)
    (hDensity : 0 < density) (_hDensityAtMostOne : density ≤ 1) :
    ∃ n₀ : ℕ, ∀ (n q : ℕ), n₀ ≤ n → q ≤ 3*b*n →
      ∀ (V : Type*) [Fintype V] (E : V → V → Prop) (X Y : ℕ → Finset V),
      Fintype.card V ≤ 3*n →
      (∀ i < q, (X i).card = (Y i).card) →
      (∀ i < q, Disjoint (X i) (Y i)) →
      (∀ i < q, ∀ a ∈ X i, ((Y i).card : ℝ)/2 + 81*b*density^(3/2:ℝ)*n ≤ ((Y i).filter (E a)).card) →
      (∀ i < q, ∀ a ∈ Y i, ((X i).card : ℝ)/2 + 81*b*density^(3/2:ℝ)*n ≤
        ((X i).filter (fun v => E v a)).card) →
      (∀ i < q, ∀ j < q, i ≠ j →
        (((X i ∪ Y i) ∩ (X j ∪ Y j)).card : ℝ) ≤ 6*density^2*n) →
      (∀ v, (((range q).filter (fun j => v ∈ X j ∪ Y j)).card : ℝ) ≤ 2*b*density*n) →
      ∃ M : ℕ → Finset (V × V),
        (∀ i < q, ∃ f : ↥(X i) ≃ ↥(Y i),
          M i = matchingArcs f ∧ ∀ a : X i, E a (f a)) ∧
        ∀ i < q, ∀ j < q, i ≠ j → Disjoint (M i) (M j) := by
  sorry

end MatchingPacking

end OverfullWork.ChenShan
