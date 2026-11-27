module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Sym

@[expose] public section

open Finset
open scoped Classical

namespace SimpleGraph

universe u_2 in
structure MultiGraph (V : Type u_2) where
  /-- Multiplicidad de cada par no ordenado. -/
  mult : Sym2 V → ℕ
  /-- No hay lazos. -/
  loopless : ∀ e : Sym2 V, e.IsDiag → mult e = 0

namespace MultiGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (M : MultiGraph V)

def degree (v : V) : ℕ :=
  ∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e), M.mult e

structure EdgeColoring (k : ℕ) where
  /-- Número de copias de la arista `e` que reciben el color `i`. -/
  col : Sym2 V → Fin k → ℕ
  /-- Las copias de `e` suman su multiplicidad. -/
  sum_col : ∀ e : Sym2 V, ∑ i : Fin k, col e i = M.mult e
  /-- En cada vértice y color, a lo sumo una copia. -/
  proper : ∀ (v : V) (i : Fin k),
    ∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e), col e i ≤ 1

variable {M} in
def EdgeColoring.colourGraph {M : MultiGraph V} {k : ℕ} (C : M.EdgeColoring k)
    (i : Fin k) : MultiGraph V where
  mult e := C.col e i
  loopless _ he := by
    have h0 : ∑ j : Fin k, C.col _ j = 0 := (C.sum_col _).trans (M.loopless _ he)
    exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)

namespace GeneralCopies

abbrev Copies (M : MultiGraph V) := Σ e : Sym2 V, Fin (M.mult e)

end GeneralCopies
end MultiGraph
end SimpleGraph

namespace OverfullWork.ChenShan

open SimpleGraph
universe u

section Tripartite

universe uA uB uW

variable {A : Type uA} {B : Type uB} {W : Type uW}

structure TripartiteTriangleDecomposition (E : A → B → Prop) (left : A → W → Prop)
    (right : B → W → Prop) where
  triangle : A → B → W → Prop
  supported : ∀ a b w, triangle a b w → E a b ∧ left a w ∧ right b w
  coversBase : ∀ a b, E a b → ∃! w, triangle a b w
  coversLeft : ∀ a w, left a w → ∃! b, triangle a b w
  coversRight : ∀ b w, right b w → ∃! a, triangle a b w

def TripartiteLocallyBalanced [Fintype A] [Fintype B] [Fintype W]
    (E : A → B → Prop) (left : A → W → Prop) (right : B → W → Prop) : Prop :=
  (∀ a, Fintype.card {b // E a b} = Fintype.card {w // left a w}) ∧
  (∀ b, Fintype.card {a // E a b} = Fintype.card {w // right b w}) ∧
  ∀ w, Fintype.card {a // left a w} = Fintype.card {b // right b w}

structure DenseTripartite [Fintype A] [Fintype B] [Fintype W]
    (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (m : ℕ) (η ε : ℝ) : Prop where
  sizeA : Fintype.card A = m
  sizeB : Fintype.card B = m
  balanced : TripartiteLocallyBalanced E L R
  degreeA : ∀ a, (1/2 + η) * m ≤ (#(univ.filter (E a)) : ℝ)
  degreeB : ∀ b, (1/2 + η) * m ≤ (#(univ.filter (fun a => E a b)) : ℝ)
  missingAW : ∀ a, (#(univ.filter (fun w => ¬ L a w)) : ℝ) ≤ ε * m
  missingBW : ∀ b, (#(univ.filter (fun w => ¬ R b w)) : ℝ) ≤ ε * m
  missingWA : ∀ w, (#(univ.filter (fun a => ¬ L a w)) : ℝ) ≤ ε * m
  missingWB : ∀ w, (#(univ.filter (fun b => ¬ R b w)) : ℝ) ≤ ε * m

end Tripartite

section BalancedColoring

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

def sideCount (C : M.EdgeColoring k) (A : Finset V) (i : Fin k) : ℤ :=
  ∑ v ∈ A, ((C.colourGraph i).degree v : ℤ)

/-- **Chen–Shan, Lemma 3.9.** Start with a proper k-edge-coloring of a finite
loopless multigraph. Take two disjoint vertex sets A and B with equal degree
sums. Their complement has even size, and each of its vertices has degree k.
There is another proper coloring with the same palette in which every color
meets each outside vertex once and covers equally many vertices of A and B.
On each side the numbers covered by any two colors differ by at most two.
The theorem also gives a per-color upper bound, stated after multiplying
by k. -/
theorem exists_balanced_equitable_outside_coloring
    (C : M.EdgeColoring k) (A B : Finset V)
    (hAB : Disjoint A B) (hEven : Even ((A ∪ B)ᶜ.card))
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, M.degree v = k)
    (hDegrees : (∑ v ∈ A, M.degree v) = ∑ v ∈ B, M.degree v) :
    ∃ D : M.EdgeColoring k, (∀ i, sideCount D A i = sideCount D B i) ∧
      (∀ i j, sideCount D A i ≤ sideCount D A j + 2) ∧
      (∀ v ∈ (A ∪ B)ᶜ, ∀ i, (D.colourGraph i).degree v = 1) ∧
      (∀ i, (k : ℤ) * sideCount D A i ≤ (∑ v ∈ A, (M.degree v : ℤ)) + 2*k) := by
  sorry

end BalancedColoring

/-- **Chen–Shan, Theorem 4.15.** The two core parts A and B both have size m
and every core vertex has at least (1/2 + η)m neighbors in the other core
part. Each vertex has the same number of neighbors in its two opposite
parts. Each of the pairs between a core part and W misses at most εm neighbors
at each endpoint. For fixed positive η, sufficiently large m and sufficiently
small ε, the tripartite graph decomposes into triangles, with every edge
covered once. -/
theorem exists_triangle_decomposition_of_dense_tripartite
    (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, ∃ m₀ : ℕ, 0 < ε₀ ∧
      ∀ (m : ℕ), m₀ ≤ m → ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      ∀ (A B W : Type u) [Fintype A] [Fintype B] [Fintype W]
        (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop),
      DenseTripartite E P Q m η ε →
        Nonempty (TripartiteTriangleDecomposition E P Q) := by
  sorry

/-- **Chen–Shan, Theorem 4.16.** The uncolored edges form a simple bipartite
graph on two parts of size m with minimum degree at least (1/2 + η)m.
The other edge copies already have colors and the precoloring is proper.
The number of precolored copies at any vertex or in any one color is at most
ε₀m. The combined graph is regular of degree equal to the palette size.
For fixed positive η, sufficiently large m and a suitable ε₀, the given
precoloring extends so that each color is incident once at every vertex. -/
theorem exists_regular_bipartite_precoloring_extension (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, ∃ m₀ : ℕ, 0 < ε₀ ∧
      ∀ m : ℕ, m₀ ≤ m →
      ∀ (A B W X : Type u) [Fintype A] [Fintype B] [Fintype W] [Fintype X]
        (E : A → B → Prop) (l : X → A) (r : X → B) (d : X → W),
      Fintype.card A = m → Fintype.card B = m →
      Function.Injective (fun x => (l x,d x)) →
      Function.Injective (fun x => (r x,d x)) →
      (∀ a, Fintype.card {b // E a b} + Fintype.card {x // l x = a} = Fintype.card W) →
      (∀ b, Fintype.card {a // E a b} + Fintype.card {x // r x = b} = Fintype.card W) →
      (∀ a, (1/2+η)*m ≤ ((univ.filter (E a)).card : ℝ)) →
      (∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => E a b)).card : ℝ)) →
      (∀ a, (Fintype.card {x // l x = a} : ℝ) ≤ ε₀*m) →
      (∀ b, (Fintype.card {x // r x = b} : ℝ) ≤ ε₀*m) →
      (∀ w, (Fintype.card {x // d x = w} : ℝ) ≤ ε₀*m) →
      let H := {p : A × B // E p.1 p.2}
      ∃ c : H ⊕ X → W, (∀ x, c (.inr x) = d x) ∧
        (∀ a w, ∃! e : H ⊕ X, Sum.elim (fun p => p.val.1) l e = a ∧ c e = w) ∧
        (∀ b w, ∃! e : H ⊕ X, Sum.elim (fun p => p.val.2) r e = b ∧ c e = w) := by
  sorry

/-- **Chen–Shan, Theorem 4.2.** Add a loopless auxiliary multigraph M to a
simple bipartite core with two parts of size m and minimum degree at least
(1/2 + η)m. Each core vertex has total degree k and at most εm incidences
from M. The exceptional set has even size and each exceptional vertex has
degree k in M. The theorem assumes that M already has a proper k-edge-coloring.
For fixed positive η, sufficiently large m and a suitable ε, the combined
graph has a 1-factorization. The statement assigns k colors to the original
edge copies so that every vertex meets each color exactly once. -/
theorem exists_factorization_of_dense_bipartite_core (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, ∃ m₀ : ℕ, 0 < ε ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ k : ℕ,
      ∀ (A B Z : Type u) [Fintype A] [Fintype B] [Fintype Z]
        (E : A → B → Prop) (M : MultiGraph (A ⊕ (B ⊕ Z))),
      Fintype.card A = m → Fintype.card B = m → Even (Fintype.card Z) →
      (∀ a, (1/2+η)*m ≤ ((univ.filter (E a)).card : ℝ)) →
      (∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => E a b)).card : ℝ)) →
      (∀ a, Fintype.card {b // E a b} + M.degree (.inl a) = k) →
      (∀ b, Fintype.card {a // E a b} + M.degree (.inr (.inl b)) = k) →
      (∀ z, M.degree (.inr (.inr z)) = k) →
      (∀ a, (M.degree (.inl a) : ℝ) ≤ ε*m) →
      (∀ b, (M.degree (.inr (.inl b)) : ℝ) ≤ ε*m) →
      Nonempty (M.EdgeColoring k) →
      let H := {ab : A × B // E ab.1 ab.2}
      let X := MultiGraph.GeneralCopies.Copies M
      ∃ c : H ⊕ X → Fin k, ∀ v w, ∃! e : H ⊕ X,
        Sum.elim (fun h => Sum.inl h.val.1 = v ∨ .inr (.inl h.val.2) = v)
          (fun x => v ∈ x.1) e ∧ c e = w := by
  sorry

end OverfullWork.ChenShan
