module

public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

section Absorber

universe uA uB uW uV

abbrev TripartiteVertex (A : Type uA) (B : Type uB) (W : Type uW) := A ⊕ (B ⊕ W)

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

def FootprintEdge {V : Type uV} (Q Z : Finset V) (u v : V) : Prop :=
  (u ∈ Q ∧ (v ∈ Q ∨ v ∈ Z)) ∨ (v ∈ Q ∧ (u ∈ Q ∨ u ∈ Z))

variable [Fintype A] [Fintype B] [Fintype W]

/-- For Chen–Shan, Lemma 4.6, the first core part has size m and the third part
has size at least γm. The core pair has minimum degree at least (1/2+η)m on
both sides, and the other two pairs have at most εm missing neighbors per
vertex. Given a terminal set U of at most h vertices inside a small forbidden
set Z, the explicit bounds on ε, Z, and m give an absorber supported on U
and a new set Q disjoint from Z. The absorber has a triangle decomposition
on its own and after adjoining any locally balanced subgraph of the host
supported on U. Both its edge count and its new vertex count are included
in the stated bound. -/
theorem exists_universal_tripartite_absorber
    (AB : A → B → Prop) (AW : A → W → Prop) (BW : B → W → Prop)
    (U Z : Finset (TripartiteVertex A B W)) (h : ℕ) (m η γ ε : ℝ)
    (hm : 0 < m) (hη : 0 < η) (hγ : 0 < γ)
    (hSizeA : (Fintype.card A : ℝ) = m)
    (hSizeW : γ*m ≤ (Fintype.card W : ℝ))
    (hDegreeA : ∀ a, (1/2+η)*m ≤ ((univ.filter (AB a) : Finset B).card : ℝ))
    (hDegreeB : ∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => AB a b) : Finset A).card : ℝ))
    (hAW : ∀ a, ((univ.filter (fun z => ¬ AW a z) : Finset W).card : ℝ) ≤ ε*m)
    (hBW : ∀ b, ((univ.filter (fun z => ¬ BW b z) : Finset W).card : ℝ) ≤ ε*m)
    (hWA : ∀ z, ((univ.filter (fun a => ¬ AW a z) : Finset A).card : ℝ) ≤ ε*m)
    (hWB : ∀ z, ((univ.filter (fun b => ¬ BW b z) : Finset B).card : ℝ) ≤ ε*m)
    (hε : 0 ≤ ε) (hEps : ε ≤ η/32) (hEpsCycles : (h : ℝ)*ε ≤ γ/16)
    (hUZ : U ⊆ Z) (hU : U.card ≤ h) (hZ : (Z.card : ℝ) ≤ min η γ*m/16)
    (hRoom : ((4*(h*h)*2^(h*h) : ℕ) : ℝ) ≤ min η γ*m/16) :
    ∃ (Q : Finset (TripartiteVertex A B W))
      (E : A → B → Prop) (l : A → W → Prop) (r : B → W → Prop),
      Disjoint Q Z ∧
      tripartiteArcs E l r ⊆ tripartiteArcs AB AW BW ∧
      (∀ e ∈ tripartiteArcs E l r, FootprintEdge Q U e.1 e.2) ∧
      (tripartiteArcs E l r).card + Q.card ≤ 4*(h*h)*2^(h*h) ∧
      Nonempty (TripartiteTriangleDecomposition E l r) ∧
      ∀ (L : A → B → Prop) (lL : A → W → Prop) (rL : B → W → Prop),
        tripartiteArcs L lL rL ⊆ tripartiteArcs AB AW BW →
        tripartiteArcs L lL rL ⊆ U ×ˢ U → TripartiteLocallyBalanced L lL rL →
        Nonempty (TripartiteTriangleDecomposition
          (fun a b => E a b ∨ L a b) (fun a w => l a w ∨ lL a w)
          (fun b w => r b w ∨ rL b w)) := by
  sorry

end Absorber

section SignedWeights

open scoped BigOperators

universe uA uB

variable {A : Type uA} {B : Type uB} [Fintype A] [Fintype B]

/-- Chen–Shan, Lemma 4.7. In a bipartite graph with two n-vertex parts and
minimum degree at least n/2+gap on both sides, prescribe real incident weight
sums on the two parts, with equal totals and each sum of absolute value at
most d. Supported signed weights realize all these sums, with absolute value
at most d/gap on each edge. -/
theorem exists_bounded_signed_edge_weights
    (E : A → B → Prop) (r : A → ℝ) (s : B → ℝ) (n : ℕ) (gap d : ℝ)
    (hGap : 0 < gap) (hd : 0 ≤ d) (hSizeA : Fintype.card A = n) (hSizeB : Fintype.card B = n)
    (hA : ∀ a, (n : ℝ)/2+gap ≤ ((univ.filter (E a)).card : ℝ))
    (hB : ∀ b, (n : ℝ)/2+gap ≤ ((univ.filter (fun a => E a b)).card : ℝ))
    (hBalance : (∑ a, r a) = ∑ b, s b)
    (hr : ∀ a, |r a| ≤ d) (hs : ∀ b, |s b| ≤ d) :
    ∃ z : A → B → ℝ,
      (∀ a, (∑ b, z a b) = r a) ∧ (∀ b, (∑ a, z a b) = s b) ∧
      (∀ a b, |z a b| ≤ d/gap) ∧ (∀ a b, ¬ E a b → z a b = 0) := by
  sorry

end SignedWeights

section FractionalDecomposition

open scoped BigOperators

universe uA uB uW

variable {A : Type uA} {B : Type uB} {W : Type uW}

structure TripartiteEdgeWeights (A : Type uA) (B : Type uB) (W : Type uW) where
  ab : A → B → ℝ
  aw : A → W → ℝ
  bw : B → W → ℝ

def TriangleSupported (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (p : A → B → W → ℝ) : Prop :=
  ∀ a b w, ¬ (E a b ∧ L a w ∧ R b w) → p a b w = 0

def triangleBoundary [Fintype A] [Fintype B] [Fintype W]
    (p : A → B → W → ℝ) : TripartiteEdgeWeights A B W :=
  ⟨fun a b => ∑ w, p a b w, fun a w => ∑ b, p a b w, fun b w => ∑ a, p a b w⟩

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

noncomputable def edgeOnes (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop) :
    TripartiteEdgeWeights A B W :=
  ⟨fun a b => if E a b then 1 else 0, fun a w => if L a w then 1 else 0,
   fun b w => if R b w then 1 else 0⟩

variable [Fintype A] [Fintype B] [Fintype W]

variable {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}

def BoundedFractionalTriangleDecomposition (E : A → B → Prop)
    (L : A → W → Prop) (R : B → W → Prop) : Prop :=
  ∃ ω : A → B → W → ℝ, TriangleSupported E L R ω ∧
    triangleBoundary ω = edgeOnes E L R ∧
    ∀ a b w, E a b → L a w → R b w →
      1/(2*(Fintype.card W : ℝ)) ≤ ω a b w ∧ ω a b w ≤ 3/(2*(Fintype.card W : ℝ))

/-- Chen–Shan, Lemma 4.8. The two core parts have size m, each core vertex
has at least (1/2+η)m neighbors across the core pair, and each of the two
pairs meeting W misses at most εm neighbors at either endpoint. Every vertex
has equal degrees into its two opposite parts. For 0 < η < 1/2 and ε below
a positive threshold, supported triangle weights give total weight one on
every edge. Each existing triangle has weight between 1/(2|W|) and 3/(2|W|). -/
theorem exists_bounded_fractional_triangle_decomposition (η : ℝ)
    (hη : 0 < η) (hηhalf : η < 1/2) :
    ∃ ε₀ > 0, ∀ (m : ℕ) (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      DenseTripartite E L R m η ε → BoundedFractionalTriangleDecomposition E L R := by
  sorry

end FractionalDecomposition

section MatchingRetention

open SimpleGraph
open scoped Classical

universe uV uI

variable {V : Type uV} {I : Type uI}

/-- Chen–Shan, Lemma 5.22. A finite graph has a perfect matching and at most
four disjoint core cliques. Each clique has more than 2|X|+4 vertices,
and every vertex in the exceptional complement X has more than 2|X|+4
neighbors in the core. Given a matching consisting of exceptional–core
edges, some perfect matching retains all but at most 135720 of its edges. -/
theorem exists_perfect_matching_retaining_exceptional_core_edges
    [Finite V] [Fintype I] (G : SimpleGraph V)
    (K : I → Set V) (X : Set V) (hX : X = (⋃ i, K i)ᶜ)
    (hFour : Fintype.card I ≤ 4)
    (hDis : ∀ i j : I, i ≠ j → ∀ v : V, v ∈ K i → v ∉ K j) (hCliques : ∀ i, G.IsClique (K i))
    (hCoreSize : ∀ i, 2*X.ncard+4 < (K i).ncard)
    (hNeighbors : ∀ v ∈ X, 2*X.ncard+4 < (G.neighborSet v ∩ ⋃ i, K i).ncard)
    (hPerfect : ∃ M : G.Subgraph, M.IsPerfectMatching)
    (M : G.Subgraph) (hM : M.IsMatching)
    (hAcross : ∀ v w, M.Adj v w → (v ∈ X ↔ w ∉ X)) :
    ∃ P : G.Subgraph, P.IsPerfectMatching ∧ (M.edgeSet \ P.edgeSet).ncard ≤ 135720 := by
  sorry

end MatchingRetention


section TriangleHypergraph

variable {A B W : Type*}

abbrev OrientedTripartiteEdge (A B W : Type*) :=
  TripartiteVertex A B W × TripartiteVertex A B W

/-- A triangle as three vertices of the associated hypergraph. Each
vertex of that hypergraph represents one oriented graph edge. -/
noncomputable def triangleEdges (t : A × B × W) : Finset (OrientedTripartiteEdge A B W) :=
  {(.inl t.1,.inr (.inl t.2.1)),(.inr (.inl t.2.1),.inr (.inr t.2.2)),(.inr (.inr t.2.2),.inl t.1)}

theorem triangleEdges_card (t : A × B × W) : (triangleEdges t).card = 3 := by
  classical
  simp [triangleEdges,Finset.card_insert_of_notMem]

/-- Two distinct graph edges determine at most one tripartite triangle. -/
theorem triangle_eq_of_two_edges {t u : A × B × W}
    {e f : OrientedTripartiteEdge A B W} (hef : e ≠ f)
    (he : e ∈ triangleEdges t) (hf : f ∈ triangleEdges t)
    (he' : e ∈ triangleEdges u) (hf' : f ∈ triangleEdges u) : t = u := by
  classical
  rcases t with ⟨a,b,w⟩
  rcases u with ⟨a',b',w'⟩
  simp only [triangleEdges,mem_insert,mem_singleton] at he hf
  rcases he with rfl | rfl | rfl <;>
    rcases hf with rfl | rfl | rfl <;>
    simp_all [triangleEdges]

theorem triangleEdges_injective : Function.Injective (triangleEdges : A × B × W → _) := by
  intro t u h
  let e : OrientedTripartiteEdge A B W := (.inl t.1,.inr (.inl t.2.1))
  let f : OrientedTripartiteEdge A B W := (.inr (.inl t.2.1),.inr (.inr t.2.2))
  have hef : e ≠ f := by simp [e,f]
  have he : e ∈ triangleEdges t := by simp [e,triangleEdges]
  have hf : f ∈ triangleEdges t := by simp [f,triangleEdges]
  exact triangle_eq_of_two_edges hef he hf (h ▸ he) (h ▸ hf)

noncomputable def triangleHypergraph (T : Finset (A × B × W)) :
    Finset (Finset (OrientedTripartiteEdge A B W)) :=
  T.map ⟨triangleEdges,triangleEdges_injective⟩

variable [Fintype A] [Fintype B] [Fintype W]

noncomputable def supportedTriangles (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop) :
    Finset (A × B × W) :=
  univ.filter (fun t => E t.1 t.2.1 ∧ L t.1 t.2.2 ∧ R t.2.1 t.2.2)

end TriangleHypergraph

section PackingLeave

variable {V : Type*}

def ArcBalanced (E : Finset (V × V)) : Prop :=
  ∀ v, (E.filter (fun e => e.1 = v)).card = (E.filter (fun e => e.2 = v)).card

noncomputable def incidentDegree (G : Finset (V × V)) (v : V) : ℕ :=
  (G.filter (fun e => e.1 = v ∨ e.2 = v)).card

noncomputable def coveredEdges (M : Finset (Finset (V × V))) : Finset (V × V) :=
  M.biUnion id

noncomputable def packingLeave (G : Finset (V × V)) (M : Finset (Finset (V × V))) :
    Finset (V × V) :=
  G \ coveredEdges M

end PackingLeave

section TrianglePacking

universe uA uB uW

/-- Chen–Shan, Lemma 4.10. For fixed 0 < η < 1/2 and positive ζ, take a
sufficiently large locally balanced tripartite graph with two core parts of
size m. Its core pair has minimum degree at least (1/2+η)m and each other
pair misses at most εm neighbors per vertex for sufficiently small ε.
There is an edge-disjoint triangle packing whose uncovered graph still
has equal degrees into the two opposite parts at each vertex and has
maximum degree at most ζm. -/
theorem exists_triangle_packing_with_small_balanced_leave (η ζ : ℝ)
    (hη : 0 < η) (hηhalf : η < 1/2) (hζ : 0 < ζ) :
    ∃ ε₀ : ℝ, ∃ m₀ : ℕ, 0 < ε₀ ∧ ∀ (m : ℕ), m₀ ≤ m →
    ∀ (A : Type uA) (B : Type uB) (W : Type uW) [Fintype A] [Fintype B] [Fintype W]
      (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop) (ε : ℝ),
      0 ≤ ε → ε ≤ ε₀ → DenseTripartite E L R m η ε →
      ∃ T ⊆ supportedTriangles E L R,
        (↑(triangleHypergraph T) : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
        ArcBalanced (packingLeave (tripartiteArcs E L R) (triangleHypergraph T)) ∧
        ∀ v, (incidentDegree (packingLeave (tripartiteArcs E L R) (triangleHypergraph T)) v : ℝ)
          ≤ ζ * m := by
  sorry

end TrianglePacking

end OverfullWork.ChenShan

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
