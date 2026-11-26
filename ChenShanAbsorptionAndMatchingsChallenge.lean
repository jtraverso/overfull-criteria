module

public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Tutte

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

/-- The statement of Chen–Shan's universal tripartite absorber lemma. -/
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

/-- The statement of Chen–Shan's bounded signed edge weighting lemma. -/
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

/-- The statement of Chen–Shan's matching retention lemma. -/
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

/-- Chen–Shan, Lemma 4.10. Under the density and balance hypotheses of
Lemma 4.8, an edge-disjoint triangle packing leaves a locally balanced
graph of maximum degree at most ζm. -/
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
