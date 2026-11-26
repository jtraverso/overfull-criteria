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

end OverfullWork.ChenShan
