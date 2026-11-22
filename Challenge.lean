module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.List.Infix

@[expose] public section

/-! Eventual Hamiltonicity, spanning linkage, fixed-size sampling and
spanning configuration packing for robust expanders. -/

open Finset
open scoped Classical
universe u v w


namespace OverfullWork.UniformSubsetSampling

variable {V : Type*} [Fintype V]

noncomputable def probability (k : ℕ) (P : Finset V → Prop) : ℝ :=
  (((univ : Finset V).powersetCard k).filter P).card/(Fintype.card V).choose k

end OverfullWork.UniformSubsetSampling

namespace OverfullWork.InducedDigraphSampling

variable {V : Type*} [Fintype V]

def induced (D : Digraph V) (X : Finset V) : Digraph X where
  Adj u v := D.Adj u.val v.val

end OverfullWork.InducedDigraphSampling

namespace OverfullWork.DirectedRobustExpansion

open UniformSubsetSampling
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def inNeighbours (D : Digraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter fun u => D.Adj u v).card

noncomputable def inDegree (D : Digraph V) (v : V) : ℕ := inNeighbours D univ v

noncomputable def outDegree (D : Digraph V) (v : V) : ℕ :=
  (univ.filter fun w => D.Adj v w).card

noncomputable def realNeighbourhood (D : Digraph V) (ν : ℝ) (S : Finset V) : Finset V :=
  univ.filter fun v => ν*(Fintype.card V:ℝ) ≤ (inNeighbours D S v:ℝ)

def IsRealRobust (D : Digraph V) (ν τ : ℝ) : Prop :=
  ∀ S : Finset V,τ*(Fintype.card V:ℝ) ≤ (S.card:ℝ) →
    (S.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ) →
    (S.card:ℝ)+ν*(Fintype.card V:ℝ) ≤ ((realNeighbourhood D ν S).card:ℝ)

def IsOrientationOf (D : Digraph V) (G : SimpleGraph V) : Prop :=
  (∀ u v,D.Adj u v → G.Adj u v) ∧
  (∀ u v,G.Adj u v → D.Adj u v ∨ D.Adj v u) ∧
  ∀ u v,¬(D.Adj u v ∧ D.Adj v u)

def IsVertexSamplingRobust (D : Digraph V) (c p ν τ : ℝ) : Prop :=
  IsRealRobust D ν τ ∧ ∀ k : ℕ,k ≤ Fintype.card V → c*(Fintype.card V:ℝ) ≤ (k:ℝ) →
    probability k (fun X => ¬IsRealRobust (InducedDigraphSampling.induced D X) ν τ) ≤ p

end OverfullWork.DirectedRobustExpansion

namespace OverfullWork.PrunedCore

open SimpleGraph
variable {V : Type u} [Fintype V] [DecidableEq V]

def neighboursIn (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (x : V) : ℕ :=
  ((G.neighborFinset x).filter fun y => y∈T).card

end OverfullWork.PrunedCore

namespace OverfullWork.RobustExpansion

open PrunedCore
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def realNeighbourhood (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : ℝ) (S : Finset V) : Finset V :=
  univ.filter fun v=>ν*(Fintype.card V:ℝ)≤(neighboursIn G S v:ℝ)

def IsRealRobust (G : SimpleGraph V) [DecidableRel G.Adj] (ν τ : ℝ) : Prop :=
  ∀S : Finset V,τ*(Fintype.card V:ℝ)≤(S.card:ℝ) →
    (S.card:ℝ)≤(1-τ)*(Fintype.card V:ℝ) →
    (S.card:ℝ)+ν*(Fintype.card V:ℝ)≤((realNeighbourhood G ν S).card:ℝ)

end OverfullWork.RobustExpansion

namespace OverfullWork.DirectedReserveUsage

variable {V I : Type*} [Fintype V] [Fintype I]

noncomputable def visits (A : I → Finset V) (v : V) : ℕ :=
  ((univ : Finset I).filter (fun i => v ∈ A i)).card

end OverfullWork.DirectedReserveUsage

namespace OverfullWork.BipartiteRegularitySource

open DirectedRobustExpansion

/-- A uniformly sampled set of a fixed linear size inherits robust expansion. -/

theorem robust_vertex_sampling_explicit (ν τ : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : 0 < τ) (hτSmall : τ ≤ 1/8) :
    ∀ c : ℝ,0 < c → c ≤ 1 → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] (D : Digraph V),N ≤ Fintype.card V →
        IsRealRobust D ν τ →
          IsVertexSamplingRobust D c (1/(Fintype.card V:ℝ)^2) (ν^6/(2:ℝ)^60) (4*τ) := by
  sorry

end OverfullWork.BipartiteRegularitySource

namespace OverfullWork.DirectedAbsorbingLadder

open DirectedRobustExpansion

/-- A sufficiently large robust outexpander of linear minimum semidegree has a Hamilton cycle. -/

theorem exists_hamilton_threshold (ν τ γ : ℝ) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V),
      N ≤ Fintype.card V → IsRealRobust D ν τ →
      (∀ v, γ*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, γ*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      ∃ T : List V, ∃ x : V, T.Nodup ∧ (∀ v, v ∈ T) ∧ T.head? = some x ∧
        (T ++ [x]).IsChain D.Adj := by
  sorry

end OverfullWork.DirectedAbsorbingLadder

namespace OverfullWork.RobustSpanningLinkage

/-- Spanning vertex-disjoint paths join the prescribed disjoint pairs of endpoints. -/

theorem cms_lemma_3_15 (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], N ≤ Fintype.card V → RobustExpansion.IsRealRobust G ν τ →
      α*(Fintype.card V:ℝ) ≤ (G.minDegree:ℝ) →
      ∀ {p : ℕ}, 0 < p → (p:ℝ) ≤ ν^4*(Fintype.card V:ℝ) →
      ∀ (a b : Fin p → V), Function.Injective a → Function.Injective b →
        (∀ i j, a i ≠ b j) →
        ∃ P : ∀ i, G.Walk (a i) (b i),
          (∀ i,(P i).IsPath) ∧
          (∀ i j,i ≠ j → ∀ v,v ∈ (P i).support → v ∉ (P j).support) ∧
          ∀ v, ∃ i,v ∈ (P i).support := by
  sorry

end OverfullWork.RobustSpanningLinkage

namespace OverfullWork.DirectedSpanningConfiguration

open DirectedRobustExpansion DirectedReserveUsage
variable {V : Type u} {I : Type v}

/-- The indices distinguish layout edge occurrences even for equal ordered
endpoint pairs. The boundary also includes the isolated layout vertices. -/
structure Layout (V : Type u) (I : Type v) where
  boundary : Finset V
  source : I → V
  target : I → V
  fixed : Finset I
  ends : ∀ i, source i ∈ boundary ∧ target i ∈ boundary ∧ source i ≠ target i

/-- Successive ordered pairs of a word form a digraph. -/
def wordGraph (l : List V) : Digraph V where
  Adj x y := List.IsInfix [x,y] l

/-- Each interior is outside the layout and each vertex outside the layout
belongs to exactly one interior. Fixed edge occurrences have empty interiors.
Flexible paths are built in the host digraph and have a nonempty interior. -/
structure Realization (D : Digraph V) (L : Layout V I) where
  interior : I → List V
  simple : ∀ i, (L.source i :: interior i ++ [L.target i]).Nodup
  fixed_empty : ∀ i ∈ L.fixed, interior i = []
  flexible_nonempty : ∀ i ∉ L.fixed, interior i ≠ []
  flexible_chain : ∀ i ∉ L.fixed, (L.source i :: interior i ++ [L.target i]).IsChain D.Adj
  outside : ∀ i x, x ∈ interior i → x ∉ L.boundary
  unique : ∀ i j, i ≠ j → List.Disjoint (interior i) (interior j)
  spans : ∀ x, x ∉ L.boundary → ∃ i, x ∈ interior i

def Realization.word {D : Digraph V} {L : Layout V I} (R : Realization D L) (i : I) : List V :=
  L.source i :: R.interior i ++ [L.target i]

def Realization.used {D : Digraph V} {L : Layout V I} (R : Realization D L) : Digraph V :=
  ⨆ i : {i // i ∉ L.fixed}, wordGraph (R.word i.val)

section
variable [Fintype I]

/-- Flexible occurrences incident to the given vertex, in the indicated
direction. This counts repeated ordered endpoint pairs with multiplicity. -/
noncomputable def Layout.endpointLoad {V I : Type*} [Fintype I] (L : Layout V I) (incoming : Bool) (v : V) : ℕ :=
  ∑ i : {i // i ∉ L.fixed}, if v = (if incoming then L.target i.val else L.source i.val)
    then 1 else 0

end

/-- The host edges underlying a subdigraph of an orientation. -/
def hostEdges {V : Type*} (G : SimpleGraph V) (U : Digraph V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (U.Adj x y ∨ U.Adj y x)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

/-- A disjoint realization of all prescribed layouts in a simple host,
with independent fixed copies. The used directed graph records just
the host arcs consumed in the undirected remainder. -/
structure CMSPacking {V J : Type*} (I : J → Type*) (G : SimpleGraph V)
    (L : ∀ j, Layout V (I j)) where
  orientation : Digraph V
  isOrientation : IsOrientationOf orientation G
  configuration : ∀ j, Realization orientation (L j)
  host_disjoint : Pairwise (fun i j => Disjoint (configuration i).used (configuration j).used)

def CMSPacking.used {V J : Type*} {I : J → Type*} {G : SimpleGraph V}
    {L : ∀ j, Layout V (I j)} (P : CMSPacking I G L) : Digraph V :=
  ⨆ j, (P.configuration j).used

/-- A family of small layouts is realized by spanning configurations with a robust remainder. -/

theorem cms_lemma_3_14 (a gap ν τ : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1)
    (hgap : 0 < gap) (hgapA : gap ≤ a) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτgap : 16384*τ ≤ gap) :
    ∃ ε ν' : ℝ, 0 < ε ∧ 0 < ν' ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] {J : Type w} [Fintype J]
        (I : J → Type v) [∀ j, Fintype (I j)]
        (G : SimpleGraph V) [DecidableRel G.Adj] (L : ∀ j, Layout V (I j)) (long : ∀ j, I j),
        let n := Fintype.card V
        N ≤ n → RobustExpansion.IsRealRobust G ν τ →
        (∀ v, |(G.degree v:ℝ)-a*(n:ℝ)| ≤ ε*(n:ℝ)) →
        (Fintype.card J:ℝ) ≤ ((a-gap)/2)*(n:ℝ) →
        (∀ i, ((L i).boundary.card:ℝ) ≤ ε^2*(n:ℝ) ∧ long i ∉ (L i).fixed ∧
          (Fintype.card (I i):ℝ) ≤ ε^4*(n:ℝ)) →
        (∀ v, ((∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v):ℕ):ℝ)
          ≤ ε^3*(n:ℝ)) →
        (∀ v, (visits (fun i => (L i).boundary) v:ℝ) ≤ ε^2*(n:ℝ)) →
        ∃ P : CMSPacking I G L, RobustExpansion.IsRealRobust (G \ hostEdges G P.used) ν' τ := by
  sorry

end OverfullWork.DirectedSpanningConfiguration

/-! Hamilton decompositions. -/
namespace OverfullWork.DirectedRobustExpansion

variable {V : Type u} [Fintype V]

def HasSpanningCycle (Adj : V → V → Prop) : Prop :=
  ∃ T : List V, ∃ x : V, T.Nodup ∧ (∀ v, v ∈ T) ∧ T.head? = some x ∧
    (T ++ [x]).IsChain Adj

structure DirectedHamiltonDecomposition (D : Digraph V) (k : ℕ) : Type u where
  factor : Fin k → Digraph V
  factor_le : ∀ i, factor i ≤ D
  partition : ∀ v w, D.Adj v w → ∃! i, (factor i).Adj v w
  degrees : ∀ i v, outDegree (factor i) v = 1 ∧ inDegree (factor i) v = 1
  spanning : ∀ i, HasSpanningCycle (factor i).Adj

structure HamiltonDecomposition (G : SimpleGraph V) (k : ℕ) : Type u where
  factor : Fin k → SimpleGraph V
  factor_le : ∀ i, factor i ≤ G
  partition : ∀ v w, G.Adj v w → ∃! i, (factor i).Adj v w
  degrees : ∀ i v, (factor i).degree v = 2
  spanning : ∀ i, HasSpanningCycle (factor i).Adj

def matchingUnion {t : ℕ} (M : Fin t → Equiv.Perm V) : Digraph V :=
  ⟨fun v w => ∃ j, M j v = w⟩

def RobustApproximateHamiltonPacking : Prop :=
  ∀ α : ℝ, 0 < α → ∃ τ : ℝ, 0 < τ ∧
    ∀ ν η : ℝ, 0 < ν → 0 < η → ∃ N : ℕ,
    ∀ {V : Type u} [Fintype V] (D : Digraph V) (r : ℕ),
      N ≤ Fintype.card V → α*(Fintype.card V:ℝ) ≤ (r:ℝ) → IsRealRobust D ν τ →
      (∀ v, inDegree D v = r ∧ outDegree D v = r) → (∀ v, ¬ D.Adj v v) →
      ∃ (s : ℕ) (C : Fin s → Equiv.Perm V), (1-η)*(r:ℝ) ≤ (s:ℝ) ∧ matchingUnion C ≤ D ∧
        (∀ i, HasSpanningCycle (fun x y => C i x = y)) ∧ ∀ i j, i ≠ j → ∀ v, C i v ≠ C j v

theorem osthus_staden_theorem_1_1_existence : RobustApproximateHamiltonPacking.{u} := by
  sorry

theorem kuhn_osthus_directed_decomposition (α : ℝ) (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ ν : ℝ, 0 < ν → ∃ N : ℕ, ∀ {V : Type u} [Fintype V]
        (G : Digraph V) (r : ℕ), N ≤ Fintype.card V →
        α*(Fintype.card V:ℝ) ≤ (r:ℝ) → IsRealRobust G ν τ →
        (∀ v, outDegree G v = r ∧ inDegree G v = r) → (∀ v, ¬ G.Adj v v) →
        Nonempty (DirectedHamiltonDecomposition G r) := by
  sorry

theorem cms_theorem_5_5 (α : ℝ) (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
        N ≤ Fintype.card V → α*(Fintype.card V:ℝ) ≤ 2*(k:ℝ) → RobustExpansion.IsRealRobust G ν τ →
        (∀ v, G.degree v = 2*k) → Nonempty (HamiltonDecomposition G k) := by
  sorry

end OverfullWork.DirectedRobustExpansion
