module

public import OverfullWork.KuhnOsthusPreprocessingFromWoundPack
public import OverfullWork.KuhnOsthusExceptionalInternalArcs

@[expose] public section


/-! Data of the first physical reserve in the proof of Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling
open scoped Classical

/-- The first physical reserve retains the exceptional packing,
the sparse extender and the graph that pays the prescribed semidegrees. -/
structure KuhnOsthusPreprocessingReserve {V : Type*} [Fintype V] {l j : ℕ}
    (G : Digraph V) (Z : Finset V) (R : Digraph (Fin (l*j)))
    (X : Fin (l*j) → Finset V) (hj : 0 < j) (m r t : ℕ) (σ d d₀ ε ηS : ℝ) where
  pack : WoundFactorPacking G Z X hj 50 m r σ
  label : V → Fin 50
  cluster : ↥Zᶜ → Fin (l*j)
  chord : Digraph ↥Zᶜ
  successor : Digraph ↥Zᶜ
  graph : Digraph V
  extender : Digraph V
  style_label : ∀ i x, x ∈ pack.cell i → label x = i.1
  coordinate : ∀ i x, cluster x = i ↔ x.val ∈ X i
  pairs_disjoint : Disjoint chord successor
  pairs : ExtenderPairBounds R chord successor cluster (fun x => label x.val) m
    d₀ (d₀/((l*j:ℕ):ℝ)) ε ((d₀/200-ηS)*(50*m)) ((d₀/(d/2))^2*(50*m))
  degree_extender : ∀ x, (inDegree (chord ⊔ successor) x:ℝ) +
    outDegree (chord ⊔ successor) x ≤ (8*d₀/d)*(50*m)
  le_host : graph ≤ G
  extender_le : extender ≤ graph
  induced_extender : induced extender Zᶜ = chord ⊔ successor
  contains_factors : (⨆ i, ⨆ a, (pack.factors i a).digraph) ≤ graph
  factors_disjoint : Disjoint (⨆ i, ⨆ a, (pack.factors i a).digraph) extender
  degree : ∀ x, let D := if x ∈ Z then 50*l*r else 50*l*r+t
    inDegree graph x = D ∧ outDegree graph x = D

/-- Preprocessing spends precisely the exceptional slots of its
factors, leaving the internal arcs for Lemma 11.1. -/
theorem KuhnOsthusPreprocessingReserve.no_internal {V : Type*} [Fintype V] {l j m r t : ℕ}
    {G : Digraph V} {Z : Finset V} {R : Digraph (Fin (l*j))} {X : Fin (l*j) → Finset V}
    {hj : 0 < j} {σ d d₀ ε ηS : ℝ}
    (prep : KuhnOsthusPreprocessingReserve G Z R X hj m r t σ d d₀ ε ηS) :
    ∀ x ∈ Z, ∀ y ∈ Z, ¬ prep.graph.Adj x y := by
  intro x hx y hy
  exact (prep.pack.reserve_preserves_internal_arcs prep.graph prep.contains_factors
    (fun z hz => by simpa only [if_pos hz] using (prep.degree z).2) x hx y hy).1

end OverfullWork.DirectedRobustExpansion
