module

public import OverfullWork.OsthusStadenFactorsFromBalancedLayers
public import OverfullWork.OsthusStadenGlobalPack

@[expose] public section


/-! Merge the extracted factors in each layer, then combine the packs
on the common host. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u v w

/-- Given the cut-link data on the actual extraction coordinates, all
layers contribute κ Hamilton cycles in the original graph. -/
theorem exists_hamilton_pack_from_physical_layer_factors
    (d ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 0 < d) :
    ∃ N : ℕ, ∀ {U : Type u} [Fintype U] {V : Type v} [Fintype V] {I : Type w} [Fintype I]
      {J : Type*} [Fintype J] (G : Digraph V) (H : J → Digraph V)
      (ordinary : J → Finset V) (cell : J → U → Finset V) (factor : J → Equiv.Perm U)
      (red : J → Finset (V × V)) (incoming outgoing : J → Finset U)
      (n κ p batch : ℕ) (ε₃ d₃ : ℝ)
      (P : ∀ j, OsthusStadenPhysicalFactors (H j) (ordinary j) (cell j) (factor j) (red j) n κ ε₃ d₃)
      (K : ∀ j, LayerBridgeData (factor j) (incoming j) (outgoing j) p
        ((red j).map (Equiv.prodCongr (P j).coord.symm (P j).coord.symm).toEmbedding) I)
      (root : ∀ j, ↥(incoming j ∪ outgoing j)),
      (∀ j, H j ≤ G) → (∀ j k, j ≠ k → Disjoint (H j) (H k)) →
      κ ≤ (p-4)*batch → 0 ≤ ε₃ → ε₃ ≤ ε → d ≤ d₃-2*ε₃ →
      0 < n → N ≤ n →
      (batch:ℝ)+ν*(n:ℝ) ≤ d*τ*(n:ℝ) →
      γ*(n:ℝ)+(batch:ℝ) ≤ d*(n:ℝ) →
      ∃ F : Fin (Fintype.card J*κ) → Equiv.Perm V,
        (∀ f, HasSpanningCycle (fun x y => F f x = y)) ∧
        (∀ f x, G.Adj x (F f x)) ∧
        ∀ f g, f ≠ g → ∀ x, F f x ≠ F g x := by
  obtain ⟨N,hN⟩ := exists_hamilton_pack_of_prepared_layer.{v,u,0,w} d ε ν τ γ hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro U _ V _ I _ J _ G H ordinary cell factor red incoming outgoing n κ p batch ε₃ d₃ P K root
    hLe hDis hCap hε₃ hεBound hDensity hn hSize hCost hDegree
  let X (j : J) := SliceVertex ↥((ordinary j)ᶜ : Finset V) U (Fin n)
  let pull (j : J) : Digraph (X j) := pullDirectedPair (P j).coord.toEmbedding (P j).coord.toEmbedding (H j)
  choose F hCycle hArc hFDis using fun j =>
    hN (factor j) (incoming j) (outgoing j) p κ batch
      ((red j).map (Equiv.prodCongr (P j).coord.symm (P j).coord.symm).toEmbedding)
      (K j) (root j) (P j).factors (P j).reserve (pull j) ε₃ d₃
      hCap (P j).uses_red_or_successor (P j).factors_disjoint (P j).factor_arcs (P j).reserve_arcs
      (P j).reserve_fresh (P j).reserve_regular hε₃ hεBound hDensity
      (by simpa only [Fintype.card_fin] using hn) (by simpa only [Fintype.card_fin] using hSize)
      (by simpa only [Fintype.card_fin] using hCost) (by simpa only [Fintype.card_fin] using hDegree)
  let e := Fintype.equivFin J
  exact combine_physical_layer_packs (fun i => X (e.symm i)) (fun i => (P (e.symm i)).coord) G
    (fun i => H (e.symm i)) (fun i => F (e.symm i))
    (fun i => hLe (e.symm i)) (fun i j h => hDis _ _ (fun he => h (e.symm.injective he)))
    (fun i => hCycle (e.symm i)) (fun i => hArc (e.symm i)) (fun i => hFDis (e.symm i))

end OverfullWork.DirectedRobustExpansion
