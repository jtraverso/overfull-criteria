module

public import OverfullWork.BipartiteCellParameters
public import OverfullWork.GeneralBipartiteRegularitySource
public import OverfullWork.TwoSidedRealTransfer

@[expose] public section


/-! Actual quotient arcs between two families of chunks inherit their
directed regular-pair data from the encoded parent partition. -/
namespace OverfullWork.BipartiteRegularitySource
open Finset Finpartition DirectedClusterQuotient DirectedBipartiteEncoding
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

theorem two_sided_pair_from_parents (D : Digraph V)
    (P : Finpartition (univ : Finset (V ⊕ V))) (f g : V → Option I)
    (π σ : I → P.parts) (m : ℕ) (ε d γ : ℝ)
    (hF : ∀ i,(cluster f i).card=m) (hG : ∀ i,(cluster g i).card=m)
    (hFP : ∀ i,(cluster f i).map (sideEmbedding false) ⊆ (π i).val)
    (hGP : ∀ i,(cluster g i).map (sideEmbedding true) ⊆ (σ i).val)
    (hScale : ∀ U : P.parts,(U.val.card:ℝ)*γ/6 ≤ (m:ℝ))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 ≤ ε) (hεγ : ε ≤ γ/6)
    (i j : I)
    (hArc : (TwoSidedClusterQuotient.quotient
      (crossDigraph ((graph D).regularityReduced P ε d)) f g).Adj i j) :
    DirectedRegularPairs.IsUniform D (12*ε/γ) (cluster f i) (cluster g j) ∧
      d-ε ≤ DirectedRegularPairs.density D (cluster f i) (cluster g j) := by
  obtain ⟨u,v,hu,hv,hEdge,U,hU,W,hW,huU,hvW,hUW,hUniform,hDensity⟩ := hArc
  have huP : Sum.inl u ∈ (π i).val := by
    exact hFP i (mem_map.mpr ⟨u,(mem_cluster f i u).mpr hu,rfl⟩)
  have hvP : Sum.inr v ∈ (σ j).val := by
    exact hGP j (mem_map.mpr ⟨v,(mem_cluster g j v).mpr hv,rfl⟩)
  have hParentU : U=(π i).val := P.eq_of_mem_parts hU (π i).property huU huP
  have hParentW : W=(σ j).val := P.eq_of_mem_parts hW (σ j).property hvW hvP
  subst U;subst W
  apply directed_pair_from_parent D (π i).val (σ j).val (cluster f i) (cluster g j) ε d γ
    hγ hγ1 hε hεγ hUniform hDensity
  · simpa only [left,sideEmbedding,Bool.false_eq_true,if_false] using hFP i
  · simpa only [right,sideEmbedding,if_true] using hGP j
  · rw [hF];exact hScale (π i)
  · rw [hG];exact hScale (σ j)

end OverfullWork.BipartiteRegularitySource
