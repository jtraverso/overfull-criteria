module

public import OverfullWork.DirectedBipartiteEncoding
public import OverfullWork.PureGraphDeletionBudget
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

@[expose] public section


/-! An actual initial regularity source for arbitrary digraphs, obtained
from the simple bipartite encoding. The two copies share a bounded
parent equipartition. This produces an actual close directed subgraph;
equal source/target subcells still require a separate construction. -/
namespace OverfullWork.BipartiteRegularitySource
open Finset Finpartition DirectedRobustExpansion DirectedClusterQuotient DirectedDegreeTrimming
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 18000000

def crossDigraph (G : SimpleGraph (V ⊕ V)) : Digraph V where
  Adj u v := G.Adj (.inl u) (.inr v)

theorem cross_le (D : Digraph V) (G : SimpleGraph (V ⊕ V))
    (hG : G ≤ DirectedBipartiteEncoding.graph D) : crossDigraph G ≤ D := by
  intro u v huv
  exact hG huv

theorem cross_deletion_bound (D : Digraph V) (G : SimpleGraph (V ⊕ V)) :
    total (D\crossDigraph G) ≤
      ((univ ×ˢ univ).filter fun xy : (V ⊕ V) × (V ⊕ V) =>
        (DirectedBipartiteEncoding.graph D).Adj xy.1 xy.2 ∧ ¬G.Adj xy.1 xy.2).card := by
  letI : DecidableRel (D\crossDigraph G).Adj := fun _ _ => Classical.propDecidable _
  let E : (V × V) ↪ ((V ⊕ V) × (V ⊕ V)) :=
    ⟨fun uv => (.inl uv.1,.inr uv.2),by
      intro a b hh
      exact Prod.ext (Sum.inl.inj (congrArg Prod.fst hh)) (Sum.inr.inj (congrArg Prod.snd hh))⟩
  rw [←arcCell_univ_card]
  have hSub : (arcCell (D\crossDigraph G) univ univ).map E ⊆
      (univ ×ˢ univ).filter (fun xy => (DirectedBipartiteEncoding.graph D).Adj xy.1 xy.2 ∧ ¬G.Adj xy.1 xy.2) := by
    intro xy hxy
    obtain ⟨uv,huv,rfl⟩ := mem_map.mp hxy
    obtain ⟨_,hD,hNot⟩ := mem_filter.mp huv
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _,mem_univ _⟩,hD,hNot⟩
  simpa only [card_map] using card_le_card hSub

theorem ordered_reduction_budget {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (G : SimpleGraph A) (P : Finpartition (univ : Finset A)) (η : ℝ) (hη : 0 < η)
    (hEqui : P.IsEquipartition) (hUniform : P.IsUniform G (η/8))
    (hParts : 4/η ≤ (P.parts.card:ℝ)) :
    (((univ ×ˢ univ).filter fun xy : A × A =>
      G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P (η/8) (η/4)).Adj xy.1 xy.2).card:ℝ)
      < 2*η*(Fintype.card A:ℝ)^2 := by
  letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  let B := (P.nonUniforms G (η/8)).biUnion fun UV => UV.1 ×ˢ UV.2
  let C := P.parts.biUnion offDiag
  let F := (P.sparsePairs G (η/4)).biUnion fun UV => G.interedges UV.1 UV.2
  have hSub : ((univ ×ˢ univ).filter fun xy : A × A =>
      G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P (η/8) (η/4)).Adj xy.1 xy.2) ⊆ B ∪ C ∪ F := by
    rintro ⟨x,y⟩ hxy
    exact SimpleGraph.unreduced_edges_subset (G:=G) (P:=P) (ε:=η) hxy
  have h₁ : (B.card:ℝ) < 4*(η/8)*(Fintype.card A:ℝ)^2 := by
    simpa only [B,card_univ] using hEqui.sum_nonUniforms_lt (G:=G) univ_nonempty (by positivity) hUniform
  have h₂ : (C.card:ℝ) ≤ η/2*(Fintype.card A:ℝ)^2 := by
    simpa only [C,card_univ] using hEqui.card_biUnion_offDiag_le hη hParts
  have h₃ : (F.card:ℝ) ≤ 4*(η/4)*(Fintype.card A:ℝ)^2 := by
    simpa only [F,card_univ] using hEqui.card_interedges_sparsePairs_le (G:=G) (ε:=η/4) (by positivity)
  have hCount : (((univ ×ˢ univ).filter fun xy : A × A =>
      G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P (η/8) (η/4)).Adj xy.1 xy.2).card:ℝ) ≤
      (B.card:ℝ)+(C.card:ℝ)+(F.card:ℝ) := by
    have hh := card_le_card hSub
    have hU := card_union_le (B ∪ C) F
    have hV := card_union_le B C
    have hn : ((univ ×ˢ univ).filter fun xy : A × A =>
      G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P (η/8) (η/4)).Adj xy.1 xy.2).card ≤ B.card+C.card+F.card := by omega
    exact_mod_cast hn
  linarith only [hCount,h₁,h₂,h₃]

end OverfullWork.BipartiteRegularitySource

namespace OverfullWork.BipartiteRegularitySource
open Finset Finpartition DirectedDegreeTrimming
open scoped Classical
universe u
set_option maxHeartbeats 18000000

theorem exists_initial_source (η : ℝ) (hη : 0 < η) (l₀ : ℕ) :
    ∃ K N : ℕ,∀ {V : Type u} [Fintype V] (D : Digraph V),
      N ≤ Fintype.card V →
      ∃ (P : Finpartition (univ : Finset (V ⊕ V))) (H : Digraph V),
        H ≤ D ∧ P.IsEquipartition ∧ P.IsUniform (DirectedBipartiteEncoding.graph D) (η/8) ∧
        l₀ ≤ P.parts.card ∧ P.parts.card ≤ K ∧
        H=crossDigraph ((DirectedBipartiteEncoding.graph D).regularityReduced P (η/8) (η/4)) ∧
        (total (D\H):ℝ) ≤ 8*η*(Fintype.card V:ℝ)^2 := by
  let l := max l₀ ⌈4/η⌉₊
  refine ⟨SzemerediRegularity.bound (η/8) l,max 1 l,?_⟩
  intro V _ D hn
  have hnPos : 0 < Fintype.card V := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp hnPos
  let G := DirectedBipartiteEncoding.graph D
  have hOrder : l ≤ Fintype.card (V ⊕ V) := by
    simp only [Fintype.card_sum];omega
  obtain ⟨P,hEqui,hLow,hHigh,hUniform⟩ := szemeredi_regularity G (by positivity : 0 < η/8) hOrder
  let H := crossDigraph (G.regularityReduced P (η/8) (η/4))
  refine ⟨P,H,cross_le D _ SimpleGraph.regularityReduced_le,hEqui,hUniform,?_,hHigh,rfl,?_⟩
  · exact (le_max_left _ _).trans hLow
  · have hParts : 4/η ≤ (P.parts.card:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right l₀ ⌈4/η⌉₊).trans hLow)
    have hEncoded := ordered_reduction_budget G P η hη hEqui hUniform hParts
    have hCross : (total (D\H):ℝ) ≤
        (((univ ×ˢ univ).filter fun xy : (V ⊕ V) × (V ⊕ V) =>
          G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P (η/8) (η/4)).Adj xy.1 xy.2).card:ℝ) := by
      exact_mod_cast cross_deletion_bound D (G.regularityReduced P (η/8) (η/4))
    simp only [Fintype.card_sum,Nat.cast_add] at hEncoded
    nlinarith only [hEncoded,hCross]

end OverfullWork.BipartiteRegularitySource
