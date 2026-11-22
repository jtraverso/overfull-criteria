module

public import OverfullWork.BipartiteRegularitySource

@[expose] public section


/-! Independent regularity, density and diagonal-error parameters for
the encoded source. This separation is required when later slicing. -/
namespace OverfullWork.BipartiteRegularitySource
open Finset Finpartition DirectedDegreeTrimming
open scoped Classical
set_option maxHeartbeats 18000000

theorem general_ordered_reduction_budget {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (G : SimpleGraph A) (P : Finpartition (univ : Finset A)) (ε d β : ℝ)
    (hε : 0 < ε) (hd : 0 ≤ d) (hβ : 0 < β)
    (hEqui : P.IsEquipartition) (hUniform : P.IsUniform G ε)
    (hParts : 4/β ≤ (P.parts.card:ℝ)) :
    (((univ ×ˢ univ).filter fun xy : A × A =>
      G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P ε d).Adj xy.1 xy.2).card:ℝ)
      ≤ (4*ε+β/2+4*d)*(Fintype.card A:ℝ)^2 := by
  letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  let B := (P.nonUniforms G ε).biUnion fun UV => UV.1 ×ˢ UV.2
  let C := P.parts.biUnion offDiag
  let F := (P.sparsePairs G d).biUnion fun UV => G.interedges UV.1 UV.2
  have hSub : ((univ ×ˢ univ).filter fun xy : A × A =>
      G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P ε d).Adj xy.1 xy.2) ⊆ B ∪ C ∪ F := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨_,hAdj,hNot⟩ := mem_filter.mp hxy
    obtain ⟨U,hU,hx⟩ := P.exists_mem (mem_univ x)
    obtain ⟨V,hV,hy⟩ := P.exists_mem (mem_univ y)
    by_cases hUV : U=V
    · subst V
      exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr
        ⟨U,hU,mem_offDiag.mpr ⟨hx,hy,G.ne_of_adj hAdj⟩⟩))
    by_cases hu : G.IsUniform ε U V
    · have hSparse : (G.edgeDensity U V:ℝ) < d := by
        by_contra hh
        exact hNot ⟨hAdj,U,hU,V,hV,hx,hy,hUV,hu,le_of_not_gt hh⟩
      exact mem_union_right _ (mem_biUnion.mpr ⟨(U,V),
        (P.mk_mem_sparsePairs G U V d).mpr ⟨hU,hV,hUV,hSparse⟩,
        (G.mem_interedges_iff).mpr ⟨hx,hy,hAdj⟩⟩)
    · exact mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨(U,V),
        (P.mk_mem_nonUniforms G).mpr ⟨hU,hV,hUV,hu⟩,mem_product.mpr ⟨hx,hy⟩⟩))
  have h₁ : (B.card:ℝ) ≤ 4*ε*(Fintype.card A:ℝ)^2 := by
    have hh := hEqui.sum_nonUniforms_lt (G:=G) univ_nonempty hε hUniform
    simpa only [B,card_univ] using hh.le
  have h₂ : (C.card:ℝ) ≤ β/2*(Fintype.card A:ℝ)^2 := by
    simpa only [C,card_univ] using hEqui.card_biUnion_offDiag_le hβ hParts
  have h₃ : (F.card:ℝ) ≤ 4*d*(Fintype.card A:ℝ)^2 := by
    simpa only [F,card_univ] using hEqui.card_interedges_sparsePairs_le (G:=G) (ε:=d) hd
  have hCount : (((univ ×ˢ univ).filter fun xy : A × A =>
      G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P ε d).Adj xy.1 xy.2).card:ℝ) ≤
      (B.card:ℝ)+(C.card:ℝ)+(F.card:ℝ) := by
    have hh := card_le_card hSub
    have hU := card_union_le (B ∪ C) F
    have hV := card_union_le B C
    exact_mod_cast (show ((univ ×ˢ univ).filter fun xy : A × A =>
      G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P ε d).Adj xy.1 xy.2).card ≤ B.card+C.card+F.card by omega)
  nlinarith only [hCount,h₁,h₂,h₃]

end OverfullWork.BipartiteRegularitySource

namespace OverfullWork.BipartiteRegularitySource
open Finset Finpartition DirectedDegreeTrimming
open scoped Classical
universe u
set_option maxHeartbeats 18000000

theorem exists_general_initial_source (ε d β : ℝ) (hε : 0 < ε) (hd : 0 ≤ d)
    (hβ : 0 < β) (l₀ : ℕ) :
    ∃ K N : ℕ,∀ {V : Type u} [Fintype V] (D : Digraph V),
      N ≤ Fintype.card V →
      ∃ (P : Finpartition (univ : Finset (V ⊕ V))) (H : Digraph V),
        H ≤ D ∧ P.IsEquipartition ∧ P.IsUniform (DirectedBipartiteEncoding.graph D) ε ∧
        l₀ ≤ P.parts.card ∧ P.parts.card ≤ K ∧
        H=crossDigraph ((DirectedBipartiteEncoding.graph D).regularityReduced P ε d) ∧
        (total (D\H):ℝ) ≤ (16*ε+2*β+16*d)*(Fintype.card V:ℝ)^2 := by
  let l := max l₀ ⌈4/β⌉₊
  refine ⟨SzemerediRegularity.bound ε l,max 1 l,?_⟩
  intro V _ D hn
  have hnPos : 0 < Fintype.card V := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp hnPos
  let G := DirectedBipartiteEncoding.graph D
  have hOrder : l ≤ Fintype.card (V ⊕ V) := by
    simp only [Fintype.card_sum];omega
  obtain ⟨P,hEqui,hLow,hHigh,hUniform⟩ := szemeredi_regularity G hε hOrder
  let H := crossDigraph (G.regularityReduced P ε d)
  refine ⟨P,H,cross_le D _ SimpleGraph.regularityReduced_le,hEqui,hUniform,?_,hHigh,rfl,?_⟩
  · exact (le_max_left _ _).trans hLow
  · have hParts : 4/β ≤ (P.parts.card:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right l₀ ⌈4/β⌉₊).trans hLow)
    have hEncoded := general_ordered_reduction_budget G P ε d β hε hd hβ hEqui hUniform hParts
    have hCross : (total (D\H):ℝ) ≤
        (((univ ×ˢ univ).filter fun xy : (V ⊕ V) × (V ⊕ V) =>
          G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P ε d).Adj xy.1 xy.2).card:ℝ) := by
      have hh := cross_deletion_bound D (G.regularityReduced P ε d)
      have hCast := (Nat.cast_le (α:=ℝ)).mpr hh
      convert hCast using 1 <;> congr 2 <;> ext xy <;> simp only [mem_filter,SimpleGraph.regularityReduced_adj,G]

    simp only [Fintype.card_sum,Nat.cast_add] at hEncoded
    nlinarith only [hEncoded,hCross]

end OverfullWork.BipartiteRegularitySource
