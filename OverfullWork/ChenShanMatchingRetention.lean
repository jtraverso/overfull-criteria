module

public import OverfullWork.ChenShanCorePathLift
public import OverfullWork.ChenShanInducedTutte
public import OverfullWork.ChenShanMatchingReserve

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph
open scoped Classical

universe uV uI

variable {V : Type uV} {I : Type uI}

private def induce_compl_image_iso (G : SimpleGraph V) (D : Set V) (C : Set ↥(Dᶜ : Set V)) :
    ((G.induce Dᶜ).induce Cᶜ) ≃g G.induce ((Subtype.val '' C) ∪ D)ᶜ where
  toFun v := ⟨v.val.val,fun h => h.elim
    (fun ⟨_w,hw,hEq⟩ => v.property ((Subtype.ext hEq) ▸ hw)) v.val.property⟩
  invFun v := ⟨⟨v.val,fun h => v.property (Or.inr h)⟩,
    fun h => v.property (Or.inl ⟨_,h,rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Chen–Shan, Lemma 5.22. In a graph with at most four disjoint clique
cores, retain all but at most 135720 prescribed exceptional–core edges
in a perfect matching. -/
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
  classical
  have hExceptional (v : V) (hv : ∀ i, v ∉ K i) : v ∈ X := by
    rw [hX]
    exact fun h => (Set.mem_iUnion.mp h).elim hv
  have hAttach (v : V) (hv : ∀ i, v ∉ K i) :
      3 < (G.neighborSet v ∩ ⋃ i, K i).ncard :=
    (show 3 ≤ 2*X.ncard+4 by omega).trans_lt (hNeighbors v (hExceptional v hv))
  have hDisjoint : (Set.univ : Set I).PairwiseDisjoint K :=
    fun i _ j _ hij => Set.disjoint_left.mpr (fun v hv => hDis i j hij v hv)
  obtain ⟨W,hW,hReserve⟩ := exists_core_clique_reserve_preserving_components
    K hFour hDisjoint hCliques hAttach
  obtain ⟨N,hNM,hN,hNW,hLoss⟩ := exists_matching_avoiding_reserve M hM W
  have hSizeN := matching_across_set_vertex_bounds hN X (fun v w ha => hAcross v w (hNM.2 ha))
  suffices hResidual : ∃ P : (G.induce N.vertsᶜ).Subgraph, P.IsPerfectMatching by
    obtain ⟨P,hP,hNP⟩ := exists_perfect_matching_extending_of_induce_compl hN hResidual
    exact ⟨P,hP,(matching_reserve_loss_le hNP W hLoss).trans hW⟩
  apply (tutte_induce_complement _).mpr
  intro C
  let Y : Set V := Subtype.val '' C
  have hCY : Y.ncard = C.ncard := Set.ncard_image_of_injective C Subtype.val_injective
  have hDY : Disjoint N.verts Y := by
    apply Set.disjoint_left.mpr
    rintro _ hN ⟨v,_,rfl⟩
    exact v.property hN
  rw [odd_component_count_eq_of_iso (induce_compl_image_iso G N.verts C),← hCY]
  change (G.induce (Y ∪ N.verts)ᶜ).oddComponents.ncard ≤ Y.ncard
  by_cases hSmall : Y.ncard ≤ 3
  · let y := (Set.toFinite Y).toFinset
    let d := (Set.toFinite N.verts).toFinset
    have hYset : (y : Set V) = Y := Set.Finite.coe_toFinset _
    have hDset : (d : Set V) = N.verts := Set.Finite.coe_toFinset _
    have hy : y.card = Y.ncard := by rw [← Set.ncard_coe_finset y,hYset]
    have hd : d.card = N.verts.ncard := by rw [← Set.ncard_coe_finset d,hDset]
    have hWD : Disjoint W d := by
      apply Finset.disjoint_left.mpr
      intro v hv hd'
      have hMem : v ∈ (d : Set V) := hd'
      rw [hDset] at hMem
      exact Set.disjoint_left.mp hNW hMem hv
    have hCard : (y ∪ d).card ≤ 2*X.ncard+3 := by
      have h := Finset.card_union_le y d
      rw [hy,hd] at h
      have hn := hSizeN.2
      omega
    have hK (i : I) : (y ∪ d).card < (K i).ncard :=
      hCard.trans_lt ((show 2*X.ncard+3 ≤ 2*X.ncard+4 by omega).trans_lt (hCoreSize i))
    have hV (v : V) (hv : ∀ i, v ∉ K i) :
        (y ∪ d).card < (G.neighborSet v ∩ ⋃ i, K i).ncard :=
      hCard.trans_lt ((show 2*X.ncard+3 ≤ 2*X.ncard+4 by omega).trans_lt
        (hNeighbors v (hExceptional v hv)))
    obtain ⟨hIn,hKeep⟩ := hReserve y d (hy.symm ▸ hSmall) hWD hK hV
    have hOdd := odd_components_after_induced_matching_deletion_le hN Y hDY
    apply le_trans (hOdd ?_) ((tutte_induce_complement G).mp hPerfect Y)
    intro u v h
    have hs : Yᶜ ⊆ ((y : Set V)ᶜ) := by rw [hYset]
    have hSet : (↑(y ∪ d) : Set V) = Y ∪ N.verts := by rw [Finset.coe_union,hYset,hDset]
    have hTo : (Y ∪ N.verts)ᶜ ⊆ ((↑(y ∪ d) : Set V)ᶜ) := by rw [hSet]
    have hFrom : ((↑(y ∪ d) : Set V)ᶜ) ⊆ (Y ∪ N.verts)ᶜ := by rw [hSet]
    have hr := (hKeep (Set.inclusion hTo u) (Set.inclusion hTo v)).mp
      (h.map (G.induceHomOfLE hs).toHom)
    exact hr.map (G.induceHomOfLE hFrom).toHom
  · by_cases hMiddle : Y.ncard < X.ncard+4
    · have hDeleted : ((Y ∪ N.verts) ∩ ⋃ i, K i).ncard ≤ 2*X.ncard+4 := by
        have hSub : (Y ∪ N.verts) ∩ (⋃ i, K i) ⊆ Y ∪ (N.verts \ X) := by
          rintro v ⟨hv,hCore⟩
          rcases hv with hY | hN
          · exact Or.inl hY
          · refine Or.inr ⟨hN,fun hEx => ?_⟩
            rw [hX] at hEx
            exact hEx hCore
        have hc := (Set.ncard_le_ncard hSub).trans (Set.ncard_union_le _ _)
        have hn := hSizeN.1
        omega
      have hb := odd_components_induce_le_core_count K hCliques (Y ∪ N.verts)
        (fun v hv => hDeleted.trans_lt (hNeighbors v (hExceptional v hv)))
      exact hb.trans (hFour.trans (by omega))
    · have hCover (v : V) (hv : v ∉ X) : ∃ i, v ∈ K i := by
        rw [hX] at hv
        exact Set.mem_iUnion.mp (not_not.mp hv)
      have hb := odd_components_induce_le_core_add_exceptional K X (Y ∪ N.verts) hCliques hCover
      exact hb.trans (by omega)

end OverfullWork.ChenShan
