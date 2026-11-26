module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph
open scoped Sym2

variable {V : Type*} {G : SimpleGraph V}

/-- Discard exactly the matching edges incident to the protected set.
The discarded edges inject into the protected vertices. -/
theorem exists_matching_avoiding_reserve [Finite V] (M : G.Subgraph)
    (hM : M.IsMatching) (W : Finset V) :
    ∃ N : G.Subgraph, N ≤ M ∧ N.IsMatching ∧ Disjoint N.verts (W : Set V) ∧
      (M.edgeSet \ N.edgeSet).ncard ≤ W.card := by
  classical
  let S : Set V := {v | v ∉ W ∧ ∃ w, M.Adj v w ∧ w ∉ W}
  let N := M.induce S
  have hSub : N ≤ M := ⟨fun _ hv => hv.2.choose_spec.1.fst_mem,fun _ _ he => he.2.2⟩
  have hMatch : N.IsMatching := by
    intro v hv
    obtain ⟨hvW,w,hvw,hwW⟩ := hv
    refine ⟨w,⟨⟨hvW,w,hvw,hwW⟩,⟨hwW,v,hvw.symm,hvW⟩,hvw⟩,?_⟩
    intro u hu
    exact hM.eq_of_adj_left hu.2.2 hvw
  have hCut (e : ↥(M.edgeSet \ N.edgeSet)) : ∃ v ∈ W, v ∈ e.val := by
    obtain ⟨e,he,heN⟩ := e
    induction e using Sym2.ind with
    | h a b =>
      have hab : M.Adj a b := he
      by_cases ha : a ∈ W
      · exact ⟨a,ha,Sym2.mem_mk_left ..⟩
      by_cases hb : b ∈ W
      · exact ⟨b,hb,Sym2.mem_mk_right ..⟩
      have hN : N.Adj a b := ⟨⟨ha,b,hab,hb⟩,⟨hb,a,hab.symm,ha⟩,hab⟩
      exact (heN hN).elim
  have hEdge (e : ↥(M.edgeSet \ N.edgeSet)) {v : V} (hv : v ∈ e.val) :
      (hM.toEdge ⟨v,Subgraph.mem_verts_of_mem_edge e.property.1 hv⟩).val = e.val := by
    obtain ⟨w,he⟩ := Sym2.mem_iff_exists.mp hv
    have hAdj : M.Adj v w := by
      change s(v,w) ∈ M.edgeSet
      rw [← he]
      exact e.property.1
    exact (congrArg Subtype.val (hM.toEdge_eq_of_adj hAdj)).trans he.symm
  let pick (e : ↥(M.edgeSet \ N.edgeSet)) : W :=
    ⟨(hCut e).choose,(hCut e).choose_spec.1⟩
  have hInj : Function.Injective pick := by
    intro e e' h
    have hEq : (hCut e).choose = (hCut e').choose := congrArg Subtype.val h
    apply Subtype.ext
    rw [← hEdge e (hCut e).choose_spec.2, ← hEdge e' (hCut e').choose_spec.2]
    congr
  refine ⟨N,hSub,hMatch,Set.disjoint_left.mpr (fun _ hN hW => hN.1 hW),?_⟩
  simpa only [Nat.card_coe_set_eq,Nat.card_eq_fintype_card,Fintype.card_coe] using
    Nat.card_le_card_of_injective pick hInj

/-- A matching between the exceptional set and its complement removes at
most one ordinary vertex for each exceptional vertex. -/
theorem matching_across_set_vertex_bounds [Finite V] {M : G.Subgraph}
    (hM : M.IsMatching) (X : Set V)
    (hAcross : ∀ v w, M.Adj v w → (v ∈ X ↔ w ∉ X)) :
    (M.verts \ X).ncard ≤ X.ncard ∧ M.verts.ncard ≤ 2*X.ncard := by
  let mate (v : ↥(M.verts \ X)) := (hM v.property.1).choose
  have hAdj (v : ↥(M.verts \ X)) : M.Adj v.val (mate v) := (hM v.property.1).choose_spec.1
  let f (v : ↥(M.verts \ X)) : X := ⟨mate v,(hAcross _ _ (hAdj v).symm).mpr v.property.2⟩
  have hInjective : Function.Injective f := by
    intro v w h
    have he : mate v = mate w := congrArg Subtype.val h
    apply Subtype.ext
    exact hM.eq_of_adj_right (he ▸ hAdj v) (hAdj w)
  have hBound : (M.verts \ X).ncard ≤ X.ncard := Nat.card_le_card_of_injective f hInjective
  have hInt : (M.verts ∩ X).ncard ≤ X.ncard := Set.ncard_le_ncard Set.inter_subset_right
  have hNum := Set.ncard_inter_add_ncard_sdiff_eq_ncard M.verts X
  exact ⟨hBound,by omega⟩

/-- A perfect matching of the induced complement extends a prescribed
matching by disjoint union. -/
theorem exists_perfect_matching_extending_of_induce_compl {N : G.Subgraph}
    (hN : N.IsMatching)
    (hResidual : ∃ M : (G.induce N.vertsᶜ).Subgraph, M.IsPerfectMatching) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ N ≤ M := by
  obtain ⟨M,hM⟩ := hResidual
  let φ : G.induce N.vertsᶜ →g G := (Embedding.induce (G := G) N.vertsᶜ).toHom
  let R := M.map φ
  have hR : R.IsMatching := hM.1.map φ Subtype.val_injective
  have hVerts : R.verts = N.vertsᶜ := by
    change φ '' M.verts = N.vertsᶜ
    rw [hM.2.verts_eq_univ]
    ext v
    constructor
    · rintro ⟨w,_,rfl⟩
      exact w.property
    · intro hv
      exact ⟨⟨v,hv⟩,Set.mem_univ _,rfl⟩
  have hDis : Disjoint N.support R.support := by
    rw [hN.support_eq_verts,hR.support_eq_verts,hVerts]
    exact Set.disjoint_left.mpr (fun _ hv hv' => hv' hv)
  refine ⟨N ⊔ R,⟨hN.sup hR hDis,?_⟩,le_sup_left⟩
  rw [Subgraph.isSpanning_iff]
  change N.verts ∪ R.verts = Set.univ
  rw [hVerts,Set.union_compl_self]

/-- Given a perfect matching of the remaining graph, losing only the
edges discarded to protect the reserve is enough. -/
theorem matching_reserve_loss_le [Finite V] {M N P : G.Subgraph}
    (hNP : N ≤ P) (W : Finset V) (hLoss : (M.edgeSet \ N.edgeSet).ncard ≤ W.card) :
    (M.edgeSet \ P.edgeSet).ncard ≤ W.card := by
  apply le_trans (Set.ncard_le_ncard ?_) hLoss
  intro e he
  exact ⟨he.1,fun hN => he.2 (Subgraph.edgeSet_mono hNP hN)⟩

end OverfullWork.ChenShan
