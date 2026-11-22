module

public import OverfullWork.CMSOperation41ProjectionBudget

@[expose] public section


/-! CMS Case S2.5 selects two distinct core neighbours for each
remaining exceptional vertex. Hall is applied to two copies of the
source set so representatives are distinct across both columns. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1800000 in
theorem exists_two_distinct_projection_neighbours (G : SimpleGraph V) [DecidableRel G.Adj]
    (B F : Finset V) (hDegree : ∀ z ∈ B,F.card+2*B.card ≤ G.degree z) :
    ∃ e : (↥B × Bool) ↪ ↥(Fᶜ : Finset V),∀ z j,G.Adj z.val (e (z,j)).val := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v))
  let A := ↥B × Bool
  let C := ↥(Fᶜ : Finset V)
  let rel (a : A) (c : C) := G.Adj a.1.val c.val
  have hCard : Fintype.card A = 2*B.card := by
    simp [A,Fintype.card_prod,Nat.mul_comm]
  have hRow (a : A) : Fintype.card A ≤ (univ.filter (rel a)).card := by
    change Fintype.card A ≤ (univ.filter (fun c : C => G.Adj a.1.val c.val)).card
    rw [DenseHall.subtype_filter_card (Fᶜ : Finset V) (G.Adj a.1.val),hCard]
    have hEq : Fᶜ.filter (G.Adj a.1.val) = G.neighborFinset a.1.val \ F := by
      ext c
      simp only [mem_filter,mem_compl,mem_sdiff,mem_neighborFinset]
      tauto
    rw [hEq]
    have hBound := card_le_card_sdiff_add_card (s := G.neighborFinset a.1.val) (t := F)
    rw [card_neighborFinset_eq_degree] at hBound
    have hh := hDegree a.1.val a.1.property
    omega
  have hHall (S : Finset A) : S.card ≤ (univ.filter fun c : C => ∃ a ∈ S,rel a c).card := by
    rcases S.eq_empty_or_nonempty with h | ⟨a,ha⟩
    · rw [h,card_empty]; exact Nat.zero_le _
    · have hSub : univ.filter (rel a) ⊆ univ.filter (fun c : C => ∃ a ∈ S,rel a c) := by
        intro c hc
        exact mem_filter.mpr ⟨mem_univ _,a,ha,(mem_filter.mp hc).2⟩
      exact (card_le_univ S).trans ((hRow a).trans (card_le_card hSub))
  obtain ⟨f,hf,hRel⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hHall
  exact ⟨⟨f,hf⟩,fun z j => hRel (z,j)⟩

theorem exists_two_spoke_replacement_words (G : SimpleGraph V) [DecidableRel G.Adj]
    (B U Z : Finset V) (hBU : B ⊆ U)
    (hDegree : ∀ z ∈ B,(U ∪ Z).card+2*B.card ≤ G.degree z) :
    ∃ e : (↥B × Bool) ↪ ↥((U ∪ Z)ᶜ : Finset V),
      let word (z : B) := [(e (z,false)).val,z.val,(e (z,true)).val]
      (∀ z,(word z).Nodup ∧ (word z).IsChain G.Adj) ∧
      ∀ z w,z ≠ w → List.Disjoint (word z) (word w) := by
  obtain ⟨e,hG⟩ := exists_two_distinct_projection_neighbours G B (U ∪ Z) hDegree
  have hOut (z : B) (j : Bool) : (e (z,j)).val ∉ U := fun h =>
    (mem_compl.mp (e (z,j)).property) (mem_union_left _ h)
  have hDifferent (z w : B) (i j : Bool) (h : (z,i) ≠ (w,j)) :
      (e (z,i)).val ≠ (e (w,j)).val := fun hh => h (e.injective (Subtype.ext hh))
  refine ⟨e,?_,?_⟩
  · intro z
    have h₁ : (e (z,false)).val ≠ z.val := fun h => hOut z false (h.symm ▸ hBU z.property)
    have h₂ : z.val ≠ (e (z,true)).val := fun h => hOut z true (h ▸ hBU z.property)
    have h₃ := hDifferent z z false true (by intro h; cases congrArg Prod.snd h)
    have hL := (hG z false).symm
    have hR := hG z true
    simp [h₁,h₂,h₃,List.isChain_cons_cons,hL,hR]
  · intro z w hzw v hv hv'
    have hz : z.val ∈ U := hBU z.property
    have hw : w.val ∈ U := hBU w.property
    have hZZ : z.val ≠ w.val := fun h => hzw (Subtype.ext h)
    have hEnd (i j : Bool) : (e (z,i)).val ≠ (e (w,j)).val :=
      hDifferent z w i j (fun h => hzw (congrArg Prod.fst h))
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv hv'
    rcases hv with hv|hv|hv <;> rcases hv' with hv'|hv'|hv'
    · exact hEnd false false (hv.symm.trans hv')
    · exact hOut z false (hv ▸ (hv'.symm ▸ hw))
    · exact hEnd false true (hv.symm.trans hv')
    · exact hOut w false (hv' ▸ (hv.symm ▸ hz))
    · exact hZZ (hv.symm.trans hv')
    · exact hOut w true (hv' ▸ (hv.symm ▸ hz))
    · exact hEnd true false (hv.symm.trans hv')
    · exact hOut z true (hv ▸ (hv'.symm ▸ hw))
    · exact hEnd true true (hv.symm.trans hv')

/-- This supplies Claim 4.1(5) for a nonindependent active pair of
degree at least six. The construction works for any cut with the
displayed degree budget. -/
theorem two_matchings_of_high_degree_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (hDegree : ∀ w ∈ W,3*W.card ≤ G.degree w) :
    ∃ M₁ M₂ : SimpleGraph V,M₁ ≤ G ∧ M₂ ≤ G ∧
      OneFactor.IsMatchingGraph M₁ ∧ OneFactor.IsMatchingGraph M₂ ∧ Disjoint M₁ M₂ ∧
      (∀ w ∈ W,∃! v,M₁.Adj w v) ∧ (∀ w ∈ W,∃! v,M₂.Adj w v) ∧
      (∀ u v,M₁.Adj u v → (u ∈ W ∧ v ∉ W) ∨ (v ∈ W ∧ u ∉ W)) ∧
      (∀ u v,M₂.Adj u v → (u ∈ W ∧ v ∉ W) ∨ (v ∈ W ∧ u ∉ W)) := by
  obtain ⟨e,hAdj⟩ := exists_two_distinct_projection_neighbours G W W (by
    intro w hw
    have h := hDegree w hw
    omega)
  let f (w : W) := e (w,false)
  let g (w : W) := e (w,true)
  have hf : Function.Injective f := fun _ _ h => congrArg Prod.fst (e.injective h)
  have hg : Function.Injective g := fun _ _ h => congrArg Prod.fst (e.injective h)
  have hDis (w : W) : f w ≠ g w := by
    intro h
    cases congrArg Prod.snd (e.injective h)
  open LowVertexMatchingAbsorption in
  exact ⟨selectionGraph W f,selectionGraph W g,selectionGraph_le W f (fun w => hAdj w false),
    selectionGraph_le W g (fun w => hAdj w true),(selectionGraph_isMatching W f hf).1,
    (selectionGraph_isMatching W g hg).1,selectionGraph_disjoint W f g hDis,
    (selectionGraph_isMatching W f hf).2,(selectionGraph_isMatching W g hg).2,
    fun _ _ h => selectionGraph_crosses_cut W f h,
    fun _ _ h => selectionGraph_crosses_cut W g h⟩

end OverfullWork.CMSTrimmingRound
