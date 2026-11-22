module

public import OverfullWork.FournierCoreCriterion
public import OverfullWork.MaximumMatchingPeeling

@[expose] public section


/-! # Exact two-colour trimming and extension

A forest of maximum degree two has an actual two-edge-colouring. If a
two-coloured layer covers the top two degree strata twice, removing it
lowers the maximum degree by exactly two. Colourings extend back, so an
uncolourable original graph has an uncolourable residue. No preservation
of the absence of overfull sets is asserted.
-/
namespace OverfullWork.TwoColourTrimming
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem two_colourable_of_acyclic_and_degree_le_two (L : SimpleGraph V)
    [DecidableRel L.Adj] (hforest : L.IsAcyclic) (hdeg : ∀v,L.degree v≤2) :
    L.EdgeColorable 2 := by
  have hc:=FournierCore.edgeColourable_of_acyclic_maximum_core L (hforest.induce _)
  exact hc.mono (L.maxDegree_le_of_forall_degree_le 2 hdeg)

omit [Fintype V] [DecidableEq V] in
/-- Disjoint palettes colour any union, including when the graphs share
some edges. Every edge is assigned to exactly one palette. -/
theorem colourable_sup (B L : SimpleGraph V) {k l : ℕ}
    (hB : B.EdgeColorable k) (hL : L.EdgeColorable l) :
    (B⊔L).EdgeColorable (k+l) := by
  classical
  obtain ⟨CB⟩:=hB
  obtain ⟨CL⟩:=hL
  have hmem : ∀e:(B⊔L).edgeSet,e.val∉L.edgeSet → e.val∈B.edgeSet := by
    intro e he
    obtain ⟨e,he'⟩:=e
    induction e using Sym2.inductionOn with
    | hf a b =>
      rw [mem_edgeSet,sup_adj] at he'
      exact he'.resolve_right he
  let col : (B⊔L).edgeSet → Fin k⊕Fin l := fun e =>
    if he:e.val∈L.edgeSet then Sum.inr (CL ⟨e.val,he⟩)
    else Sum.inl (CB ⟨e.val,hmem e he⟩)
  have C : (B⊔L).lineGraph.Coloring (Fin k⊕Fin l) := Coloring.mk col (by
    intro e f hef hcol
    obtain ⟨hne,v,hve,hvf⟩:=lineGraph_adj_iff_exists.mp hef
    by_cases he:e.val∈L.edgeSet <;> by_cases hf:f.val∈L.edgeSet
    · simp only [col,dif_pos he,dif_pos hf,Sum.inr.injEq] at hcol
      exact CL.valid (lineGraph_adj_iff_exists.mpr
        ⟨fun hh => hne (Subtype.ext (Subtype.mk.inj hh)),v,hve,hvf⟩) hcol
    · simp only [col,dif_pos he,dif_neg hf] at hcol
      cases hcol
    · simp only [col,dif_neg he,dif_pos hf] at hcol
      cases hcol
    · simp only [col,dif_neg he,dif_neg hf,Sum.inl.injEq] at hcol
      exact CB.valid (lineGraph_adj_iff_exists.mpr
        ⟨fun hh => hne (Subtype.ext (Subtype.mk.inj hh)),v,hve,hvf⟩) hcol)
  change (B⊔L).lineGraph.Colorable (k+l)
  simpa only [Fintype.card_sum,Fintype.card_fin] using C.colorable

/-- Covering both top strata is the precise degree demand for a drop
by two; a bound on the removed layer alone would not suffice. -/
theorem maxDegree_sdiff_of_two_cover (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hD : 2≤G.maxDegree) (hLG : L≤G)
    (hcover : ∀v,G.maxDegree≤G.degree v+1 → L.degree v=2) :
    (G\L).maxDegree=G.maxDegree-2 := by
  have hup : (G\L).maxDegree≤G.maxDegree-2 := by
    apply (G\L).maxDegree_le_of_forall_degree_le
    intro v
    have hs:=MaximumMatching.degree_sdiff_add_of_le G L hLG v
    have hd:=G.degree_le_maxDegree v
    by_cases hv:G.maxDegree≤G.degree v+1
    · have hh:=hcover v hv
      omega
    · omega
  have hn : Nonempty V := by
    by_contra h
    have : IsEmpty V:=not_nonempty_iff.mp h
    have hz:G.maxDegree=0:=G.maxDegree_of_subsingleton
    omega
  obtain ⟨v,hv⟩:=G.exists_maximal_degree_vertex
  have hh:=hcover v (by omega)
  have hs:=MaximumMatching.degree_sdiff_add_of_le G L hLG v
  have hr:=(G\L).degree_le_maxDegree v
  omega

/-- The full degree-demand form also permits a deficient vertex to be
a path endpoint: an original degree D-1 requires only one removed edge. -/
theorem maxDegree_sdiff_of_degree_demands (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hD : 2≤G.maxDegree) (hLG : L≤G)
    (hL : ∀v,L.degree v≤2)
    (hdemand : ∀v,G.degree v+2≤G.maxDegree+L.degree v) :
    (G\L).maxDegree=G.maxDegree-2 := by
  have hup : (G\L).maxDegree≤G.maxDegree-2 := by
    apply (G\L).maxDegree_le_of_forall_degree_le
    intro v
    have hs:=MaximumMatching.degree_sdiff_add_of_le G L hLG v
    have hd:=hdemand v
    omega
  have hn : Nonempty V := by
    by_contra h
    have : IsEmpty V:=not_nonempty_iff.mp h
    have hz:G.maxDegree=0:=G.maxDegree_of_subsingleton
    omega
  obtain ⟨v,hv⟩:=G.exists_maximal_degree_vertex
  have hs:=MaximumMatching.degree_sdiff_add_of_le G L hLG v
  have hl:=hL v
  have hd:=hdemand v
  have hr:=(G\L).degree_le_maxDegree v
  omega

omit [DecidableEq V] in
theorem colourable_of_two_colour_residue (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hD : 2≤G.maxDegree) (hLG : L≤G)
    (hL : L.EdgeColorable 2) (hc : (G\L).EdgeColorable (G.maxDegree-2)) :
    G.EdgeColorable G.maxDegree := by
  have hh:=colourable_sup (G\L) L hc hL
  rw [sdiff_sup_cancel hLG] at hh
  convert hh using 1
  omega

theorem critical_residue_not_colourable (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj]
    (hc : Overfull.IsDeltaCritical G) (hD : 2≤G.maxDegree) (hLG : L≤G)
    (hL : L.EdgeColorable 2)
    (hcover : ∀v,G.maxDegree≤G.degree v+1 → L.degree v=2) :
    ¬(G\L).EdgeColorable (G\L).maxDegree := by
  rw [maxDegree_sdiff_of_two_cover G L hD hLG hcover]
  exact fun h => hc.2.1 (colourable_of_two_colour_residue G L hD hLG hL h)

theorem critical_residue_of_degree_demands (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj]
    (hc : Overfull.IsDeltaCritical G) (hD : 2≤G.maxDegree) (hLG : L≤G)
    (hL : L.EdgeColorable 2) (hdeg : ∀v,L.degree v≤2)
    (hdemand : ∀v,G.degree v+2≤G.maxDegree+L.degree v) :
    ¬(G\L).EdgeColorable (G\L).maxDegree := by
  rw [maxDegree_sdiff_of_degree_demands G L hD hLG hdeg hdemand]
  exact fun h => hc.2.1 (colourable_of_two_colour_residue G L hD hLG hL h)

end OverfullWork.TwoColourTrimming
