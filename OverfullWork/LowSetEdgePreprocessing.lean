module

public import OverfullWork.CriticalEdgeFilter
public import OverfullWork.CriticalCaptureReduction

@[expose] public section


/-! # Actual finite low-set edge preprocessing

This implements the stopping condition of CMS Algorithm 1 on a fixed
ambient vertex type. Isolated vertices can remain: they do not affect
colourability or the final positive-degree low set. Every removed edge
meets W, the induced graph outside W is unchanged, and every deletion
preserves the existence of a maximum-palette colouring. No preservation
of the absence of overfull subsets is needed.
-/
namespace OverfullWork.LowSetEdgePreprocessing
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

/-- The two sides of a vertex cut partition every neighbourhood. -/
theorem neighboursIn_add_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (x : V) :
    neighboursIn G W x+neighboursIn G Wᶜ x=G.degree x := by
  unfold neighboursIn
  simp only [mem_compl]
  exact card_filter_add_card_filter_not (fun z=>z∈W)

/-- VAL forbids a bad cut edge in every common-Delta critical copy.
This uses source degrees only through their valid ambient upper bounds. -/
theorem critical_copy_avoids_bad_edge
    {A : Type v} [Fintype A] [DecidableEq A]
    {J : SimpleGraph A} [DecidableRel J.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    (hW : ∀w∈W,G.degree w<G.maxDegree)
    (f : Copy J G) (hmax : J.maxDegree=G.maxDegree)
    (hc : Overfull.IsDeltaCritical J) {w x : V} (hw : w∈W)
    (hbad : G.degree w≤neighboursIn G W x) :
    ∀{a b},J.Adj a b → s(f a,f b)≠s(w,x) := by
  classical
  have hT : ((univ : Finset A).filter fun z=>J.degree z=J.maxDegree).image f ⊆ Wᶜ := by
    intro z hz
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hz
    have hd:=(mem_filter.mp ha).2
    apply mem_compl.mpr
    intro hfw
    have hh:=hW (f a) hfw
    have hl:=f.degree_le a
    omega
  have hforbid : ∀{a b},J.Adj a b → f a=x → f b=w → False := by
    intro a b hab hax hbw
    have hb:=EdgeKernel.critical_copy_val_bound f hmax hc Wᶜ hT hab
    rw [hax,hbw,erase_eq_of_notMem (show w∉Wᶜ from by simpa using hw)] at hb
    have hs:=neighboursIn_add_compl G W x
    have hd:=G.degree_le_maxDegree x
    omega
  intro a b hab heq
  rcases Sym2.eq_iff.mp heq with ⟨ha,hb⟩|⟨ha,hb⟩
  · exact hforbid hab.symm hb ha
  · exact hforbid hab ha hb

/-- Deleting one offending edge preserves exactly the existence of a
colouring with the original maximum palette. -/
theorem colourable_iff_delete_bad_edge
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    (hW : ∀w∈W,G.degree w<G.maxDegree) {w x : V} (hw : w∈W)
    (hbad : G.degree w≤neighboursIn G W x) :
    G.EdgeColorable G.maxDegree ↔
      (G.deleteEdges {s(w,x)}).EdgeColorable G.maxDegree := by
  classical
  apply CriticalCapture.colourable_iff_of_critical_capture (deleteEdges_le _)
  intro c
  let f : c.graph →g G.deleteEdges {s(w,x)} :=
    { toFun:=c.embedding
      map_rel':=by
        intro a b hab
        exact deleteEdges_adj.mpr ⟨c.embedding.toHom.map_adj hab,by
          simpa only [Set.mem_singleton_iff] using
            critical_copy_avoids_bad_edge G W hW c.embedding c.maxDegree_eq c.critical hw hbad hab⟩ }
  exact ⟨f.toCopy c.embedding.injective⟩

omit [Fintype V] [DecidableEq V] in
/-- A deleted cut edge cannot change the graph induced outside W. -/
theorem induce_compl_delete_bad_edge (G : SimpleGraph V) (W : Finset V)
    {w x : V} (hw : w∈W) :
    (G.deleteEdges {s(w,x)}).induce ((W:Set V)ᶜ)=G.induce ((W:Set V)ᶜ) := by
  ext a b
  simp only [induce_adj,deleteEdges_adj,Set.mem_singleton_iff]
  constructor
  · exact And.left
  · intro hab
    refine ⟨hab,?_⟩
    intro he
    rcases Sym2.eq_iff.mp he with ⟨ha,_⟩|⟨_,hb⟩
    · exact a.property (ha ▸ hw)
    · exact b.property (hb ▸ hw)

/-- A finite trace records only actual deletions satisfying the bad-edge
comparison at the moment of deletion. -/
inductive DeletionRun (W : Finset V) : SimpleGraph V → SimpleGraph V → Prop
  | refl (G : SimpleGraph V) : DeletionRun W G G
  | step {G H : SimpleGraph V} [DecidableRel H.Adj]
      (run : DeletionRun W G H) {w x : V} (hw : w∈W)
      (hedge : H.Adj w x) (hbad : H.degree w≤neighboursIn H W x) :
      DeletionRun W G (H.deleteEdges {s(w,x)})

/-- Actual finite deletion terminates at the strict degree comparison.
The proof minimizes a natural edge count among real subgraphs, preserving
both the obstruction and every edge outside W. There is no assumed
sequence of deletions or assumed ability to repeat a two-colour layer. -/
theorem exists_preprocessed_obstruction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnc : ¬G.EdgeColorable G.maxDegree) (W : Finset V)
    (hW : ∀w∈W,G.degree w<G.maxDegree) :
    ∃H : SimpleGraph V,DeletionRun W G H ∧ H≤G ∧ H.maxDegree=G.maxDegree ∧
      ¬H.EdgeColorable H.maxDegree ∧
      H.induce ((W:Set V)ᶜ)=G.induce ((W:Set V)ᶜ) ∧
      (∀w∈W,H.degree w<H.maxDegree) ∧
      ∀w∈W,∀x,H.Adj w x → neighboursIn H W x<H.degree w := by
  classical
  have hex : ∃m : ℕ,∃H : SimpleGraph V,H≤G ∧ H.edgeSet.ncard=m ∧
      ¬H.EdgeColorable G.maxDegree ∧ DeletionRun W G H ∧
      H.induce ((W:Set V)ᶜ)=G.induce ((W:Set V)ᶜ) :=
    ⟨G.edgeSet.ncard,G,le_rfl,rfl,hnc,DeletionRun.refl G,rfl⟩
  obtain ⟨H,hHG,hcount,hncH,hrun,hcore⟩:=Nat.find_spec hex
  have hmax : H.maxDegree=G.maxDegree:=Critical.maxDegree_eq_of_obstruction hHG hncH
  have hWH : ∀w∈W,H.degree w<H.maxDegree := by
    intro w hw
    have hl:=H.degree_le_of_le hHG (v:=w)
    have hh:=hW w hw
    omega
  refine ⟨H,hrun,hHG,hmax,by rwa [hmax],hcore,hWH,?_⟩
  intro w hw x hwx
  by_contra hnot
  have hbad : H.degree w≤neighboursIn H W x := by omega
  let J:=H.deleteEdges {s(w,x)}
  have hncJ : ¬J.EdgeColorable G.maxDegree := by
    intro hcol
    apply hncH
    have hh := (colourable_iff_delete_bad_edge H W hWH hw hbad).mpr
      (by simpa only [hmax] using hcol)
    simpa only [hmax] using hh
  have hJcore : J.induce ((W:Set V)ᶜ)=G.induce ((W:Set V)ᶜ) :=
    (induce_compl_delete_bad_edge H W hw).trans hcore
  have hlt : J.edgeSet.ncard<Nat.find hex := by
    rw [←hcount]
    apply Set.ncard_lt_ncard _ (Set.toFinite _)
    rw [edgeSet_deleteEdges]
    exact Set.sdiff_ssubset_left_iff.mpr ⟨s(w,x),hwx,rfl⟩
  exact Nat.find_min hex hlt ⟨J,(deleteEdges_le _).trans hHG,rfl,hncJ,DeletionRun.step hrun hw hwx hbad,hJcore⟩

end OverfullWork.LowSetEdgePreprocessing
