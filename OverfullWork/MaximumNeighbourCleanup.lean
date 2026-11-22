module

public import OverfullWork.LowSetEdgePreprocessing

@[expose] public section


/-! # CMS Algorithm 2: actual maximum-degree-neighbour cleanup

Source: Chen--McDonald--Shan, Towards the Overfull Conjecture II,
Lemma 3.9 and Algorithm 2. The source need only be class two, not critical.
Each deleted edge violates the maximum-neighbour inequality and hence
belongs to no common-Delta critical copy. Actual finite deletion preserves
the palette obstruction, maximum degree and the induced graph outside W.
Isolated vertices may remain on the fixed ambient type.
-/
namespace OverfullWork.MaximumNeighbourCleanup
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

def maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun z=>G.degree z=G.maxDegree

/-- The bad edge cannot occur in any critical copy with the same maximum. -/
theorem critical_copy_avoids_bad_edge
    {A : Type v} [Fintype A] [DecidableEq A]
    {J : SimpleGraph A} [DecidableRel J.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Copy J G) (hMax : J.maxDegree=G.maxDegree) (hc : Overfull.IsDeltaCritical J)
    {w x : V} (hw : G.degree w<G.maxDegree)
    (hBad : G.degree w+neighboursIn G (maximumVertices G) x≤G.maxDegree) :
    ∀{a b},J.Adj a b → s(f a,f b)≠s(w,x) := by
  have hImage:((univ:Finset A).filter fun z=>J.degree z=J.maxDegree).image f⊆maximumVertices G:=by
    intro z hz
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hz
    have hDa:=(mem_filter.mp ha).2
    have hLo:=f.degree_le a
    have hHi:=G.degree_le_maxDegree (f a)
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hwNot:w∉maximumVertices G:=by
    intro h
    have he:=(mem_filter.mp h).2
    omega
  have hForbid:∀{a b},J.Adj a b → f a=x → f b=w → False:=by
    intro a b hab ha hb
    have hVal:=EdgeKernel.critical_copy_val_bound f hMax hc (maximumVertices G) hImage hab
    rw [ha,hb,erase_eq_of_notMem hwNot] at hVal
    omega
  intro a b hab he
  rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩|⟨ha,hb⟩
  · exact hForbid hab.symm hb ha
  · exact hForbid hab ha hb

/-- Lemma 3.9 in the exact fixed-palette form needed by the algorithm. -/
theorem colourable_iff_delete_bad_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {w x : V} (hw : G.degree w<G.maxDegree)
    (hBad : G.degree w+neighboursIn G (maximumVertices G) x≤G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔ (G.deleteEdges {s(w,x)}).EdgeColorable G.maxDegree := by
  classical
  apply CriticalCapture.colourable_iff_of_critical_capture (deleteEdges_le _)
  intro c
  let f:c.graph→g G.deleteEdges {s(w,x)}:={
    toFun:=c.embedding
    map_rel':=by
      intro a b hab
      exact deleteEdges_adj.mpr ⟨c.embedding.toHom.map_adj hab,by
        simpa only [Set.mem_singleton_iff] using
          critical_copy_avoids_bad_edge G c.embedding c.maxDegree_eq c.critical hw hBad hab⟩ }
  exact ⟨f.toCopy c.embedding.injective⟩

inductive DeletionRun (W : Finset V) : SimpleGraph V→SimpleGraph V→Prop
  | refl (G : SimpleGraph V) : DeletionRun W G G
  | step {G H : SimpleGraph V} [DecidableRel H.Adj]
      (run : DeletionRun W G H) {w x : V} (hw : w∈W) (hEdge : H.Adj w x)
      (hBad : H.degree w+neighboursIn H (maximumVertices H) x≤H.maxDegree) :
      DeletionRun W G (H.deleteEdges {s(w,x)})

theorem DeletionRun.le {W : Finset V} {G H : SimpleGraph V} (p : DeletionRun W G H) : H≤G := by
  induction p with
  | refl => exact le_rfl
  | step p _ _ _ ih => exact (deleteEdges_le _).trans ih

/-- For the independent-set input of the paper, every eligible edge
at every actual prefix crosses the cut. The general deletion primitive
does not need to assume independence separately at each step. -/
theorem DeletionRun.edge_crosses {W : Finset V} {G H : SimpleGraph V}
    (p : DeletionRun W G H) (hInd : G.IsIndepSet (W:Set V))
    {w x : V} (hw : w∈W) (hEdge : H.Adj w x) : x∉W := by
  intro hx
  have hOriginal:=p.le hEdge
  exact hInd hw hx hOriginal.ne hOriginal

/-- A real finite run terminates at the published maximum-neighbour
inequality. The class-two obstruction, not criticality, is preserved. -/
theorem exists_cleanup (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnc : ¬G.EdgeColorable G.maxDegree) (W : Finset V)
    (hW : ∀w∈W,G.degree w<G.maxDegree) :
    ∃H : SimpleGraph V,DeletionRun W G H ∧ H≤G ∧ H.maxDegree=G.maxDegree ∧
      ¬H.EdgeColorable H.maxDegree ∧ H.induce ((W:Set V)ᶜ)=G.induce ((W:Set V)ᶜ) ∧
      (∀w∈W,H.degree w<H.maxDegree) ∧
      ∀w∈W,∀x,H.Adj w x → H.maxDegree+1≤H.degree w+neighboursIn H (maximumVertices H) x := by
  classical
  have hex:∃m:ℕ,∃H:SimpleGraph V,H≤G ∧ H.edgeSet.ncard=m ∧
      ¬H.EdgeColorable G.maxDegree ∧ DeletionRun W G H ∧
      H.induce ((W:Set V)ᶜ)=G.induce ((W:Set V)ᶜ):=
    ⟨G.edgeSet.ncard,G,le_rfl,rfl,hnc,DeletionRun.refl G,rfl⟩
  obtain ⟨H,hHG,hCount,hNC,hRun,hCore⟩:=Nat.find_spec hex
  have hMax:H.maxDegree=G.maxDegree:=Critical.maxDegree_eq_of_obstruction hHG hNC
  have hWH:∀w∈W,H.degree w<H.maxDegree:=by
    intro w hw
    have hLo:=H.degree_le_of_le hHG (v:=w)
    have hOld:=hW w hw
    omega
  refine ⟨H,hRun,hHG,hMax,by rwa [hMax],hCore,hWH,?_⟩
  intro w hw x hEdge
  by_contra hNot
  have hBad:H.degree w+neighboursIn H (maximumVertices H) x≤H.maxDegree:=by omega
  let J:=H.deleteEdges {s(w,x)}
  have hNCJ:¬J.EdgeColorable G.maxDegree:=by
    intro hCol
    apply hNC
    have hBack:=(colourable_iff_delete_bad_edge H (hWH w hw) hBad).mpr
      (by simpa only [hMax] using hCol)
    simpa only [hMax] using hBack
  have hJCore:J.induce ((W:Set V)ᶜ)=G.induce ((W:Set V)ᶜ):=
    (LowSetEdgePreprocessing.induce_compl_delete_bad_edge H W hw).trans hCore
  have hLt:J.edgeSet.ncard<Nat.find hex:=by
    rw [←hCount]
    apply Set.ncard_lt_ncard _ (Set.toFinite _)
    rw [edgeSet_deleteEdges]
    exact Set.sdiff_ssubset_left_iff.mpr ⟨s(w,x),hEdge,rfl⟩
  exact Nat.find_min hex hLt ⟨J,(deleteEdges_le _).trans hHG,rfl,hNCJ,
    DeletionRun.step hRun hw hEdge hBad,hJCore⟩

/-- Cleanup preserves original no-overfullness because it only removes
edges while keeping the maximum degree exactly unchanged. -/
theorem exists_cleanup_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnc : ¬G.EdgeColorable G.maxDegree) (W : Finset V)
    (hW : ∀w∈W,G.degree w<G.maxDegree) (hNo : ¬G.HasOverfullSubgraph) :
    ∃H : SimpleGraph V,DeletionRun W G H ∧ H≤G ∧ H.maxDegree=G.maxDegree ∧
      ¬H.EdgeColorable H.maxDegree ∧ ¬H.HasOverfullSubgraph ∧
      H.induce ((W:Set V)ᶜ)=G.induce ((W:Set V)ᶜ) ∧
      (∀w∈W,H.degree w<H.maxDegree) ∧
      ∀w∈W,∀x,H.Adj w x → H.maxDegree+1≤H.degree w+neighboursIn H (maximumVertices H) x := by
  classical
  obtain ⟨H,hRun,hHG,hMax,hNC,hCore,hWH,hFinal⟩:=exists_cleanup G hnc W hW
  exact ⟨H,hRun,hHG,hMax,hNC,Critical.no_overfull_of_copy (Copy.ofLE H G hHG) hMax hNo,
    hCore,hWH,hFinal⟩

/-- Maximum vertices and the prescribed nonmaximum set spend disjoint
parts of every actual neighbourhood. -/
theorem neighbours_set_add_maximum_le (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Finset V) (hW : ∀w∈W,H.degree w<H.maxDegree) (x : V) :
    neighboursIn H W x+neighboursIn H (maximumVertices H) x≤H.degree x := by
  have hDis:Disjoint ((H.neighborFinset x).filter fun z=>z∈W)
      ((H.neighborFinset x).filter fun z=>z∈maximumVertices H):=by
    apply Finset.disjoint_left.mpr
    intro z hzW hzM
    have hlt:=hW z (mem_filter.mp hzW).2
    have he:=(mem_filter.mp (mem_filter.mp hzM).2).2
    omega
  have hCount:=card_le_card (union_subset (filter_subset _ _) (filter_subset _ _) :
    ((H.neighborFinset x).filter fun z=>z∈W)∪
      ((H.neighborFinset x).filter fun z=>z∈maximumVertices H)⊆H.neighborFinset x)
  rw [card_union_of_disjoint hDis,card_neighborFinset_eq_degree] at hCount
  exact hCount

/-- The stopping rule of Algorithm 2 implies the Hall property used by
CMS Lemma 3.4, with no criticality hypothesis on the cleaned graph. -/
theorem hall_of_final_inequality (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Finset V) (hW : ∀w∈W,H.degree w<H.maxDegree)
    (hFinal : ∀w∈W,∀x,H.Adj w x →
      H.maxDegree+1≤H.degree w+neighboursIn H (maximumVertices H) x) :
    ∀w∈W,∀x,H.Adj w x → neighboursIn H W x<H.degree w := by
  intro w hw x hEdge
  have hVal:=hFinal w hw x hEdge
  have hCount:=neighbours_set_add_maximum_le H W hW x
  have hDx:=H.degree_le_maxDegree x
  omega

/-- In the cleaned graph every surviving edge incident with W also has
the weak-VAL degree sum Delta+2 required in Claim 4.5. -/
theorem degree_sum_of_final_inequality (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Finset V) (hW : ∀w∈W,H.degree w<H.maxDegree)
    (hFinal : ∀w∈W,∀x,H.Adj w x →
      H.maxDegree+1≤H.degree w+neighboursIn H (maximumVertices H) x) :
    ∀w∈W,∀x,H.Adj w x → H.maxDegree+2≤H.degree w+H.degree x := by
  intro w hw x hEdge
  have hVal:=hFinal w hw x hEdge
  have hCount:=neighbours_set_add_maximum_le H W hW x
  have hPositive:1≤neighboursIn H W x:=by
    apply card_pos.mpr
    exact ⟨w,mem_filter.mpr ⟨(mem_neighborFinset H x w).mpr hEdge.symm,hw⟩⟩
  omega

/-- An actual completed Algorithm 2 run supplies all three local
conditions used by the paper: maximum-neighbour, Hall and degree-sum. -/
theorem exists_cleanup_ready (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnc : ¬G.EdgeColorable G.maxDegree) (W : Finset V)
    (hW : ∀w∈W,G.degree w<G.maxDegree) :
    ∃H : SimpleGraph V,DeletionRun W G H ∧ H≤G ∧ H.maxDegree=G.maxDegree ∧
      ¬H.EdgeColorable H.maxDegree ∧ H.induce ((W:Set V)ᶜ)=G.induce ((W:Set V)ᶜ) ∧
      (∀w∈W,H.degree w<H.maxDegree) ∧
      (∀w∈W,∀x,H.Adj w x → H.maxDegree+1≤H.degree w+neighboursIn H (maximumVertices H) x) ∧
      (∀w∈W,∀x,H.Adj w x → neighboursIn H W x<H.degree w) ∧
      ∀w∈W,∀x,H.Adj w x → H.maxDegree+2≤H.degree w+H.degree x := by
  classical
  obtain ⟨H,hRun,hHG,hMax,hNC,hCore,hWH,hFinal⟩:=exists_cleanup G hnc W hW
  exact ⟨H,hRun,hHG,hMax,hNC,hCore,hWH,hFinal,
    hall_of_final_inequality H W hWH hFinal,degree_sum_of_final_inequality H W hWH hFinal⟩

end OverfullWork.MaximumNeighbourCleanup
