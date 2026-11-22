module

public import OverfullWork.CombinedCoreSupport

@[expose] public section


/-! # Edge pruning by the excluded-neighbour form of VAL

Unlike a further vertex test on the maximum core, this test can discard
edges between nonmaximum vertices. Every common-Delta critical copy
retains all its edges. No extension of a prescribed colouring is asserted.
-/
namespace OverfullWork.EdgeKernel
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

def edgeFilter (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧
    G.maxDegree+1 ≤ G.degree y+neighboursIn G (T.erase y) x ∧
    G.maxDegree+1 ≤ G.degree x+neighboursIn G (T.erase x) y
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) :
    DecidableRel (edgeFilter G T).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

noncomputable def filteredGraph (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph V :=
  edgeFilter G (DeficitCore.core G)

noncomputable instance (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (filteredGraph G).Adj := by unfold filteredGraph; infer_instance

theorem edgeFilter_le (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) :
    edgeFilter G T ≤ G := fun _ _ h => h.1

theorem filteredGraph_le (G : SimpleGraph V) [DecidableRel G.Adj] : filteredGraph G ≤ G :=
  edgeFilter_le G _

theorem neighboursIn_le_erase_add_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (x y : V) :
    neighboursIn G T x ≤ neighboursIn G (T.erase y) x+1 := by
  have hs : ((G.neighborFinset x).filter fun z => z∈T) ⊆
      insert y ((G.neighborFinset x).filter fun z => z∈T.erase y) := by
    intro z hz
    obtain ⟨hzN,hzT⟩ := mem_filter.mp hz
    by_cases he : z=y
    · exact mem_insert.mpr (Or.inl he)
    · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hzN,mem_erase.mpr ⟨he,hzT⟩⟩))
  exact (card_le_card hs).trans (card_insert_le _ _)

theorem copy_neighboursIn_erase_le
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (T : Finset W) (y x : W) :
    neighboursIn H (T.erase y) x ≤
      neighboursIn G ((T.image f).erase (f y)) (f x) := by
  apply (copy_neighboursIn_le f (T.erase y) x).trans
  apply neighboursIn_mono G
  intro z hz
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
  obtain ⟨hay,haT⟩ := mem_erase.mp ha
  exact mem_erase.mpr ⟨fun he => hay (f.injective he),mem_image.mpr ⟨a,haT,rfl⟩⟩

theorem copy_val_bound
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (T : Finset V)
    (hT : ((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f ⊆ T)
    {x y : W}
    (hval : H.maxDegree+1 ≤ H.degree y+neighboursIn H
      (((univ : Finset W).filter fun z => H.degree z=H.maxDegree).erase y) x) :
    G.maxDegree+1 ≤ G.degree (f y)+neighboursIn G (T.erase (f y)) (f x) := by
  have hc := copy_neighboursIn_erase_le f
    ((univ : Finset W).filter fun z => H.degree z=H.maxDegree) y x
  have hs : (((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f).erase (f y)
      ⊆ T.erase (f y) := by
    intro z hz
    exact mem_erase.mpr ⟨(mem_erase.mp hz).1,hT (mem_erase.mp hz).2⟩
  have hb := hc.trans (neighboursIn_mono G hs (f x))
  have hd := f.degree_le y
  omega

/-- VAL's exclusion survives injective copies even when the excluded
ambient vertex is a candidate maximum but its preimage is not maximum. -/
theorem critical_copy_val_bound
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (T : Finset V)
    (hT : ((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f ⊆ T)
    {x y : W} (hxy : H.Adj x y) :
    G.maxDegree+1 ≤ G.degree (f y)+neighboursIn G (T.erase (f y)) (f x) := by
  apply copy_val_bound f hmax T hT
  simpa only [neighboursIn,mem_erase,mem_filter,mem_univ,true_and] using
    Overfull.val_crit hcrit hxy

def critical_copy_to_edgeFilter
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (T : Finset V)
    (hT : ((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f ⊆ T) :
    Copy H (edgeFilter G T) :=
  SimpleGraph.Hom.toCopy ({ toFun := f, map_rel' := fun hxy => ⟨f.toHom.map_adj hxy,
       critical_copy_val_bound f hmax hcrit T hT hxy,
       critical_copy_val_bound f hmax hcrit T hT hxy.symm⟩ } : H →g edgeFilter G T)
    (fun _ _ he => f.injective he)

noncomputable def critical_copy_to_filteredGraph
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀x,0<H.degree x) :
    Copy H (filteredGraph G) :=
  critical_copy_to_edgeFilter f hmax hcrit _
    (DeficitCore.critical_maximum_image_subset_core f hmax hcrit hactive)

/-- Edges incident with retained maximum vertices are unchanged. -/
theorem core_edge_survives (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} (hx : x∈DeficitCore.core G) (hxy : G.Adj x y) :
    (filteredGraph G).Adj x y := by
  have hxD := ((DeficitCore.core_is_admissible G).1 x hx).1
  have hxN := ((DeficitCore.core_is_admissible G).1 x hx).2.1
  have hyN := ((DeficitCore.core_is_admissible G).1 x hx).2.2 y hxy
  have hyE := neighboursIn_le_erase_add_one G (DeficitCore.core G) y x
  refine ⟨hxy,?_,by omega⟩
  by_cases hy : y∈DeficitCore.core G
  · have hyD := ((DeficitCore.core_is_admissible G).1 y hy).1
    have hxE := neighboursIn_le_erase_add_one G (DeficitCore.core G) x y
    omega
  · have hxF : x∈deficitFilter G (DeficitCore.core G) := by
      rw [(DeficitCore.core_is_admissible G).2]
      exact hx
    have hb := (mem_filter.mp hxF).2 y hxy
    rw [erase_eq_of_notMem hy]
    have hd := G.degree_le_maxDegree y
    omega

theorem core_degree_preserved (G : SimpleGraph V) [DecidableRel G.Adj]
    {x : V} (hx : x∈DeficitCore.core G) :
    (filteredGraph G).degree x=G.degree x := by
  rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp only [mem_neighborFinset]
  exact ⟨fun h => h.1,fun h => core_edge_survives G hx h⟩

theorem maxDegree_filteredGraph_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcore : (DeficitCore.core G).Nonempty) : (filteredGraph G).maxDegree=G.maxDegree := by
  obtain ⟨x,hx⟩ := hcore
  have hxD := ((DeficitCore.core_is_admissible G).1 x hx).1
  have he := core_degree_preserved G hx
  have hl := (filteredGraph G).degree_le_maxDegree x
  have hu := (Copy.ofLE _ _ (filteredGraph_le G)).maxDegree_mono
  omega

end OverfullWork.EdgeKernel
