module

public import OverfullWork.CriticalEdgeFilter

@[expose] public section


/-! # Tight local deficits force degree saturation

Equality in the ambient VAL budget forces equality of source and ambient
degrees at the neighbouring vertex. Its entire ambient neighbourhood
therefore lifts to the critical copy.
-/
namespace OverfullWork.EdgeKernel
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]

theorem degree_eq_of_tight_deficit (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (T : Finset V)
    (hT : ((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f⊆T)
    {b a : W} (hba : H.Adj b a)
    (htight : neighboursIn G T (f b)=G.maxDegree-G.degree (f a)+1) :
    H.degree a=G.degree (f a) := by
  have hv:=Gate8J2C.deficit_le_maximumNeighbours H hcrit hba
  have hc:=(copy_neighboursIn_le f
    (univ.filter fun z => H.degree z=H.maxDegree) b).trans
    (neighboursIn_mono G hT (f b))
  rw [SaturatedCore.neighboursIn_maximumVertices] at hc
  have hH:=H.degree_le_maxDegree a
  have hG:=G.degree_le_maxDegree (f a)
  have hm:=f.degree_le a
  omega

theorem exists_adj_preimage_of_tight_deficit (f : Copy H G)
    (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (T : Finset V)
    (hT : ((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f⊆T)
    {b a : W} (hba : H.Adj b a)
    (htight : neighboursIn G T (f b)=G.maxDegree-G.degree (f a)+1)
    {y : V} (hay : G.Adj (f a) y) :
    ∃ z : W,H.Adj a z ∧ f z=y :=
  f.exists_adj_preimage_of_degree_eq a
    (degree_eq_of_tight_deficit f hmax hcrit T hT hba htight) hay

/-- Every edge at a tight neighbour is forced, even when that neighbour
is not a maximum-degree vertex. -/
theorem edge_survives_of_tight_deficit (f : Copy H G)
    (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (hactive : ∀ x,0<H.degree x) {b a : W} (hba : H.Adj b a)
    (htight : neighboursIn G (DeficitCore.core G) (f b)=G.maxDegree-G.degree (f a)+1)
    {y : V} (hay : G.Adj (f a) y) : (filteredGraph G).Adj (f a) y := by
  obtain ⟨z,haz,hz⟩:=exists_adj_preimage_of_tight_deficit f hmax hcrit _
    (DeficitCore.critical_maximum_image_subset_core f hmax hcrit hactive) hba htight hay
  have hh:=(critical_copy_to_filteredGraph f hmax hcrit hactive).toHom.map_adj haz
  change (filteredGraph G).Adj (f a) (f z) at hh
  simpa only [hz] using hh

end OverfullWork.EdgeKernel
