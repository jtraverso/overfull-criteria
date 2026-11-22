module

public import OverfullWork.CopyNeighbourSaturation
public import OverfullWork.MaximumTwoCore

@[expose] public section


/-! # A deficit-aware local filter preserving critical maximum vertices

This filter is a certified additional reduction, not an assumption that
an arbitrary low-degree vertex can be removed from a colouring problem.
-/
namespace OverfullWork.PrunedCore
open SimpleGraph Finset
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def deficitFilter (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) : Finset V :=
  T.filter fun b => ∀ a,G.Adj b a → G.maxDegree-G.degree a+1≤neighboursIn G T b

theorem deficitFilter_subset (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) :
    deficitFilter G T⊆T:=filter_subset _ _

theorem deficitFilter_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hST : S⊆T) : deficitFilter G S⊆deficitFilter G T := by
  intro b hb
  obtain ⟨hbS,hbound⟩:=mem_filter.mp hb
  exact mem_filter.mpr ⟨hST hbS,fun a ha => (hbound a ha).trans (neighboursIn_mono G hST b)⟩

/-- Saturation at a maximum vertex lifts every ambient edge to the
critical copy. VAL then pays at least the ambient neighbour's deficit. -/
theorem critical_copy_deficit_bound {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (T : Finset V)
    (hT : ((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f⊆T)
    (b : W) (hb : H.degree b=H.maxDegree) {a : V} (hba : G.Adj (f b) a) :
    G.maxDegree-G.degree a+1≤neighboursIn G T (f b) := by
  obtain ⟨z,hbz,hfz⟩:=f.exists_adj_preimage_of_maximum_degree hmax b hb hba
  have hdeg : H.degree z≤G.degree a := by
    have hh:=f.degree_le z
    have hfz' : f z=a:=hfz
    change H.degree z≤G.degree (f z) at hh
    rw [hfz'] at hh
    exact hh
  have hHdeg:=H.degree_le_maxDegree z
  have hGdeg:=G.degree_le_maxDegree a
  have hdef : G.maxDegree-G.degree a+1≤H.maxDegree-H.degree z+1:=by omega
  have hval:=Gate8J2C.deficit_le_maximumNeighbours H hcrit hbz
  have hrow : Gate8J2C.maximumNeighbours H b=
      neighboursIn H (univ.filter fun z => H.degree z=H.maxDegree) b := by
    simp only [Gate8J2C.maximumNeighbours,neighboursIn,mem_filter,mem_univ,true_and]
  rw [hrow] at hval
  exact hdef.trans (hval.trans ((copy_neighboursIn_le f _ b).trans (neighboursIn_mono G hT (f b))))

/-- Every maximum vertex of the critical copy survives one deficit-aware
filtering step as soon as its maximum-vertex image is contained in T. -/
theorem critical_maximum_image_subset_deficitFilter {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (T : Finset V)
    (hT : ((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f⊆T) :
    ((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f⊆deficitFilter G T := by
  intro b hb
  have hbT:=hT hb
  obtain ⟨z,hz,rfl⟩:=mem_image.mp hb
  refine mem_filter.mpr ⟨hbT,?_⟩
  intro a hza
  exact critical_copy_deficit_bound f hmax hcrit T hT z (mem_filter.mp hz).2 hza

end OverfullWork.PrunedCore
