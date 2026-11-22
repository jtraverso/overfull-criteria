module

public import OverfullWork.MaximumTwoCore
public import OverfullWork.CopyNeighbourSaturation

@[expose] public section


/-! # A maximum-degree kernel retaining saturation at every neighbour

A vertex is retained only when it has two neighbours in the candidate
set and all of its ambient neighbours also have two neighbours there.
The union of admissible sets is the greatest fixed point within the
maximum-degree vertices.  Degree equality is used only at maximum
vertices when transporting this property through a graph copy.
-/
namespace OverfullWork.SaturatedCore
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def saturatedStep (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) : Finset V :=
  T.filter fun x => 2≤neighboursIn G T x ∧ ∀ y,G.Adj x y → 2≤neighboursIn G T y

def IsSaturatedCoreSet (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : Prop :=
  ∀ x∈T,G.degree x=G.maxDegree ∧ 2≤neighboursIn G T x ∧
    ∀ y,G.Adj x y → 2≤neighboursIn G T y

noncomputable def saturatedCore (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun x => ∃ T : Finset V,IsSaturatedCoreSet G T ∧ x∈T

theorem mem_saturatedCore (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    x∈saturatedCore G ↔ ∃ T : Finset V,IsSaturatedCoreSet G T ∧ x∈T := by
  simp only [saturatedCore,mem_filter,mem_univ,true_and]

theorem saturatedStep_subset (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) :
    saturatedStep G T⊆T := filter_subset _ _

theorem saturatedStep_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hST : S⊆T) : saturatedStep G S⊆saturatedStep G T := by
  intro x hx
  obtain ⟨hxS,hx,hn⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hST hxS,hx.trans (neighboursIn_mono G hST x),
    fun y hy => (hn y hy).trans (neighboursIn_mono G hST y)⟩

theorem saturatedSet_subset_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : IsSaturatedCoreSet G T) : T⊆saturatedCore G := by
  intro x hx
  exact (mem_saturatedCore G x).mpr ⟨T,hT,hx⟩

theorem saturatedCore_isSaturatedCoreSet (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsSaturatedCoreSet G (saturatedCore G) := by
  intro x hx
  obtain ⟨T,hT,hxT⟩ := (mem_saturatedCore G x).mp hx
  obtain ⟨hd,hxN,hn⟩ := hT x hxT
  have hsub := saturatedSet_subset_core G T hT
  exact ⟨hd,hxN.trans (neighboursIn_mono G hsub x),
    fun y hy => (hn y hy).trans (neighboursIn_mono G hsub y)⟩

theorem saturatedCore_subset_maximumTwoCore (G : SimpleGraph V) [DecidableRel G.Adj] :
    saturatedCore G⊆maximumTwoCore G := by
  apply coreSet_subset_maximumTwoCore
  intro x hx
  have h := saturatedCore_isSaturatedCoreSet G x hx
  exact ⟨h.1,h.2.1⟩

theorem saturatedCore_subset_maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] :
    saturatedCore G⊆univ.filter fun x => G.degree x=G.maxDegree :=
  (saturatedCore_subset_maximumTwoCore G).trans (maximumTwoCore_subset_maximumVertices G)

theorem saturatedCore_fixedpoint (G : SimpleGraph V) [DecidableRel G.Adj] :
    saturatedStep G (saturatedCore G)=saturatedCore G := by
  apply subset_antisymm (saturatedStep_subset G _)
  intro x hx
  exact mem_filter.mpr ⟨hx,(saturatedCore_isSaturatedCoreSet G x hx).2⟩

/-- The kernel is the greatest fixed point of this pruning operator
among subsets of the maximum-degree vertices. -/
theorem fixedpoint_subset_saturatedCore (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hmax : ∀ x∈T,G.degree x=G.maxDegree)
    (hfix : saturatedStep G T=T) : T⊆saturatedCore G := by
  apply saturatedSet_subset_core
  intro x hx
  have hxstep : x∈saturatedStep G T := by rw [hfix]; exact hx
  exact ⟨hmax x hx,(mem_filter.mp hxstep).2⟩

theorem saturatedCore_survives_step (G : SimpleGraph V) [DecidableRel G.Adj]
    {T : Finset V} (hT : saturatedCore G⊆T) : saturatedCore G⊆saturatedStep G T := by
  rw [←saturatedCore_fixedpoint G]
  exact saturatedStep_mono G hT

/-- Saturation lifts every ambient neighbour of the image of a maximum
vertex.  No equality of degrees is required at that neighbour. -/
theorem saturatedSet_image_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) {T : Finset W}
    (hT : IsSaturatedCoreSet H T) : IsSaturatedCoreSet G (T.image f) := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
  obtain ⟨hxD,hxN,hn⟩ := hT x hx
  have hxG : G.degree (f x)=G.maxDegree := by
    have hl := f.degree_le x
    have hu := G.degree_le_maxDegree (f x)
    omega
  refine ⟨hxG,hxN.trans (copy_neighboursIn_le f T x),?_⟩
  intro y hxy
  obtain ⟨z,hxz,rfl⟩ := f.exists_adj_preimage_of_maximum_degree hmax x hxD hxy
  exact (hn z hxz).trans (copy_neighboursIn_le f T z)

theorem image_saturatedCore_subset_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) :
    (saturatedCore H).image f⊆saturatedCore G :=
  saturatedSet_subset_core G _
    (saturatedSet_image_of_copy f hmax (saturatedCore_isSaturatedCoreSet H))

theorem neighboursIn_maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    neighboursIn G (univ.filter fun y => G.degree y=G.maxDegree) x=
      Gate8J2C.maximumNeighbours G x := by
  unfold neighboursIn Gate8J2C.maximumNeighbours
  congr 1
  ext y
  simp only [mem_filter,mem_univ,true_and]

theorem critical_maximumVertices_isSaturated (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ x,0<G.degree x) :
    IsSaturatedCoreSet G (univ.filter fun x => G.degree x=G.maxDegree) := by
  intro x hx
  refine ⟨(mem_filter.mp hx).2,?_,?_⟩
  · rw [neighboursIn_maximumVertices]
    exact Gate8J2C.critical_maximumNeighbours_ge_two G hcrit hactive x
  · intro y _
    rw [neighboursIn_maximumVertices]
    exact Gate8J2C.critical_maximumNeighbours_ge_two G hcrit hactive y

theorem critical_maximum_image_subset_saturatedCore {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀ x,0<H.degree x) :
    (univ.filter fun x => H.degree x=H.maxDegree).image f⊆saturatedCore G :=
  saturatedSet_subset_core G _ (saturatedSet_image_of_copy f hmax
    (critical_maximumVertices_isSaturated H hcrit hactive))

theorem critical_maximum_image_survives_step {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀ x,0<H.degree x)
    (T : Finset V) (hT : (univ.filter fun x => H.degree x=H.maxDegree).image f⊆T) :
    (univ.filter fun x => H.degree x=H.maxDegree).image f⊆saturatedStep G T := by
  have hs := saturatedSet_image_of_copy f hmax
    (critical_maximumVertices_isSaturated H hcrit hactive)
  intro x hx
  obtain ⟨_,hxN,hn⟩ := hs x hx
  exact mem_filter.mpr ⟨hT hx,hxN.trans (neighboursIn_mono G hT x),
    fun y hy => (hn y hy).trans (neighboursIn_mono G hT y)⟩


end OverfullWork.SaturatedCore
