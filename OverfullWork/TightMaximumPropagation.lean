module

public import OverfullWork.TightDeficitSaturation

@[expose] public section


/-! # Tight VAL budgets force all candidate maximum neighbours

Equality of the local budget saturates both a degree and a finite
neighbour count. Every candidate neighbour in that count is therefore
the image of a genuine maximum-degree vertex of the critical copy.
-/
namespace OverfullWork.EdgeKernel
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]

theorem maximum_neighbours_image_eq_of_tight_deficit (f : Copy H G)
    (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (T : Finset V)
    (hT : ((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f⊆T)
    {b a : W} (hba : H.Adj b a)
    (htight : neighboursIn G T (f b)=G.maxDegree-G.degree (f a)+1) :
    ((H.neighborFinset b).filter fun z => H.degree z=H.maxDegree).image f =
      (G.neighborFinset (f b)).filter fun y => y∈T := by
  let A := (H.neighborFinset b).filter fun z => H.degree z=H.maxDegree
  let B := (G.neighborFinset (f b)).filter fun y => y∈T
  have hs : A.image f⊆B := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
    obtain ⟨hzN,hzD⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨(mem_neighborFinset G _ _).mpr
      (f.toHom.map_adj ((mem_neighborFinset H _ _).mp hzN)),
      hT (mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ z,hzD⟩,rfl⟩)⟩
  have hv := Gate8J2C.deficit_le_maximumNeighbours H hcrit hba
  have hd := f.degree_le a
  have hHd := H.degree_le_maxDegree a
  have hGd := G.degree_le_maxDegree (f a)
  change H.maxDegree-H.degree a+1≤A.card at hv
  have hB : B.card=G.maxDegree-G.degree (f a)+1 := htight
  have himage : (A.image f).card=A.card :=
    card_image_of_injective A (fun _ _ he => f.injective he)
  apply Finset.eq_of_subset_of_card_le hs
  omega

/-- No maximum-role assumption on b is needed: its tight neighbour
count already forces every candidate maximum neighbour to be genuine. -/
theorem maximum_neighbour_preimage_of_tight_deficit (f : Copy H G)
    (hmax : H.maxDegree=G.maxDegree) (hcrit : Overfull.IsDeltaCritical H)
    (T : Finset V)
    (hT : ((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f⊆T)
    {b a : W} (hba : H.Adj b a)
    (htight : neighboursIn G T (f b)=G.maxDegree-G.degree (f a)+1)
    {y : V} (hby : G.Adj (f b) y) (hyT : y∈T) :
    ∃z,H.Adj b z ∧ f z=y ∧ H.degree z=H.maxDegree := by
  have hy : y∈((H.neighborFinset b).filter fun z => H.degree z=H.maxDegree).image f := by
    rw [maximum_neighbours_image_eq_of_tight_deficit f hmax hcrit T hT hba htight]
    exact mem_filter.mpr ⟨(mem_neighborFinset G _ _).mpr hby,hyT⟩
  obtain ⟨z,hz,hzy⟩ := mem_image.mp hy
  obtain ⟨hzN,hzD⟩ := mem_filter.mp hz
  exact ⟨z,(mem_neighborFinset H _ _).mp hzN,hzy,hzD⟩

end OverfullWork.EdgeKernel
