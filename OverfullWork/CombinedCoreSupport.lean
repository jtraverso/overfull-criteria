module

public import OverfullWork.CombinedDeficitCore

@[expose] public section


/-! # Critical capture by the support of the combined core -/
namespace OverfullWork.DeficitCore
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Vertices with at least two neighbours in the combined core. -/
noncomputable def candidateSupport (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun x => 2 ≤ neighboursIn G (core G) x

theorem mem_candidateSupport (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    x ∈ candidateSupport G ↔ 2 ≤ neighboursIn G (core G) x := by
  simp only [candidateSupport, mem_filter, mem_univ, true_and]

theorem core_subset_candidateSupport (G : SimpleGraph V) [DecidableRel G.Adj] :
    core G ⊆ candidateSupport G := by
  intro x hx
  exact (mem_candidateSupport G x).mpr ((core_is_admissible G).1 x hx).2.1

/-- The closed neighbourhood of each core vertex is contained in the support. -/
theorem core_neighbours_mem_candidateSupport (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} (hx : x ∈ core G) (hxy : G.Adj x y) : y ∈ candidateSupport G :=
  (mem_candidateSupport G y).mpr (((core_is_admissible G).1 x hx).2.2 y hxy)

/-- Every vertex of a common-Δ critical copy has two neighbours in the core. -/
theorem critical_vertex_mem_candidateSupport
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree = G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀ w, 0 < H.degree w) (x : W) :
    f x ∈ candidateSupport G := by
  classical
  let T := (univ : Finset W).filter fun z => H.degree z = H.maxDegree
  have hn : 2 ≤ neighboursIn H T x := by
    simpa only [neighboursIn, T, mem_filter, mem_univ, true_and,
      Gate8J2C.maximumNeighbours] using
      Gate8J2C.critical_maximumNeighbours_ge_two H hcrit hactive x
  have hsub : T.image f ⊆ core G :=
    critical_maximum_image_subset_core f hmax hcrit hactive
  exact (mem_candidateSupport G (f x)).mpr
    (hn.trans ((copy_neighboursIn_le f T x).trans (neighboursIn_mono G hsub (f x))))

/-- The support captures the entire critical obstruction, not just its core. -/
theorem critical_image_subset_candidateSupport
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree = G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀ w, 0 < H.degree w) :
    (univ : Finset W).image f ⊆ candidateSupport G := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := mem_image.mp hy
  exact critical_vertex_mem_candidateSupport f hmax hcrit hactive x

end OverfullWork.DeficitCore
