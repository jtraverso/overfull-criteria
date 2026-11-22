module

public import OverfullWork.TightMaximumPropagation
public import Mathlib.Logic.Relation

@[expose] public section


/-! # Directed propagation of genuine maximum roles

A tight local deficit at b forces its candidate-core neighbours to be
maximum vertices of any critical copy in which b is maximum. The tight
condition is imposed only at the origin, so the relation is directed.
-/
namespace OverfullWork.EdgeKernel
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def tightRoleStep (G : SimpleGraph V) [DecidableRel G.Adj]
    (b c : V) : Prop :=
  b∈DeficitCore.core G ∧ c∈DeficitCore.core G ∧ G.Adj b c ∧
    ∃a,G.Adj b a ∧
      neighboursIn G (DeficitCore.core G) b=G.maxDegree-G.degree a+1

theorem maximum_role_of_tightRoleStep
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀x,0<H.degree x)
    {b : W} {c : V} (hbD : H.degree b=H.maxDegree)
    (hstep : tightRoleStep G (f b) c) :
    ∃z,f z=c ∧ H.degree z=H.maxDegree := by
  obtain ⟨_,hc,hbc,a,hba,hta⟩ := hstep
  obtain ⟨aH,hbaH,haH⟩ := f.exists_adj_preimage_of_maximum_degree hmax b hbD hba
  have htight : neighboursIn G (DeficitCore.core G) (f b)=
      G.maxDegree-G.degree (f aH)+1 := by
    rw [haH]
    exact hta
  obtain ⟨z,_,hz,hzD⟩ := maximum_neighbour_preimage_of_tight_deficit
    f hmax hcrit (DeficitCore.core G)
    (DeficitCore.critical_maximum_image_subset_core f hmax hcrit hactive)
    hbaH htight hbc hc
  exact ⟨z,hz,hzD⟩

/-- Every endpoint reached from a genuine maximum seed is a genuine
maximum vertex, without a clique or symmetry assumption. -/
theorem maximum_role_of_reachable
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀x,0<H.degree x)
    {b : W} {c : V} (hbD : H.degree b=H.maxDegree)
    (hreach : Relation.ReflTransGen (tightRoleStep G) (f b) c) :
    ∃z,f z=c ∧ H.degree z=H.maxDegree := by
  induction hreach with
  | refl => exact ⟨b,rfl,hbD⟩
  | tail _ hstep ih =>
    obtain ⟨z,hz,hzD⟩ := ih
    apply maximum_role_of_tightRoleStep f hmax hcrit hactive hzD
    simpa only [hz] using hstep

theorem critical_maximum_image_tightRoleStep_closed
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀x,0<H.degree x)
    {b c : V}
    (hb : b∈((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f)
    (hstep : tightRoleStep G b c) :
    c∈((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f := by
  obtain ⟨bH,hbH,rfl⟩ := mem_image.mp hb
  obtain ⟨z,hz,hzD⟩ := maximum_role_of_tightRoleStep f hmax hcrit hactive
    (mem_filter.mp hbH).2 hstep
  exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ z,hzD⟩,hz⟩

theorem critical_maximum_image_reachable_closed
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀x,0<H.degree x)
    {b c : V}
    (hb : b∈((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f)
    (hreach : Relation.ReflTransGen (tightRoleStep G) b c) :
    c∈((univ : Finset W).filter fun z => H.degree z=H.maxDegree).image f := by
  obtain ⟨bH,hbH,rfl⟩ := mem_image.mp hb
  obtain ⟨z,hz,hzD⟩ := maximum_role_of_reachable f hmax hcrit hactive
    (mem_filter.mp hbH).2 hreach
  exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ z,hzD⟩,hz⟩

end OverfullWork.EdgeKernel
