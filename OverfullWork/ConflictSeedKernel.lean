module

public import OverfullWork.TightReachabilityColourability
public import OverfullWork.CombinedCoreDegree
public import OverfullWork.CriticalSupportReduction

@[expose] public section


/-! # Pruning maximum seeds by reachable certified conflicts

Every maximum of a common-Delta critical copy avoids SeedConflict.
Only critical copies are used for the new degree comparison; no
monotonicity under arbitrary graph copies is assumed.
-/
namespace OverfullWork.EdgeKernel
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def admissibleSeeds (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  (DeficitCore.core G).filter fun b => ¬SeedConflict G b

noncomputable def seedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (admissibleSeeds G).sup (neighboursIn G (admissibleSeeds G))

theorem mem_admissibleSeeds (G : SimpleGraph V) [DecidableRel G.Adj] (b : V) :
    b∈admissibleSeeds G ↔ b∈DeficitCore.core G ∧ ¬SeedConflict G b := by
  simp only [admissibleSeeds,mem_filter]

theorem admissibleSeeds_subset_core (G : SimpleGraph V) [DecidableRel G.Adj] :
    admissibleSeeds G⊆DeficitCore.core G := filter_subset _ _

theorem critical_maximum_image_subset_admissibleSeeds
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀x,0<H.degree x) :
    ((univ : Finset W).filter fun x => H.degree x=H.maxDegree).image f⊆admissibleSeeds G := by
  intro b hb
  have hcore:=DeficitCore.critical_maximum_image_subset_core f hmax hcrit hactive hb
  obtain ⟨x,hx,rfl⟩:=mem_image.mp hb
  exact (mem_admissibleSeeds G (f x)).mpr ⟨hcore,
    not_seedConflict_of_maximum_role f hmax hcrit hactive (mem_filter.mp hx).2⟩

theorem seedCoreDegree_le_combinedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj] :
    seedCoreDegree G≤DeficitCore.combinedCoreDegree G := by
  apply Finset.sup_le
  intro x hx
  exact (neighboursIn_mono G (admissibleSeeds_subset_core G) x).trans
    (DeficitCore.neighboursIn_le_combinedCoreDegree G x (admissibleSeeds_subset_core G hx))

theorem critical_combinedCoreDegree_le_seedCoreDegree
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀x,0<H.degree x) :
    DeficitCore.combinedCoreDegree H≤seedCoreDegree G := by
  have hsub : (DeficitCore.core H).image f⊆admissibleSeeds G := by
    rw [DeficitCore.critical_core_eq H hcrit hactive]
    exact critical_maximum_image_subset_admissibleSeeds f hmax hcrit hactive
  apply Finset.sup_le
  intro x hx
  have hfx : f x∈admissibleSeeds G:=hsub (mem_image.mpr ⟨x,hx,rfl⟩)
  exact (copy_neighboursIn_le f (DeficitCore.core H) x).trans
    ((neighboursIn_mono G hsub (f x)).trans (le_sup (f:=neighboursIn G (admissibleSeeds G)) hfx))

theorem critical_admissibleSeeds_eq_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀x,0<G.degree x) :
    admissibleSeeds G=DeficitCore.core G := by
  apply subset_antisymm (admissibleSeeds_subset_core G)
  intro x hx
  have hd:=((DeficitCore.core_is_admissible G).1 x hx).1
  apply (mem_admissibleSeeds G x).mpr
  exact ⟨hx,not_seedConflict_of_maximum_role (Copy.ofLE G G le_rfl) rfl hcrit hactive hd⟩

theorem critical_seedCoreDegree_eq_combinedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀x,0<G.degree x) :
    seedCoreDegree G=DeficitCore.combinedCoreDegree G := by
  unfold seedCoreDegree
  rw [critical_admissibleSeeds_eq_core G hcrit hactive]
  rfl

theorem edgeColourable_of_admissibleSeeds_eq_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (hempty : admissibleSeeds G=∅) : G.EdgeColorable G.maxDegree := by
  apply edgeColourable_of_tight_reachability_conflicts G
  intro b hb
  by_contra hn
  have hh:=(mem_admissibleSeeds G b).mpr ⟨hb,hn⟩
  rw [hempty] at hh
  simpa using hh

noncomputable def conflictSupport (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun x => 2≤neighboursIn G (admissibleSeeds G) x

theorem conflictSupport_subset_candidateSupport (G : SimpleGraph V) [DecidableRel G.Adj] :
    conflictSupport G⊆DeficitCore.candidateSupport G := by
  intro x hx
  exact (DeficitCore.mem_candidateSupport G x).mpr
    ((mem_filter.mp hx).2.trans (neighboursIn_mono G (admissibleSeeds_subset_core G) x))

theorem critical_vertex_mem_conflictSupport
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀x,0<H.degree x) (x : W) :
    f x∈conflictSupport G := by
  have hsub:=critical_maximum_image_subset_admissibleSeeds f hmax hcrit hactive
  have hn : 2≤neighboursIn H (univ.filter fun z => H.degree z=H.maxDegree) x := by
    rw [SaturatedCore.neighboursIn_maximumVertices]
    exact Gate8J2C.critical_maximumNeighbours_ge_two H hcrit hactive x
  exact mem_filter.mpr ⟨mem_univ _,hn.trans
    ((copy_neighboursIn_le f _ x).trans (neighboursIn_mono G hsub (f x)))⟩

/-- This is equivalence of existence with the original palette. No
extension of a prescribed colouring or new overfull equivalence is assumed. -/
theorem colourable_iff_conflictSupport_induce (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.EdgeColorable G.maxDegree ↔ (G.induce (conflictSupport G : Set V)).EdgeColorable G.maxDegree := by
  apply DeficitCore.colourable_iff_induce_of_critical_capture
  intro w x
  exact critical_vertex_mem_conflictSupport w.embedding w.maxDegree_eq w.critical w.no_isolates x

end OverfullWork.EdgeKernel
