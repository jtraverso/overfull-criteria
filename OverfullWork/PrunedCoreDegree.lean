module

public import OverfullWork.MaximumTwoCore

@[expose] public section


/-! # Local degree of the pruned maximum-degree core

The parameter is measured on the greatest minimum-two subset of the
maximum-degree vertices. It is monotone for copies preserving maximum
 degree and agrees with the ordinary core parameter on critical graphs.
-/
namespace OverfullWork.PrunedCore
open SimpleGraph Finset Gate8J2C
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Maximum internal degree of the constructed maximum-degree two-core. -/
noncomputable def prunedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (maximumTwoCore G).sup (neighboursIn G (maximumTwoCore G))

theorem neighboursIn_le_prunedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (hx : x∈maximumTwoCore G) :
    neighboursIn G (maximumTwoCore G) x≤prunedCoreDegree G :=
  le_sup (f:=neighboursIn G (maximumTwoCore G)) hx

theorem neighboursIn_maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    neighboursIn G (univ.filter fun v => G.degree v=G.maxDegree) x=maximumNeighbours G x := by
  simp only [neighboursIn,maximumNeighbours,mem_filter,mem_univ,true_and]

theorem prunedCoreDegree_le_maximumCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj] :
    prunedCoreDegree G≤maximumCoreDegree G := by
  apply Finset.sup_le
  intro x hx
  have hd:=(maximumTwoCore_isCoreSet G x hx).1
  have hn:=neighboursIn_mono G (maximumTwoCore_subset_maximumVertices G) x
  rw [neighboursIn_maximumVertices] at hn
  exact hn.trans (maximumNeighbours_le_coreDegree G x hd)

/-- Common-maximum-degree copies can enlarge the kernel, but cannot
 decrease its maximum internal degree. -/
theorem prunedCoreDegree_le_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) :
    prunedCoreDegree H≤prunedCoreDegree G := by
  apply Finset.sup_le
  intro x hx
  have hsub:=image_maximumTwoCore_subset_of_copy f hmax
  have hmem : f x∈maximumTwoCore G:=hsub (mem_image.mpr ⟨x,hx,rfl⟩)
  exact (copy_neighboursIn_le f (maximumTwoCore H) x).trans
    ((neighboursIn_mono G hsub (f x)).trans (neighboursIn_le_prunedCoreDegree G (f x) hmem))

/-- VAL makes the full maximum-degree vertex set admissible in an
 active critical graph. Thus pruning deletes no maximum-degree vertex. -/
theorem critical_maximumTwoCore_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) :
    maximumTwoCore G=univ.filter fun v => G.degree v=G.maxDegree := by
  apply subset_antisymm (maximumTwoCore_subset_maximumVertices G)
  apply coreSet_subset_maximumTwoCore
  intro x hx
  refine ⟨(mem_filter.mp hx).2,?_⟩
  rw [neighboursIn_maximumVertices]
  exact critical_maximumNeighbours_ge_two G hcrit hactive x

theorem critical_prunedCoreDegree_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) :
    prunedCoreDegree G=maximumCoreDegree G := by
  unfold prunedCoreDegree maximumCoreDegree
  rw [critical_maximumTwoCore_eq G hcrit hactive]
  congr 1
  funext x
  exact neighboursIn_maximumVertices G x

theorem critical_gap_add_one_le_prunedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) :
    G.maxDegree-G.minDegree+1≤prunedCoreDegree G := by
  rw [critical_prunedCoreDegree_eq G hcrit hactive]
  exact critical_gap_add_one_le_maximumCoreDegree G hcrit hactive

/-- Every maximum-degree vertex of an active critical copy lies in the
 actual pruned kernel of the host graph. -/
theorem copy_critical_maximumVertices_subset {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀ v,0<H.degree v) :
    (univ.filter fun v => H.degree v=H.maxDegree).image f⊆maximumTwoCore G := by
  rw [←critical_maximumTwoCore_eq H hcrit hactive]
  exact image_maximumTwoCore_subset_of_copy f hmax

end OverfullWork.PrunedCore
