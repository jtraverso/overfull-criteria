module

public import OverfullWork.SaturatedCoreKernel
public import OverfullWork.PrunedCoreDegree

@[expose] public section


/-! # Internal maximum degree of the saturation-pruned kernel -/
namespace OverfullWork.SaturatedCore
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Internal maximum degree of the kernel with neighbour saturation. -/
noncomputable def saturatedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (saturatedCore G).sup (neighboursIn G (saturatedCore G))

theorem neighboursIn_le_saturatedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (hx : x∈saturatedCore G) :
    neighboursIn G (saturatedCore G) x≤saturatedCoreDegree G :=
  le_sup (f:=neighboursIn G (saturatedCore G)) hx

theorem saturatedCoreDegree_le_prunedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj] :
    saturatedCoreDegree G≤PrunedCore.prunedCoreDegree G := by
  apply Finset.sup_le
  intro x hx
  have hsub := saturatedCore_subset_maximumTwoCore G
  exact (neighboursIn_mono G hsub x).trans
    (PrunedCore.neighboursIn_le_prunedCoreDegree G x (hsub hx))

theorem saturatedCoreDegree_le_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) :
    saturatedCoreDegree H≤saturatedCoreDegree G := by
  apply Finset.sup_le
  intro x hx
  have hsub := image_saturatedCore_subset_of_copy f hmax
  have hmem : f x∈saturatedCore G := hsub (mem_image.mpr ⟨x,hx,rfl⟩)
  exact (copy_neighboursIn_le f (saturatedCore H) x).trans
    ((neighboursIn_mono G hsub (f x)).trans (neighboursIn_le_saturatedCoreDegree G (f x) hmem))

theorem critical_saturatedCore_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ x,0<G.degree x) :
    saturatedCore G=univ.filter fun x => G.degree x=G.maxDegree := by
  apply subset_antisymm (saturatedCore_subset_maximumVertices G)
  exact saturatedSet_subset_core G _ (critical_maximumVertices_isSaturated G hcrit hactive)

theorem critical_saturatedCoreDegree_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ x,0<G.degree x) :
    saturatedCoreDegree G=Gate8J2C.maximumCoreDegree G := by
  unfold saturatedCoreDegree Gate8J2C.maximumCoreDegree
  rw [critical_saturatedCore_eq G hcrit hactive]
  congr 1
  funext x
  exact neighboursIn_maximumVertices G x

theorem critical_gap_add_one_le_saturatedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ x,0<G.degree x) :
    G.maxDegree-G.minDegree+1≤saturatedCoreDegree G := by
  rw [critical_saturatedCoreDegree_eq G hcrit hactive]
  exact Gate8J2C.critical_gap_add_one_le_maximumCoreDegree G hcrit hactive


end OverfullWork.SaturatedCore
