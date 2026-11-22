module

public import OverfullWork.CombinedDeficitCore
public import OverfullWork.SaturatedCoreDegree

@[expose] public section


/-! # Internal maximum degree of the combined deficit kernel -/
namespace OverfullWork.DeficitCore
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Internal maximum degree after both deficit and saturation pruning. -/
noncomputable def combinedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (core G).sup (neighboursIn G (core G))

theorem neighboursIn_le_combinedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (hx : x∈core G) :
    neighboursIn G (core G) x≤combinedCoreDegree G :=
  le_sup (f:=neighboursIn G (core G)) hx

theorem combinedCoreDegree_le_saturatedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj] :
    combinedCoreDegree G≤SaturatedCore.saturatedCoreDegree G := by
  apply Finset.sup_le
  intro x hx
  have hsub := core_subset_saturatedCore G
  exact (neighboursIn_mono G hsub x).trans
    (SaturatedCore.neighboursIn_le_saturatedCoreDegree G x (hsub hx))

theorem combinedCoreDegree_le_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) :
    combinedCoreDegree H≤combinedCoreDegree G := by
  apply Finset.sup_le
  intro x hx
  have hsub := image_core_subset_of_copy f hmax
  have hmem : f x∈core G := hsub (mem_image.mpr ⟨x,hx,rfl⟩)
  exact (copy_neighboursIn_le f (core H) x).trans
    ((neighboursIn_mono G hsub (f x)).trans (neighboursIn_le_combinedCoreDegree G (f x) hmem))


theorem critical_combinedCoreDegree_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ x,0<G.degree x) :
    combinedCoreDegree G=Gate8J2C.maximumCoreDegree G := by
  unfold combinedCoreDegree Gate8J2C.maximumCoreDegree
  rw [critical_core_eq G hcrit hactive]
  congr 1
  funext x
  exact neighboursIn_maximumVertices G x

theorem critical_gap_add_one_le_combinedCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ x,0<G.degree x) :
    G.maxDegree-G.minDegree+1≤combinedCoreDegree G := by
  rw [critical_combinedCoreDegree_eq G hcrit hactive]
  exact Gate8J2C.critical_gap_add_one_le_maximumCoreDegree G hcrit hactive


end OverfullWork.DeficitCore
