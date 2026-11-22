module

public import OverfullWork.SaturatedCoreKernel
public import OverfullWork.CoreDeficitPruning

@[expose] public section


/-! # Greatest kernel combining neighbour saturation and local deficits

Both pruning conditions are monotone and preserve the image of the
maximum-degree vertices of any critical copy with the same Delta.
-/
namespace OverfullWork.DeficitCore
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def step (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : Finset V :=
  SaturatedCore.saturatedStep G (deficitFilter G T)

def IsDeficitCoreSet (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : Prop :=
  SaturatedCore.IsSaturatedCoreSet G T ∧ deficitFilter G T=T

noncomputable def core (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun x => ∃ T : Finset V,IsDeficitCoreSet G T ∧ x∈T

theorem mem_core (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    x∈core G ↔ ∃ T : Finset V,IsDeficitCoreSet G T ∧ x∈T := by
  simp only [core,mem_filter,mem_univ,true_and]

theorem step_subset (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : step G T⊆T :=
  (SaturatedCore.saturatedStep_subset G _).trans (deficitFilter_subset G T)

theorem step_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hST : S⊆T) : step G S⊆step G T :=
  SaturatedCore.saturatedStep_mono G (deficitFilter_mono G hST)

theorem admissible_subset_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : IsDeficitCoreSet G T) : T⊆core G := by
  intro x hx
  exact (mem_core G x).mpr ⟨T,hT,hx⟩

theorem core_is_admissible (G : SimpleGraph V) [DecidableRel G.Adj] : IsDeficitCoreSet G (core G) := by
  refine ⟨?_,subset_antisymm (deficitFilter_subset G _) ?_⟩
  · intro x hx
    obtain ⟨T,hT,hxT⟩:=(mem_core G x).mp hx
    obtain ⟨hd,hxN,hn⟩:=hT.1 x hxT
    have hsub:=admissible_subset_core G T hT
    exact ⟨hd,hxN.trans (neighboursIn_mono G hsub x),
      fun y hy => (hn y hy).trans (neighboursIn_mono G hsub y)⟩
  · intro x hx
    obtain ⟨T,hT,hxT⟩:=(mem_core G x).mp hx
    have hxF : x∈deficitFilter G T:=by rw [hT.2];exact hxT
    exact deficitFilter_mono G (admissible_subset_core G T hT) hxF

theorem core_subset_saturatedCore (G : SimpleGraph V) [DecidableRel G.Adj] :
    core G⊆SaturatedCore.saturatedCore G :=
  SaturatedCore.saturatedSet_subset_core G _ (core_is_admissible G).1

theorem core_subset_maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] :
    core G⊆univ.filter fun x => G.degree x=G.maxDegree :=
  (core_subset_saturatedCore G).trans (SaturatedCore.saturatedCore_subset_maximumVertices G)

theorem admissible_fixedpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : IsDeficitCoreSet G T) : step G T=T := by
  unfold step
  rw [hT.2]
  apply subset_antisymm (SaturatedCore.saturatedStep_subset G _)
  intro x hx
  exact mem_filter.mpr ⟨hx,(hT.1 x hx).2⟩

theorem core_fixedpoint (G : SimpleGraph V) [DecidableRel G.Adj] : step G (core G)=core G :=
  admissible_fixedpoint G _ (core_is_admissible G)

theorem fixedpoint_subset_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hmax : ∀ x∈T,G.degree x=G.maxDegree) (hfix : step G T=T) : T⊆core G := by
  have hsub : T⊆deficitFilter G T := by
    have hs : step G T⊆deficitFilter G T:=SaturatedCore.saturatedStep_subset G _
    rw [hfix] at hs
    exact hs
  have hdef : deficitFilter G T=T:=subset_antisymm (deficitFilter_subset G T) hsub
  have hsat : SaturatedCore.saturatedStep G T=T := by simpa only [step,hdef] using hfix
  apply admissible_subset_core G T
  refine ⟨?_,hdef⟩
  intro x hx
  have hxS : x∈SaturatedCore.saturatedStep G T:=by rw [hsat];exact hx
  exact ⟨hmax x hx,(mem_filter.mp hxS).2⟩

theorem core_survives_step (G : SimpleGraph V) [DecidableRel G.Adj]
    {T : Finset V} (hT : core G⊆T) : core G⊆step G T := by
  rw [←core_fixedpoint G]
  exact step_mono G hT

/-- Every ambient neighbour lifts at maximum-degree image vertices.
Its ambient deficit is no larger than the source deficit. -/
theorem admissible_image_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) {T : Finset W}
    (hT : IsDeficitCoreSet H T) : IsDeficitCoreSet G (T.image f) := by
  refine ⟨SaturatedCore.saturatedSet_image_of_copy f hmax hT.1,?_⟩
  apply subset_antisymm (deficitFilter_subset G _)
  intro y hy
  obtain ⟨x,hx,rfl⟩:=mem_image.mp hy
  refine mem_filter.mpr ⟨mem_image.mpr ⟨x,hx,rfl⟩,?_⟩
  intro a hxa
  have hxD:=(hT.1 x hx).1
  obtain ⟨z,hxz,rfl⟩:=f.exists_adj_preimage_of_maximum_degree hmax x hxD hxa
  have hxF : x∈deficitFilter H T:=by rw [hT.2];exact hx
  have hzBound:=(mem_filter.mp hxF).2 z hxz
  have hdeg:=f.degree_le z
  have hdef : G.maxDegree-G.degree (f z)+1≤H.maxDegree-H.degree z+1:=by omega
  exact hdef.trans (hzBound.trans (copy_neighboursIn_le f T x))

theorem image_core_subset_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) : (core H).image f⊆core G :=
  admissible_subset_core G _ (admissible_image_of_copy f hmax (core_is_admissible H))

theorem critical_maximumVertices_is_admissible (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ x,0<G.degree x) :
    IsDeficitCoreSet G (univ.filter fun x => G.degree x=G.maxDegree) := by
  refine ⟨SaturatedCore.critical_maximumVertices_isSaturated G hcrit hactive,?_⟩
  apply subset_antisymm (deficitFilter_subset G _)
  intro x hx
  refine mem_filter.mpr ⟨hx,?_⟩
  intro a hxa
  rw [SaturatedCore.neighboursIn_maximumVertices]
  exact Gate8J2C.deficit_le_maximumNeighbours G hcrit hxa

theorem critical_core_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ x,0<G.degree x) :
    core G=univ.filter fun x => G.degree x=G.maxDegree := by
  apply subset_antisymm (core_subset_maximumVertices G)
  exact admissible_subset_core G _ (critical_maximumVertices_is_admissible G hcrit hactive)

theorem critical_maximum_image_subset_core {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀ x,0<H.degree x) :
    (univ.filter fun x => H.degree x=H.maxDegree).image f⊆core G :=
  admissible_subset_core G _ (admissible_image_of_copy f hmax
    (critical_maximumVertices_is_admissible H hcrit hactive))

theorem critical_maximum_image_survives_step {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀ x,0<H.degree x)
    (T : Finset V) (hT : (univ.filter fun x => H.degree x=H.maxDegree).image f⊆T) :
    (univ.filter fun x => H.degree x=H.maxDegree).image f⊆step G T :=
  SaturatedCore.critical_maximum_image_survives_step f hmax hcrit hactive _
    (PrunedCore.critical_maximum_image_subset_deficitFilter f hmax hcrit T hT)

end OverfullWork.DeficitCore
