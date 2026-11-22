module

public import OverfullWork.MaximumCoreDegree

@[expose] public section


/-! # The greatest minimum-two subset of the maximum-degree vertices

The kernel is defined by a union of all admissible finite sets, rather
than assuming that a pruning algorithm has already terminated.
-/
namespace OverfullWork.PrunedCore
open SimpleGraph Finset
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

def neighboursIn (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (x : V) : ℕ :=
  ((G.neighborFinset x).filter fun y => y∈T).card

def IsCoreSet (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : Prop :=
  ∀ v∈T,G.degree v=G.maxDegree ∧ 2≤neighboursIn G T v

noncomputable def maximumTwoCore (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ T : Finset V,IsCoreSet G T ∧ v∈T

theorem mem_maximumTwoCore (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    v∈maximumTwoCore G ↔ ∃ T : Finset V,IsCoreSet G T ∧ v∈T := by
  simp only [maximumTwoCore,mem_filter,mem_univ,true_and]

theorem neighboursIn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hST : S⊆T) (x : V) : neighboursIn G S x≤neighboursIn G T x := by
  apply card_le_card
  intro y hy
  obtain ⟨hyN,hyS⟩:=mem_filter.mp hy
  exact mem_filter.mpr ⟨hyN,hST hyS⟩

theorem coreSet_subset_maximumTwoCore (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (hT : IsCoreSet G T) : T⊆maximumTwoCore G := by
  intro v hv
  exact (mem_maximumTwoCore G v).mpr ⟨T,hT,hv⟩

theorem maximumTwoCore_isCoreSet (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsCoreSet G (maximumTwoCore G) := by
  intro v hv
  obtain ⟨T,hT,hvT⟩:=(mem_maximumTwoCore G v).mp hv
  obtain ⟨hd,hn⟩:=hT v hvT
  exact ⟨hd,hn.trans (neighboursIn_mono G (coreSet_subset_maximumTwoCore G T hT) v)⟩

theorem maximumTwoCore_subset_maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] :
    maximumTwoCore G⊆univ.filter fun v => G.degree v=G.maxDegree := by
  intro v hv
  exact mem_filter.mpr ⟨mem_univ v,(maximumTwoCore_isCoreSet G v hv).1⟩

theorem isCoreSet_union (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hS : IsCoreSet G S) (hT : IsCoreSet G T) : IsCoreSet G (S∪T) := by
  intro v hv
  rcases mem_union.mp hv with hvS|hvT
  · exact ⟨(hS v hvS).1,(hS v hvS).2.trans (neighboursIn_mono G subset_union_left v)⟩
  · exact ⟨(hT v hvT).1,(hT v hvT).2.trans (neighboursIn_mono G subset_union_right v)⟩

/-- An injective graph copy maps neighbours inside T injectively to
neighbours inside its image. -/
theorem copy_neighboursIn_le {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (T : Finset W) (x : W) :
    neighboursIn H T x≤neighboursIn G (T.image f) (f x) := by
  classical
  let S:=(H.neighborFinset x).filter fun y => y∈T
  let U:=(G.neighborFinset (f x)).filter fun y => y∈T.image f
  have hsub : S.image f⊆U := by
    intro y hy
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hy
    obtain ⟨hzN,hzT⟩:=mem_filter.mp hz
    exact mem_filter.mpr ⟨(mem_neighborFinset G (f x) (f z)).mpr
      (f.toHom.map_adj ((mem_neighborFinset H x z).mp hzN)),mem_image.mpr ⟨z,hzT,rfl⟩⟩
  have hc:=card_le_card hsub
  have hinj : Function.Injective (fun z : W => f z):=fun _ _ h => f.injective h
  rw [card_image_of_injective S hinj] at hc
  exact hc

/-- Same-maximum-degree copies transport admissible core sets. -/
theorem coreSet_image_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) {T : Finset W}
    (hT : IsCoreSet H T) : IsCoreSet G (T.image f) := by
  intro y hy
  obtain ⟨x,hx,rfl⟩:=mem_image.mp hy
  obtain ⟨hxD,hxN⟩:=hT x hx
  refine ⟨?_,hxN.trans (copy_neighboursIn_le f T x)⟩
  have hl:=f.degree_le x
  have hu:=G.degree_le_maxDegree (f x)
  omega

/-- The kernel is functorial for copies that preserve the original
maximum degree. The core need not have the same order after extraction. -/
theorem image_maximumTwoCore_subset_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) :
    (maximumTwoCore H).image f⊆maximumTwoCore G :=
  coreSet_subset_maximumTwoCore G _ (coreSet_image_of_copy f hmax (maximumTwoCore_isCoreSet H))

end OverfullWork.PrunedCore
