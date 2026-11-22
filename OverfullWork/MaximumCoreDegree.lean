module

public import OverfullWork.DegreeStrata

@[expose] public section


/-! # Internal maximum degree of the maximum-degree core

This measures local core density rather than its number of vertices.
-/
namespace OverfullWork.Gate8J2C
open SimpleGraph Finset
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Maximum number of maximum-degree neighbours, over maximum-degree
vertices only. It is zero for an empty maximum-degree core. -/
def maximumCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (univ.filter fun x => G.degree x=G.maxDegree).sup (maximumNeighbours G)

theorem maximumNeighbours_le_coreDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (hx : G.degree x=G.maxDegree) :
    maximumNeighbours G x≤maximumCoreDegree G := by
  exact le_sup (f:=maximumNeighbours G) (mem_filter.mpr ⟨mem_univ x,hx⟩)

theorem maximumCoreDegree_le_count (G : SimpleGraph V) [DecidableRel G.Adj] :
    maximumCoreDegree G≤Gate8J.maximumDegreeCount G := by
  apply Finset.sup_le
  intro x _
  apply card_le_card
  intro z hz
  obtain ⟨_,hd⟩:=mem_filter.mp hz
  exact mem_filter.mpr ⟨mem_univ z,hd⟩

/-- VAL at a minimum/maximum edge controls the critical gap by local
core density, independently of the number of maximum-degree vertices. -/
theorem critical_gap_add_one_le_maximumCoreDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) :
    G.maxDegree-G.minDegree+1≤maximumCoreDegree G := by
  obtain ⟨a,b,ha,hab,hb⟩:=Gate8J.exists_minimum_maximum_edge G hcrit hactive
  have h:=deficit_le_maximumNeighbours G hcrit hab.symm
  rw [ha] at h
  exact h.trans (maximumNeighbours_le_coreDegree G b hb)

/-- Common-maximum-degree copies preserve local maximum-core density
monotonically, not merely the cardinality of the maximum-degree core. -/
theorem maximumCoreDegree_le_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) :
    maximumCoreDegree H≤maximumCoreDegree G := by
  classical
  apply Finset.sup_le
  intro x hx
  have hxD:=(mem_filter.mp hx).2
  have hxG : G.degree (f x)=G.maxDegree := by
    have hl:=f.degree_le x
    have hu:=G.degree_le_maxDegree (f x)
    omega
  have hlocal : maximumNeighbours H x≤maximumNeighbours G (f x) := by
    let S:=(H.neighborFinset x).filter fun z => H.degree z=H.maxDegree
    let T:=(G.neighborFinset (f x)).filter fun z => G.degree z=G.maxDegree
    have hsub : S.image f⊆T := by
      intro z hz
      obtain ⟨w,hw,rfl⟩:=mem_image.mp hz
      obtain ⟨hwN,hwD⟩:=mem_filter.mp hw
      apply mem_filter.mpr
      refine ⟨(mem_neighborFinset G (f x) (f w)).mpr (f.toHom.map_adj ((mem_neighborFinset H x w).mp hwN)),?_⟩
      have hl:=f.degree_le w
      have hu:=G.degree_le_maxDegree (f w)
      omega
    have hc:=card_le_card hsub
    have hinj : Function.Injective (fun w : W => f w):=fun _ _ h => f.injective h
    rw [card_image_of_injective S hinj] at hc
    exact hc
  exact hlocal.trans (maximumNeighbours_le_coreDegree G (f x) hxG)

/-- VAL forces two maximum-degree neighbours at every active vertex of
an edge-critical graph. In particular the maximum-degree core has no leaf. -/
theorem critical_maximumNeighbours_ge_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) (x : V) :
    2≤maximumNeighbours G x := by
  obtain ⟨y,hxy⟩:=(G.degree_pos_iff_exists_adj x).mp (hactive x)
  by_cases hy : G.degree y=G.maxDegree
  · obtain ⟨z,hxz,hzy,hz⟩:=Overfull.exists_maxdeg_nbr hcrit hxy
    have hsub : ({y,z} : Finset V)⊆(G.neighborFinset x).filter fun w => G.degree w=G.maxDegree := by
      intro w hw
      rcases mem_insert.mp hw with he|hw
      · subst w
        exact mem_filter.mpr ⟨(mem_neighborFinset G x y).mpr hxy,hy⟩
      · have hwz : w=z:=mem_singleton.mp hw
        subst w
        exact mem_filter.mpr ⟨(mem_neighborFinset G x z).mpr hxz,hz⟩
    have hc:=card_le_card hsub
    simpa only [card_pair (Ne.symm hzy),maximumNeighbours] using hc
  · have hd:=G.degree_le_maxDegree y
    have hv:=deficit_le_maximumNeighbours G hcrit hxy
    omega

end OverfullWork.Gate8J2C
