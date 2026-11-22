module

public import OverfullWork.UniformCriticalReduction

@[expose] public section


/-! # Bounded maximum-degree cores without any original degree-gap bound

VAL forces a critical graph to have at least Delta-delta+2 vertices of
maximum degree. Their number cannot increase under critical extraction.
-/
namespace OverfullWork.Gate8J
open SimpleGraph Finset
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The number of vertices attaining the actual maximum degree. -/
def maximumDegreeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (univ.filter fun z => G.degree z=G.maxDegree).card

theorem critical_gap_add_two_le_maximumDegreeCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) :
    G.maxDegree-G.minDegree+2≤maximumDegreeCount G := by
  obtain ⟨a,b,ha,hab,hb⟩:=exists_minimum_maximum_edge G hcrit hactive
  have hcount:=minimum_edge_maximum_neighbours G hcrit ha hab
  let S:=univ.filter fun z => G.degree z=G.maxDegree
  let T:=(G.neighborFinset b).filter fun z => z≠a ∧ G.degree z=G.maxDegree
  have hsub : T⊆S.erase b := by
    intro z hz
    obtain ⟨hzN,_,hzD⟩:=mem_filter.mp hz
    have hzb : z≠b := by
      intro he
      subst z
      exact ((mem_neighborFinset G b b).mp hzN).ne rfl
    exact mem_erase.mpr ⟨hzb,mem_filter.mpr ⟨mem_univ z,hzD⟩⟩
  have hbS : b∈S:=mem_filter.mpr ⟨mem_univ b,hb⟩
  have hcard:=card_le_card hsub
  have herase:=card_erase_add_one hbS
  change G.maxDegree-G.minDegree+1≤T.card at hcount
  change G.maxDegree-G.minDegree+2≤S.card
  omega

/-- Common-maximum-degree copies cannot gain maximum-degree vertices. -/
theorem maximumDegreeCount_le_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree) :
    maximumDegreeCount H≤maximumDegreeCount G := by
  classical
  let S:=univ.filter fun z => H.degree z=H.maxDegree
  let T:=univ.filter fun z => G.degree z=G.maxDegree
  have hsub : S.image f⊆T := by
    intro z hz
    obtain ⟨w,hw,rfl⟩:=mem_image.mp hz
    have hd:=(mem_filter.mp hw).2
    have hle:=f.degree_le w
    have hup:=G.degree_le_maxDegree (f w)
    apply mem_filter.mpr
    exact ⟨mem_univ _,by omega⟩
  have hcount:=card_le_card hsub
  have hinj : Function.Injective (fun w : W => f w):=fun _ _ h => f.injective h
  rw [card_image_of_injective S hinj] at hcount
  exact hcount

/-- CCJS's low-degree interval gives no information in this regime. -/
theorem degree_dichotomy_empty_of_high_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hhigh : G.maxDegree<2*G.minDegree) (v : V) :
    G.maxDegree<G.degree v+G.minDegree := by
  have h:=G.minDegree_le_degree v
  omega

/-- No restriction on Delta-delta of the original graph: a fixed bound
on the number of maximum-degree vertices is enough above one half. -/
theorem eventually_above_half_bounded_maximum_core (B : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      N≤Fintype.card W → maximumDegreeCount G≤B →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℕ)≤(G.maxDegree:ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  obtain ⟨N,hN⟩:=eventually_exists_large_gap_critical_core_of_order.{u} B ε hε
  refine ⟨2*N,?_⟩
  intro W _ _ G _ hsize hcore hdense
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hno => ?_⟩
  by_contra hnc
  obtain ⟨w,_,_,hgap⟩:=hN G hsize hnc hno hdense
  have hlow:=critical_gap_add_two_le_maximumDegreeCount w.graph w.critical w.no_isolates
  have hup:=maximumDegreeCount_le_of_copy w.embedding w.maxDegree_eq
  omega

end OverfullWork.Gate8J
