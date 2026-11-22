module

public import OverfullWork.OsthusStadenTrimmedCopies
public import OverfullWork.RealRobustSpanningLinkage
public import OverfullWork.BipartiteRobustMargin

@[expose] public section


/-! Use two embeddings of the same carrier to realize a balanced
crossing graph. The two coordinate systems may enumerate their
clusters independently. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph PrunedCore DirectedClusterQuotient
open scoped Classical

variable {V X I : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Fintype I]

/-- A pulled fibre has precisely the vertices in the corresponding
intersection with the image of its coordinate embedding. -/
theorem map_cluster_of_embedding (a : X ↪ V) (f : V → Option I) (i : I) :
    (cluster (f ∘ a) i).map a = (univ : Finset X).map a ∩ cluster f i := by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
    exact mem_inter.mpr ⟨mem_map.mpr ⟨x,mem_univ _,rfl⟩,
      (mem_cluster f i _).mpr ((mem_cluster (f ∘ a) i x).mp hx)⟩
  · intro hv
    obtain ⟨x,_,rfl⟩ := mem_map.mp (mem_inter.mp hv).1
    exact mem_map.mpr ⟨x,(mem_cluster (f ∘ a) i x).mpr
      ((mem_cluster f i _).mp (mem_inter.mp hv).2),rfl⟩

theorem exceptional_pull_le (a : X ↪ V) (f : V → Option I) :
    (exceptional (f ∘ a)).card ≤ (exceptional f).card := by
  rw [←card_map a]
  apply card_le_card
  intro v hv
  obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
  exact (mem_exceptional f _).mpr ((mem_exceptional (f ∘ a) x).mp hx)

theorem symmetric_density (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    DirectedRegularPairs.density (RobustSpanningLinkage.symmetric G) A B =
      (G.edgeDensity A B:ℝ) := by
  have hN (v : V) :
      DirectedRobustExpansion.inNeighbours (RobustSpanningLinkage.symmetric G) A v =
        neighboursIn G A v := by
    rw [RobustExpansion.neighboursIn_eq_filter_card]
    apply congrArg Finset.card
    ext x
    rw [mem_filter,mem_filter]
    change (x ∈ A ∧ G.Adj x v) ↔ (x ∈ A ∧ G.Adj v x)
    exact and_congr_right (fun _ => G.adj_comm x v)
  have hSum : DirectedRobustExpansion.incidences (RobustSpanningLinkage.symmetric G) A B =
      (G.interedges A B).card := by
    rw [RegularPairNeighbourhood.interedges_eq_sum_neighbours]
    exact sum_congr rfl (fun x _ => hN x)
  simp only [DirectedRegularPairs.density,hSum,SimpleGraph.edgeDensity,Rel.edgeDensity,
    SimpleGraph.interedges, Rat.cast_div,Rat.cast_natCast,Rat.cast_mul]

theorem uniform_pull_symmetric (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : X ↪ V) (A B : Finset X) (ε : ℝ)
    (h : G.IsUniform ε (A.map a) (B.map b)) :
    DirectedRegularPairs.IsUniform
      (DirectedRegularPairs.pullDirectedPair a b (RobustSpanningLinkage.symmetric G)) ε A B := by
  intro S hS T hT hSz hTz
  rw [DirectedRegularPairs.density_pullDirectedPair,DirectedRegularPairs.density_pullDirectedPair,
    symmetric_density,symmetric_density]
  exact h (map_subset_map.mpr hS) (map_subset_map.mpr hT)
    (by simpa only [card_map] using hSz) (by simpa only [card_map] using hTz)

/-- Robust out-expansion in paired coordinates gives actual bipartite
expansion between the respective embedded vertex sets. -/
theorem expandsTo_of_pulled_robust (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : X ↪ V) {A B : Finset V}
    (hA : (univ : Finset X).map a = A) (hB : (univ : Finset X).map b = B)
    (r t : ℕ)
    (hR : DirectedRobustExpansion.IsRobustAt
      (DirectedRegularPairs.pullDirectedPair a b (RobustSpanningLinkage.symmetric G)) r t) :
    BipartiteRobustMargin.ExpandsTo G A B r t := by
  intro S hS hlo hhi
  let D := DirectedRegularPairs.pullDirectedPair a b (RobustSpanningLinkage.symmetric G)
  let T := (univ : Finset X).filter (fun x => a x ∈ S)
  have hT : T.map a = S := by
    ext v
    constructor
    · intro hv
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
      exact (mem_filter.mp hx).2
    · intro hv
      have hvA : v ∈ (univ : Finset X).map a := hA ▸ hS hv
      obtain ⟨x,_,rfl⟩ := mem_map.mp hvA
      exact mem_map.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,hv⟩,rfl⟩
  have hTc : T.card = S.card := (card_map a).symm.trans (congrArg card hT)
  have hAc : A.card = Fintype.card X := by rw [←hA,card_map,card_univ]
  have hCount (x : X) :
      DirectedRobustExpansion.inNeighbours D T x = neighboursIn G S (b x) := by
    rw [RobustExpansion.neighboursIn_eq_filter_card,←hT]
    have hMap :
        (T.filter (fun y => D.Adj y x)).map a = (T.map a).filter (G.Adj (b x)) := by
      ext v
      constructor
      · intro hv
        obtain ⟨y,hy,rfl⟩ := mem_map.mp hv
        have hEq : G.Adj (a y) (b x) := (mem_filter.mp hy).2
        exact mem_filter.mpr ⟨mem_map.mpr ⟨y,(mem_filter.mp hy).1,rfl⟩,hEq.symm⟩
      · intro hv
        obtain ⟨y,hy,rfl⟩ := mem_map.mp (mem_filter.mp hv).1
        have he : G.Adj (a y) (b x) := (mem_filter.mp hv).2.symm
        exact mem_map.mpr ⟨y,mem_filter.mpr ⟨hy,he⟩,rfl⟩
    change (T.filter fun y => D.Adj y x).card = _
    rw [←hMap,card_map]
  let U := DirectedRobustExpansion.neighbourhood D r T
  have hGrow : T.card+r ≤ U.card := hR T (by rwa [hTc]) (by rwa [hTc,←hAc])
  have hMap : U.map b ⊆ BipartiteRobustMargin.neighbours G B r S := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
    have hxB : b x ∈ B := hB ▸ mem_map.mpr ⟨x,mem_univ _,rfl⟩
    refine mem_filter.mpr ⟨hxB,?_⟩
    rw [←hCount]
    exact (mem_filter.mp hx).2
  have hCard := card_le_card hMap
  rw [card_map] at hCard
  exact (hTc ▸ hGrow).trans hCard

end OverfullWork.CMSBalancedCut
