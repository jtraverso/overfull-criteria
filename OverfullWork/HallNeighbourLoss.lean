module

public import OverfullWork.PrescribedVertexLoss

@[expose] public section


/-! Minimum-degree bookkeeping for the exact support graph used by Hall. -/
namespace OverfullWork.HallNeighbourLoss
open SimpleGraph Finset PrunedCore RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem neighbours_after_vertex_edge_deletions (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (D U : Finset V) (v : V) (hU : U ⊆ D) :
    neighboursIn G D v ≤ neighboursIn (G\F) U v+(D\U).card+F.degree v := by
  have hSubset : D.filter (fun x => G.Adj v x) ⊆
      (U.filter (fun x => G.Adj v x)) ∪ (D\U) := by
    intro x hx
    obtain ⟨hxD,hAdj⟩ := mem_filter.mp hx
    by_cases hxU : x ∈ U
    · exact mem_union_left _ (mem_filter.mpr ⟨hxU,hAdj⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hxD,hxU⟩)
  have hCount := (card_le_card hSubset).trans (card_union_le _ _)
  have hEdge := neighboursIn_le_sdiff_add_degree G F U v
  simp only [neighboursIn_eq_filter_card] at hEdge ⊢
  omega

theorem opposite_degree_after_deletions (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (A D U : Finset V) (v : V) (d ξ : ℝ)
    (hSide : (v ∈ A ∧ D=Aᶜ) ∨ (v ∉ A ∧ D=A)) (hU : U ⊆ D)
    (hSupport : d ≤ (G.degree v:ℝ))
    (hDis : |(neighboursIn G A v:ℝ)-(neighboursIn G Aᶜ v:ℝ)| < ξ) :
    d-ξ < 2*(neighboursIn (G\F) U v:ℝ)+2*((D\U).card:ℝ)+2*(F.degree v:ℝ) := by
  have hSplit := LowSetEdgePreprocessing.neighboursIn_add_compl G A v
  have hSplitR : (neighboursIn G A v:ℝ)+(neighboursIn G Aᶜ v:ℝ)=G.degree v := by exact_mod_cast hSplit
  have hCount : (neighboursIn G D v:ℝ) ≤ (neighboursIn (G\F) U v:ℝ)+((D\U).card:ℝ)+(F.degree v:ℝ) := by
    exact_mod_cast neighbours_after_vertex_edge_deletions G F D U v hU
  rcases hSide with ⟨_,rfl⟩|⟨_,rfl⟩
  · have hh := (abs_lt.mp hDis).2
    linarith
  · have hh := (abs_lt.mp hDis).1
    linarith

end OverfullWork.HallNeighbourLoss
