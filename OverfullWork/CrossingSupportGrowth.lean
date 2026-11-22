module

public import OverfullWork.SecondAnchorCrossingBudget

@[expose] public section


/-! # Pay crossing-support drift by actual added incident copies

A new simple crossing neighbor requires a copy in the actual graph
difference. Thus monotone additions can grow the simple crossing degree
by at most the total incident-degree gain, independently of multiplicity.
-/
namespace SimpleGraph.MultiGraph
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem support_degree_le_degree (M : MultiGraph V) (v : V) : M.supportGraph.degree v ≤ M.degree v := by
  rw [←degree_ofSimpleGraph,degree_eq_sum_mult,degree_eq_sum_mult]
  apply sum_le_sum
  intro w _
  change (if s(v,w) ∈ M.supportGraph.edgeSet then 1 else 0) ≤ M.mult s(v,w)
  simp only [SimpleGraph.mem_edgeSet]
  split_ifs with hEdge
  · change 0 < M.mult s(v,w) at hEdge
    omega
  · exact Nat.zero_le _

theorem crossing_support_growth (M N : MultiGraph V) (A : Finset V) (v : V)
    (hMono : ∀ e, M.mult e ≤ N.mult e) :
    (N.crossingSupport A).degree v+M.degree v ≤ (M.crossingSupport A).degree v+N.degree v := by
  have hSub : (N.crossingSupport A).neighborFinset v ⊆
      (M.crossingSupport A).neighborFinset v ∪ (N.subtractCopies M).supportGraph.neighborFinset v := by
    intro w hw
    have hAdj := (mem_neighborFinset _ v w).mp hw
    by_cases hOld : 0 < M.mult s(v,w)
    · exact mem_union_left _ ((mem_neighborFinset _ v w).mpr ⟨hOld,hAdj.2⟩)
    · have hDiff : (N.subtractCopies M).supportGraph.Adj v w := by
        change 0 < N.mult s(v,w)-M.mult s(v,w)
        have hh := hAdj.1
        omega
      exact mem_union_right _ ((mem_neighborFinset _ v w).mpr hDiff)
  have hCount := (card_le_card hSub).trans (card_union_le _ _)
  simp only [card_neighborFinset_eq_degree] at hCount
  have hDegree := degree_subtract_add N M hMono v
  have hSupport := (N.subtractCopies M).support_degree_le_degree v
  omega

namespace PartialColouring
variable {H : MultiGraph V} {k l : ℕ}

theorem crossing_degree_after_fresh_palette (P : H.PartialColouring k) (Q : H.PartialColouring (k+l))
    (A : Finset V) (v : V) (hMono : ∀ e, P.graph.mult e ≤ Q.graph.mult e)
    (hFilled : P.graph.degree v=k) :
    (Q.graph.crossingSupport A).degree v ≤ (P.graph.crossingSupport A).degree v+l := by
  have hh := crossing_support_growth P.graph Q.graph A v hMono
  have hBound := Q.colouring.degree_le_palette v
  omega

end PartialColouring
end SimpleGraph.MultiGraph
