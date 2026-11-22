module

public import OverfullWork.RouteResidueAccounting

@[expose] public section


/-! # Compensated crossing/residue incidence identity

Colored crossing copies increase by the added matching degree. The
drop in the missing palette compensates exactly for the endpoint
increments. This yields the identity used to telescope local budgets.
-/
namespace SimpleGraph.MultiGraph
open SimpleGraph Finset OverfullWork.PairedRoutes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 20000000

def crossDegree (M : MultiGraph V) (A : Finset V) (v : V) : ℕ :=
  ∑ w : V, if ¬(v ∈ A ↔ w ∈ A) then M.mult s(v,w) else 0

theorem internal_degree_add_crossDegree (M : MultiGraph V) (A : Finset V) (v : V) :
    (M.internalPart A).degree v+M.crossDegree A v=M.degree v := by
  simp only [degree_eq_sum_mult,crossDegree,←sum_add_distrib,internalPart_mult]
  apply sum_congr rfl
  intro w _
  by_cases hw : v ∈ A ↔ w ∈ A <;> simp [hw]

theorem crossingSupport_degree_le_crossDegree (M : MultiGraph V) (A : Finset V) (v : V) :
    (M.crossingSupport A).degree v ≤ M.crossDegree A v := by
  rw [←degree_ofSimpleGraph,degree_eq_sum_mult]
  apply sum_le_sum
  intro w _
  change (if s(v,w) ∈ (M.crossingSupport A).edgeSet then 1 else 0) ≤
    (if ¬(v ∈ A ↔ w ∈ A) then M.mult s(v,w) else 0)
  simp only [mem_edgeSet]
  by_cases he : (M.crossingSupport A).Adj v w
  · rw [if_pos he,if_pos he.2]
    exact he.1
  · rw [if_neg he]
    exact Nat.zero_le _

theorem crossDegree_eq_degree_of_crossing (M : MultiGraph V) (A : Finset V)
    (hCross : ∀ x y, (x ∈ A ↔ y ∈ A) → M.mult s(x,y)=0) (v : V) : M.crossDegree A v=M.degree v := by
  rw [crossDegree,degree_eq_sum_mult]
  apply sum_congr rfl
  intro w _
  by_cases hc : v ∈ A ↔ w ∈ A
  · rw [if_neg (not_not.mpr hc),hCross v w hc]
  · rw [if_pos hc]

namespace PartialColouring.RouteInput
variable {M : MultiGraph V} {k : ℕ} {P : M.PartialColouring k} {i : Fin k} {a b : V}

theorem bundle_balance (s : RouteInput P i a b) (e : Sym2 V) :
    s.result.graph.mult e+s.removed.mult e=P.graph.mult e+s.added.mult e :=
  P.exchange_bundle_balance i s.removed s.added s.removed_le s.added_le s.proper e

theorem crossing_change (s : RouteInput P i a b) (A : Finset V)
    (hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0)
    (hAdd : ∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) (v : V) :
    s.result.graph.crossDegree A v=P.graph.crossDegree A v+s.added.degree v := by
  rw [←crossDegree_eq_degree_of_crossing s.added A hAdd v]
  simp only [crossDegree,←sum_add_distrib]
  apply sum_congr rfl
  intro w _
  by_cases hc : ¬(v ∈ A ↔ w ∈ A)
  · rw [if_pos hc,if_pos hc,if_pos hc]
    have hh := s.bundle_balance s(v,w)
    rw [hR v w hc] at hh
    omega
  · simp only [if_neg hc]

theorem crossing_residue_telescope (s : RouteInput P i a b) (A : Finset V)
    (hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0)
    (hAdd : ∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) (v : V) :
    s.result.graph.crossDegree A v+(s.result.colouring.missingPalette v).card+(P.available.internalPart A).degree v=
      P.graph.crossDegree A v+(P.colouring.missingPalette v).card+(s.result.available.internalPart A).degree v := by
  have hCross := s.crossing_change A hR hAdd v
  have hResidue : (s.result.available.internalPart A).degree v=
      (P.available.internalPart A).degree v+s.removed.degree v := by
    rw [s.internal_residue A hR hAdd,degree_addCopies]
  have hMissing := s.missingPalette_change v
  have hAdded := s.added_degree v
  have hRemoved := s.removed_degree v
  omega

theorem crossing_degree_growth (s : RouteInput P i a b) (A : Finset V)
    (hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0)
    (hAdd : ∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) (v : V) :
    s.result.graph.crossDegree A v ≤ P.graph.crossDegree A v+1 := by
  have hh := s.crossing_change A hR hAdd v
  have hOne := s.added_matching v
  omega

theorem crossing_support_change_le (s : RouteInput P i a b) (A : Finset V) (v : V) :
    (s.result.graph.crossingSupport A).degree v ≤
      (P.graph.crossingSupport A).degree v+s.added.degree v := by
  have hs : (s.result.graph.crossingSupport A).neighborFinset v ⊆
      (P.graph.crossingSupport A).neighborFinset v ∪ s.added.supportGraph.neighborFinset v := by
    intro w hw
    have hEdge := (mem_neighborFinset (s.result.graph.crossingSupport A) v w).mp hw
    have hh := s.bundle_balance s(v,w)
    by_cases hOld : 0 < P.graph.mult s(v,w)
    · exact mem_union_left _ ((mem_neighborFinset _ _ _).mpr ⟨hOld,hEdge.2⟩)
    · have hNew : 0 < s.result.graph.mult s(v,w) := hEdge.1
      have hAdd : 0 < s.added.mult s(v,w) := by omega
      exact mem_union_right _ ((mem_neighborFinset _ _ _).mpr hAdd)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  simp only [card_neighborFinset_eq_degree] at hc
  rw [s.added.supportGraph_degree_of_matching s.added_matching v] at hc
  exact hc

theorem simple_crossing_residue_balance (s : RouteInput P i a b) (A : Finset V)
    (hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0)
    (hAdd : ∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) (v : V) :
    (s.result.graph.crossingSupport A).degree v+(s.result.colouring.missingPalette v).card+
      (P.available.internalPart A).degree v ≤
      (P.graph.crossingSupport A).degree v+(P.colouring.missingPalette v).card+
        (s.result.available.internalPart A).degree v := by
  have hCross := s.crossing_support_change_le A v
  have hResidue : (s.result.available.internalPart A).degree v=
      (P.available.internalPart A).degree v+s.removed.degree v := by
    rw [s.internal_residue A hR hAdd,degree_addCopies]
  have hMissing := s.missingPalette_change v
  have hAdded := s.added_degree v
  have hRemoved := s.removed_degree v
  omega

theorem crossing_support_degree_bound (s : RouteInput P i a b) (A : Finset V)
    (hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0)
    (hAdd : ∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0) (v : V) :
    (s.result.graph.crossingSupport A).degree v ≤
      P.graph.crossDegree A v+(P.colouring.missingPalette v).card+(s.result.available.internalPart A).degree v := by
  have hTel := s.crossing_residue_telescope A hR hAdd v
  have hSupport := s.result.graph.crossingSupport_degree_le_crossDegree A v
  omega

end PartialColouring.RouteInput
end SimpleGraph.MultiGraph
