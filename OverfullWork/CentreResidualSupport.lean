module

public import OverfullWork.StageOneFirstAnchor

@[expose] public section


/-! Row-local support loss and the finite first-anchor alternatives.

The small/large split can be applied after selecting the middle copies:
small residual neighbourhoods are cleared, while every later lost
neighbour is charged to an actually added centre copy.
-/
namespace SimpleGraph.MultiGraph
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem crossing_support_row_growth (M N : MultiGraph V) (A : Finset V) (v : V)
    (hMono : ∀ w, M.mult s(v,w) ≤ N.mult s(v,w)) :
    (N.crossingSupport A).degree v+M.degree v ≤ (M.crossingSupport A).degree v+N.degree v := by
  have hSub : (N.crossingSupport A).neighborFinset v ⊆
      (M.crossingSupport A).neighborFinset v ∪ (N.subtractCopies M).supportGraph.neighborFinset v := by
    intro w hw
    have hAdj := (mem_neighborFinset _ v w).mp hw
    by_cases hOld : 0 < M.mult s(v,w)
    · exact mem_union_left _ ((mem_neighborFinset _ v w).mpr ⟨hOld,hAdj.2⟩)
    · exact mem_union_right _ ((mem_neighborFinset _ v w).mpr (by
        change 0 < N.mult s(v,w)-M.mult s(v,w)
        have hh := hAdj.1
        omega))
  have hCount := (card_le_card hSub).trans (card_union_le _ _)
  simp only [card_neighborFinset_eq_degree] at hCount
  have hDegree : (N.subtractCopies M).degree v+M.degree v=N.degree v := by
    rw [degree_eq_sum_mult,degree_eq_sum_mult,degree_eq_sum_mult,←sum_add_distrib]
    exact sum_congr rfl (fun w _ => Nat.sub_add_cancel (hMono w))
  have hSupport := (N.subtractCopies M).support_degree_le_degree v
  omega

namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

theorem first_anchor_mass_of_cleared_available_neighbours (S : M.PartialColouring k)
    (A Z : Finset V) (a : V) (D : ℕ) (i : Fin k) (ha : a ∈ A)
    (hRegular : M.IsRegularOfDegree D) (hPalette : k < D) (hCover : S.CoversInternal A)
    (hNeighbour : ∀ v, 0 < S.available.mult s(a,v) → v ∈ Z)
    (hClear : ∀ v ∈ Z, v ∈ Aᶜ → (S.colouring.colourGraph i).degree v=0) :
    0 < S.available.degreeInto (S.colouring.missingSet Aᶜ i) a := by
  have hDegree := S.available_degree a
  have hBound := S.colouring.degree_le_palette a
  rw [hRegular a] at hDegree
  have hPositive : 0 < S.available.degree a := by omega
  rw [MultiGraph.degree_eq_sum_mult] at hPositive
  obtain ⟨v,_,hCopy⟩ := sum_pos_iff.mp hPositive
  have hvZ := hNeighbour v hCopy
  have hvSide : v ∉ A := by
    intro hvA
    have hFull := hCover a v (by tauto)
    change 0 < M.mult s(a,v)-S.graph.mult s(a,v) at hCopy
    rw [hFull,Nat.sub_self] at hCopy
    omega
  exact S.first_anchor_mass_of_missing_candidate A a v i
    (mem_filter.mpr ⟨mem_compl.mpr hvSide,hClear v hvZ (mem_compl.mpr hvSide)⟩) hCopy

theorem first_anchor_mass_of_many_neighbours (S : M.PartialColouring k)
    (A : Finset V) (a : V) (i : Fin k) (ha : a ∈ A)
    (hMany : (Aᶜ\S.colouring.missingSet Aᶜ i).card < (S.available.crossingSupport A).degree a) :
    0 < S.available.degreeInto (S.colouring.missingSet Aᶜ i) a := by
  have hNotSub : ¬(S.available.crossingSupport A).neighborFinset a ⊆
      Aᶜ\S.colouring.missingSet Aᶜ i := by
    intro hh
    have hc := card_le_card hh
    rw [card_neighborFinset_eq_degree] at hc
    omega
  obtain ⟨v,hv,hNot⟩ := not_subset.mp hNotSub
  have hAdj := (mem_neighborFinset _ a v).mp hv
  have hvB : v ∈ Aᶜ := mem_compl.mpr (by
    have hh := hAdj.2
    tauto)
  have hvMissing : v ∈ S.colouring.missingSet Aᶜ i := by
    by_contra hh
    exact hNot (mem_sdiff.mpr ⟨hvB,hh⟩)
  exact S.first_anchor_mass_of_missing_candidate A a v i hvMissing hAdj.1

end PartialColouring
end SimpleGraph.MultiGraph
