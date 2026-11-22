module

public import OverfullWork.CutMassBounds

@[expose] public section


/-! # Per-color crossing/missing potential during good route exchanges

The selected cut grows by at most ell+1, while its missing set loses
two vertices. Other colors do not change. This pays the crossing term
in the forbidden-set estimate throughout a recorded good run.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 20000000

theorem RouteInput.selected_cut_change {P : M.PartialColouring k} {i : Fin k} {a b : V}
    (s : RouteInput P i a b) (A : Finset V)
    (hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0) :
    (s.result.colouring.colourGraph i).cutSize A=(P.colouring.colourGraph i).cutSize A+s.added.cutSize A := by
  have hEq := P.exchange_colour_selected i s.removed s.added s.removed_le s.added_le s.proper
  change s.result.colouring.colourGraph i=_ at hEq
  rw [hEq]
  apply cutSize_exchange
  intro x hx y hy
  exact hR x y (by have hn := mem_compl.mp hy;tauto)

theorem RouteInput.colour_cut_missing_potential {P : M.PartialColouring k} {i : Fin k} {a b : V}
    (s : RouteInput P i a b) (A : Finset V) (ell : ℕ)
    (hR : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0)
    (hLength : s.removed.edgeCount ≤ ell) (j : Fin k) :
    2*(s.result.colouring.colourGraph j).cutSize A+(ell+1)*(s.result.colouring.missingSet univ j).card ≤
      2*(P.colouring.colourGraph j).cutSize A+(ell+1)*(P.colouring.missingSet univ j).card := by
  by_cases hj : j=i
  · subst j
    have hCut := s.selected_cut_change A hR
    have hAdd := s.added.cutSize_le_edgeCount A
    have hCount : s.added.edgeCount=s.removed.edgeCount+1 := by
      rw [s.added_count,s.removed_count]
    have hMissing := s.missing_drop_two
    rw [hMissing,Nat.mul_add]
    omega
  · have hEq := s.other_colour j hj
    have hMissing : s.result.colouring.missingSet univ j=P.colouring.missingSet univ j := by
      ext v
      simp only [EdgeColoring.missingSet,mem_filter]
      rw [hEq]
    rw [hEq,hMissing]

namespace GoodRouteRun
variable {A E : Finset V} {h ell : ℕ} {P Q : M.PartialColouring k} {n t : ℕ}

theorem colour_cut_missing_potential (run : GoodRouteRun A E h ell P Q n t) (j : Fin k) :
    2*(Q.colouring.colourGraph j).cutSize A+(ell+1)*(Q.colouring.missingSet univ j).card ≤
      2*(P.colouring.colourGraph j).cutSize A+(ell+1)*(P.colouring.missingSet univ j).card := by
  induction run with
  | refl P => exact le_refl _
  | step s hGood hAdd hProtected hLen tail ih =>
    exact ih.trans (s.colour_cut_missing_potential A ell (s.removed_internal_of_good A h hGood) hLen j)

theorem colour_bad_budget (run : GoodRouteRun A E h ell P Q n t) (j : Fin k) :
    (Q.colouring.missingSet univ j).card+2*(Q.colouring.colourGraph j).cutSize A ≤
      2*(P.colouring.colourGraph j).cutSize A+(ell+1)*(P.colouring.missingSet univ j).card := by
  have hh := run.colour_cut_missing_potential j
  have hLe : (Q.colouring.missingSet univ j).card ≤ (ell+1)*(Q.colouring.missingSet univ j).card := by
    have hm := Nat.mul_le_mul_right (Q.colouring.missingSet univ j).card (show 1 ≤ ell+1 by omega)
    simpa only [one_mul] using hm
  omega

theorem residue_size_budget (run : GoodRouteRun A E h ell P Q n t) :
    (Q.available.internalPart A).edgeCount ≤
      (P.available.internalPart A).edgeCount+ell*((∑ v, (P.colouring.missingPalette v).card)/2) := by
  have hh := run.residue_potential
  omega

end GoodRouteRun
end SimpleGraph.MultiGraph.PartialColouring
