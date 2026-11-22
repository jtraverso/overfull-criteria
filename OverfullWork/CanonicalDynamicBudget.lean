module

public import OverfullWork.InitialRouteBudgets

@[expose] public section


/-! # Explicit dynamic bounds for the actual Case 2 anchor state

Let A0 be the actual seed error and m the half order. Throughout any
recorded good run, |W_i| is bounded by initial quantities, not by a new
unproved current-state hypothesis.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
variable {R Q : p.completed.PartialColouring r.seedPalette} {h ell n t : ℕ}
set_option maxHeartbeats 24000000

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.missing_half_bound
    (budget : r.InitialRouteBudget R) :
    (((∑ v, (R.colouring.missingPalette v).card)/2:ℕ):ℝ) < (p.pairIndex+2:ℕ)*r.seedError := by
  have hh := Nat.mul_div_le (∑ v, (R.colouring.missingPalette v).card) 2
  have hhR : 2*(((∑ v, (R.colouring.missingPalette v).card)/2:ℕ):ℝ) ≤
      ((∑ v, (R.colouring.missingPalette v).card:ℕ):ℝ) := by exact_mod_cast hh
  have hTotal := budget.missing_total
  linarith

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.initial_potential_bound
    (budget : r.InitialRouteBudget R) (ell : ℕ) :
    ((R.available.internalPart s.part).edgeCount:ℝ)+(ell:ℝ)*((∑ v, (R.colouring.missingPalette v).card)/2:ℕ) <
      r.seedError*(5+(ell:ℝ)*(p.pairIndex+2:ℕ)) := by
  have hHalf := budget.missing_half_bound
  have hMul := mul_le_mul_of_nonneg_left hHalf.le (Nat.cast_nonneg ell : (0:ℝ) ≤ ell)
  have hResidue := budget.residue_size
  nlinarith only [hMul,hResidue]

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.dynamic_residue_size
    (budget : r.InitialRouteBudget R)
    (run : MultiGraph.PartialColouring.GoodRouteRun s.part s.initialExceptions h ell R Q n t) :
    ((Q.available.internalPart s.part).edgeCount:ℝ) < r.seedError*(5+(ell:ℝ)*(p.pairIndex+2:ℕ)) := by
  have hhR : ((Q.available.internalPart s.part).edgeCount:ℝ) ≤
      (R.available.internalPart s.part).edgeCount+(ell:ℝ)*((∑ v, (R.colouring.missingPalette v).card)/2:ℕ) := by
    exact_mod_cast run.residue_size_budget
  exact hhR.trans_lt (budget.initial_potential_bound ell)

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.dynamic_forbidden_bound
    (budget : r.InitialRouteBudget R)
    (run : MultiGraph.PartialColouring.GoodRouteRun s.part s.initialExceptions h ell R Q n t)
    (i : Fin r.seedPalette) (hPos : 0 < h) :
    (((Q.colouring.colourGraph i).residueForbidden (Q.colouring.colourGraph_degree_le_one i)
      (Q.available.internalPart s.part) s.part s.initialExceptions h).card:ℝ) <
      ((ell:ℝ)+1)*(6*r.seedError+2)+6*(T:ℝ)+8+
        4*r.seedError*(5+(ell:ℝ)*(p.pairIndex+2:ℕ))/(h:ℝ) := by
  have hW := run.forbidden_ratio_bound i hPos
  have hCut : ((R.colouring.colourGraph i).cutSize s.part:ℝ) ≤ 2 := by exact_mod_cast budget.colour_cut i
  have hColour := mul_le_mul_of_nonneg_left (budget.missing_colour i) (show (0:ℝ) ≤ (ell:ℝ)+1 by positivity)
  have hE : (s.initialExceptions.card:ℝ) ≤ 3*(T:ℝ)+2 := by exact_mod_cast budget.exceptions
  have hBase : 2*((R.colouring.colourGraph i).cutSize s.part:ℝ)+
      ((ell:ℝ)+1)*(R.colouring.missingSet univ i).card+2*(s.initialExceptions.card:ℝ) ≤
      ((ell:ℝ)+1)*(6*r.seedError+2)+6*(T:ℝ)+8 := by nlinarith only [hCut,hColour,hE]
  have hPosR : (0:ℝ) < h := by exact_mod_cast hPos
  have hFraction : 4*((R.available.internalPart s.part).edgeCount+
      (ell:ℝ)*((∑ v, (R.colouring.missingPalette v).card)/2:ℕ))/(h:ℝ) <
      4*r.seedError*(5+(ell:ℝ)*(p.pairIndex+2:ℕ))/(h:ℝ) := by
    apply (div_lt_div_iff_of_pos_right hPosR).mpr
    nlinarith only [budget.initial_potential_bound ell]
  linarith only [hW,hBase,hFraction]

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.residue_cap_of_scale
    (budget : r.InitialRouteBudget R) (hScale : 5*r.seedError ≤ (h:ℝ)) :
    ∀ v, (R.available.internalPart s.part).degree v ≤ h := by
  intro v
  have hDeg : (R.available.internalPart s.part).degree v ≤ (R.available.internalPart s.part).edgeCount :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have hDegR : ((R.available.internalPart s.part).degree v:ℝ) ≤ (R.available.internalPart s.part).edgeCount := by
    exact_mod_cast hDeg
  have hResidue := budget.residue_size
  exact_mod_cast (show ((R.available.internalPart s.part).degree v:ℝ) ≤ (h:ℝ) by linarith)

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.dynamic_deleted_degree
    (budget : r.InitialRouteBudget R)
    (run : MultiGraph.PartialColouring.GoodRouteRun s.part s.initialExceptions h ell R Q n t)
    (hScale : 5*r.seedError ≤ (h:ℝ)) (v : Fin (p.pairIndex+1) × Bool) (hv : v ∉ s.initialExceptions) :
    ((Q.graph.crossingSupport s.part).degree v:ℝ) < 2+6*r.seedError+(h:ℝ) := by
  have hhR : ((Q.graph.crossingSupport s.part).degree v:ℝ) ≤
      ((R.graph.crossingSupport s.part).degree v:ℝ)+(R.colouring.missingPalette v).card+(h:ℝ) := by
    exact_mod_cast run.deleted_degree_budget (budget.residue_cap_of_scale hScale) v
  have hInit : ((R.graph.crossingSupport s.part).degree v:ℝ) ≤ 2 := by exact_mod_cast budget.deleted_degree v hv
  have hMissing := budget.missing_vertex v
  linarith

end OverfullWork.NormalizedCanonicalCandidate
