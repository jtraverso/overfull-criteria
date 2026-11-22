module

public import OverfullWork.ColourCrossingPotential

@[expose] public section


/-! # Forbidden cardinality throughout a recorded good run

Pay both the current crossing-color term and the current residue from
initial-state quantities. The bound is independent of run length.
-/
namespace SimpleGraph.MultiGraph.PartialColouring.GoodRouteRun
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
variable {A E : Finset V} {h ell : ℕ} {P Q : M.PartialColouring k} {n t : ℕ}
set_option maxHeartbeats 20000000

theorem forbidden_weighted_bound (run : GoodRouteRun A E h ell P Q n t) (j : Fin k) :
    h*((Q.colouring.colourGraph j).residueForbidden (Q.colouring.colourGraph_degree_le_one j)
      (Q.available.internalPart A) A E h).card ≤
      h*(2*(P.colouring.colourGraph j).cutSize A+(ell+1)*(P.colouring.missingSet univ j).card+2*E.card)+
        4*((P.available.internalPart A).edgeCount+ell*((∑ v, (P.colouring.missingPalette v).card)/2)) := by
  have hW := (Q.colouring.colourGraph j).residueForbidden_weighted_bound
    (Q.colouring.colourGraph_degree_le_one j) (Q.available.internalPart A) A E h
  change h*((Q.colouring.colourGraph j).residueForbidden (Q.colouring.colourGraph_degree_le_one j)
    (Q.available.internalPart A) A E h).card ≤
      h*((Q.colouring.missingSet univ j).card+2*(Q.colouring.colourGraph j).cutSize A+2*E.card)+
        4*(Q.available.internalPart A).edgeCount at hW
  have hColor := Nat.mul_le_mul_left h (Nat.add_le_add_right (run.colour_bad_budget j) (2*E.card))
  have hResidue := Nat.mul_le_mul_left 4 run.residue_size_budget
  omega

theorem forbidden_ratio_bound (run : GoodRouteRun A E h ell P Q n t) (j : Fin k) (hPos : 0 < h) :
    (((Q.colouring.colourGraph j).residueForbidden (Q.colouring.colourGraph_degree_le_one j)
      (Q.available.internalPart A) A E h).card:ℝ) ≤
      2*((P.colouring.colourGraph j).cutSize A:ℝ)+((ell:ℝ)+1)*(P.colouring.missingSet univ j).card+2*(E.card:ℝ)+
        4*((P.available.internalPart A).edgeCount+(ell:ℝ)*((∑ v, (P.colouring.missingPalette v).card)/2:ℕ))/(h:ℝ) := by
  have hW : (h:ℝ)*(((Q.colouring.colourGraph j).residueForbidden (Q.colouring.colourGraph_degree_le_one j)
      (Q.available.internalPart A) A E h).card:ℝ) ≤
      (h:ℝ)*(2*((P.colouring.colourGraph j).cutSize A:ℝ)+((ell:ℝ)+1)*(P.colouring.missingSet univ j).card+2*(E.card:ℝ))+
        4*((P.available.internalPart A).edgeCount+(ell:ℝ)*((∑ v, (P.colouring.missingPalette v).card)/2:ℕ)) := by
    exact_mod_cast run.forbidden_weighted_bound j
  have hPosR : (0:ℝ) < h := by exact_mod_cast hPos
  have hDiv := (div_mul_cancel₀
    (4*((P.available.internalPart A).edgeCount+(ell:ℝ)*((∑ v, (P.colouring.missingPalette v).card)/2:ℕ)))
    (ne_of_gt hPosR))
  apply (mul_le_mul_iff_left₀ hPosR).mp
  nlinarith only [hW,hDiv]

end SimpleGraph.MultiGraph.PartialColouring.GoodRouteRun
