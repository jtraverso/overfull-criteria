module

public import OverfullWork.CertifiedRouteExchange

@[expose] public section


/-! # Coupled bookkeeping over actual good route exchanges

The run stores legal copy updates and their proved good-edge geometry.
No existence of all required paths is asserted. The initial and final
state budgets telescope, with a simple crossing-degree bound independent
of the multiplicities of the initially colored crossing bundles.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.PairedRoutes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 24000000

theorem RouteInput.removed_internal_of_good {P : M.PartialColouring k} {i : Fin k} {a b : V}
    (s : RouteInput P i a b) (A : Finset V) (h : ℕ)
    (hGood : ∀ e, s.removed.mult e ≤ ((P.colouring.colourGraph i).goodMatching (P.available.internalPart A) A h).mult e)
    (x y : V) (hCross : ¬(x ∈ A ↔ y ∈ A)) : s.removed.mult s(x,y)=0 := by
  have hh := hGood s(x,y)
  rw [goodMatching_internal _ _ _ _ x y hCross] at hh
  omega

inductive GoodRouteRun (A E : Finset V) (h ell : ℕ) :
    M.PartialColouring k → M.PartialColouring k → ℕ → ℕ → Prop
  | refl (P) : GoodRouteRun A E h ell P P 0 0
  | step {P Q n t} {i : Fin k} {a b : V} (s : RouteInput P i a b)
      (good : ∀ e, s.removed.mult e ≤ ((P.colouring.colourGraph i).goodMatching (P.available.internalPart A) A h).mult e)
      (crossing : ∀ x y, (x ∈ A ↔ y ∈ A) → s.added.mult s(x,y)=0)
      (safe_rows : ∀ x ∈ E, s.removed.degree x=0)
      (length : s.removed.edgeCount ≤ ell)
      (tail : GoodRouteRun A E h ell s.result Q n t) :
      GoodRouteRun A E h ell P Q (n+1) (s.removed.edgeCount+t)

namespace GoodRouteRun
variable {A E : Finset V} {h ell : ℕ} {P Q : M.PartialColouring k} {n t : ℕ}

theorem size_change (run : GoodRouteRun A E h ell P Q n t) : Q.graph.edgeCount=P.graph.edgeCount+n := by
  induction run with
  | refl P => omega
  | step s hGood hAdd hProtected hLen tail ih => have hh := s.size_change;omega

theorem total_missing_drop (run : GoodRouteRun A E h ell P Q n t) :
    (∑ v, (P.colouring.missingPalette v).card)=(∑ v, (Q.colouring.missingPalette v).card)+2*n := by
  induction run with
  | refl P => omega
  | step s hGood hAdd hProtected hLen tail ih => have hh := s.total_missing_drop;omega

theorem removed_bound (run : GoodRouteRun A E h ell P Q n t) : t ≤ ell*n := by
  induction run with
  | refl P => omega
  | step s hGood hAdd hProtected hLen tail ih => rw [Nat.mul_succ];omega

theorem residue_size (run : GoodRouteRun A E h ell P Q n t) :
    (Q.available.internalPart A).edgeCount=(P.available.internalPart A).edgeCount+t := by
  induction run with
  | refl P => omega
  | @step P Q n t i a b s hGood hAdd hProtected hLen tail ih =>
    have hs : (s.result.available.internalPart A).edgeCount=
        (P.available.internalPart A).edgeCount+s.removed.edgeCount := by
      rw [s.internal_residue A (s.removed_internal_of_good A h hGood) hAdd,edgeCount_addCopies]
    omega

theorem residue_potential (run : GoodRouteRun A E h ell P Q n t) :
    (Q.available.internalPart A).edgeCount+ell*((∑ v, (Q.colouring.missingPalette v).card)/2) ≤
      (P.available.internalPart A).edgeCount+ell*((∑ v, (P.colouring.missingPalette v).card)/2) := by
  have hSize := run.residue_size
  have hMissing := run.total_missing_drop
  have hRemoved := run.removed_bound
  have hDiv : (∑ v, (P.colouring.missingPalette v).card)/2=
      (∑ v, (Q.colouring.missingPalette v).card)/2+n := by omega
  rw [hSize,hDiv,Nat.mul_add]
  omega

theorem residue_cap (run : GoodRouteRun A E h ell P Q n t)
    (hCap : ∀ v, (P.available.internalPart A).degree v ≤ h) :
    ∀ v, (Q.available.internalPart A).degree v ≤ h := by
  induction run with
  | refl P => exact hCap
  | step s hGood hAdd hProtected hLen tail ih =>
    exact ih (s.internal_residue_cap A h hGood hAdd hCap)

theorem protected_rows (run : GoodRouteRun A E h ell P Q n t) (v : V) (hv : v ∈ E) :
    (Q.available.internalPart A).degree v=(P.available.internalPart A).degree v := by
  induction run with
  | refl P => rfl
  | step s hGood hAdd hProtected hLen tail ih =>
    exact ih.trans (s.internal_residue_protected A (s.removed_internal_of_good A h hGood) hAdd v (hProtected v hv))

theorem missingPalette_mono (run : GoodRouteRun A E h ell P Q n t) (v : V) :
    (Q.colouring.missingPalette v).card ≤ (P.colouring.missingPalette v).card := by
  induction run with
  | refl P => exact le_refl _
  | step s hGood hAdd hProtected hLen tail ih => have hh := s.missingPalette_change v;omega

theorem per_colour_missing_mono (run : GoodRouteRun A E h ell P Q n t) (j : Fin k) :
    (Q.colouring.missingSet univ j).card ≤ (P.colouring.missingSet univ j).card := by
  induction run with
  | refl P => exact le_refl _
  | @step P Q n t i a b s hGood hAdd hProtected hLen tail ih =>
    by_cases hj : j=i
    · subst j;have hh := s.missing_drop_two;omega
    · have heq := s.other_colour j hj
      have hMissing : s.result.colouring.missingSet univ j=P.colouring.missingSet univ j := by
        ext v
        simp only [EdgeColoring.missingSet,mem_filter]
        rw [heq]
      rw [hMissing] at ih
      exact ih

theorem crossing_residue_balance (run : GoodRouteRun A E h ell P Q n t) (v : V) :
    (Q.graph.crossingSupport A).degree v+(Q.colouring.missingPalette v).card+(P.available.internalPart A).degree v ≤
      (P.graph.crossingSupport A).degree v+(P.colouring.missingPalette v).card+(Q.available.internalPart A).degree v := by
  induction run with
  | refl P => omega
  | step s hGood hAdd hProtected hLen tail ih =>
    have hh := s.simple_crossing_residue_balance A (s.removed_internal_of_good A h hGood) hAdd v
    omega

theorem deleted_degree_budget (run : GoodRouteRun A E h ell P Q n t)
    (hCap : ∀ v, (P.available.internalPart A).degree v ≤ h) (v : V) :
    (Q.graph.crossingSupport A).degree v ≤
      (P.graph.crossingSupport A).degree v+(P.colouring.missingPalette v).card+h := by
  have hh := run.crossing_residue_balance v
  have hEnd := run.residue_cap hCap v
  omega

theorem initial_deleted_degree_budget (run : GoodRouteRun A E h ell P Q n t) (B : ℕ)
    (hCap : ∀ v, (P.available.internalPart A).degree v ≤ h)
    (hInitial : ∀ v, v ∉ E → (P.graph.crossingSupport A).degree v ≤ 2)
    (hMissing : ∀ v, (P.colouring.missingPalette v).card ≤ B) :
    ∀ v, v ∉ E → (Q.graph.crossingSupport A).degree v ≤ 2+B+h := by
  intro v hv
  have hh := run.deleted_degree_budget hCap v
  have h₀ := hInitial v hv
  have hM := hMissing v
  omega

end GoodRouteRun
end SimpleGraph.MultiGraph.PartialColouring
