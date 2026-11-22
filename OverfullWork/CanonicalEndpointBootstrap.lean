module

public import OverfullWork.RobustSeedCompletion
public import OverfullWork.CanonicalDynamicBudget

@[expose] public section


/-! # CMS endpoint bootstrap in the actual canonical Case 2 state

Reuse the rank profile at the first two canonical positions. The
initial ordinary crossing bound comes from the two actual anchor runs;
the current forbidden set and deletion losses are paid from the seed
error. This also covers missing endpoints in the partner set.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 32000000

theorem Candidate.CaseTwoMiddleCopies.bootstrap_at_current_missing
    (C : r.graph.EdgeColoring r.seedPalette)
    {Q₀ R Q : p.completed.PartialColouring r.seedPalette} {n₁ t₁ n₂ t₂ h ell n t : ℕ}
    (hFirst : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q₀ n₁ t₁)
    (hSecond : MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q₀ R n₂ t₂)
    (budget : r.InitialRouteBudget R)
    (run : MultiGraph.PartialColouring.GoodRouteRun s.part s.initialExceptions h ell R Q n t)
    (hCentre : p.centre=(0,false)) (hSecondPos : b=(0,true))
    (hHalf : p.pairIndex+1 ≤ G.maxDegree) (hScale : 5*r.seedError ≤ (h:ℝ)) (hPos : 0 < h)
    (hLoss : ((B+c.setᶜ.card:ℕ):ℝ)+η*(p.pairIndex+1:ℕ) ≤ (p.pairIndex+1:ℕ)/16)
    (hForbidden : ((ell:ℝ)+1)*(6*r.seedError+2)+6*(T:ℝ)+8+
      4*r.seedError*(5+(ell:ℝ)*(p.pairIndex+2:ℕ))/(h:ℝ) ≤ (p.pairIndex+1:ℕ)/32)
    (hDeletion : 2+6*r.seedError+(h:ℝ) ≤ (p.pairIndex+1:ℕ)/32)
    (i : Fin r.seedPalette) (v : Fin (p.pairIndex+1) × Bool)
    (hv : v ∈ Q.colouring.missingSet univ i) :
    ((p.pairIndex+1:ℕ):ℝ)/8 < (Q.bootstrapSet s.part
      ((Q.colouring.colourGraph i).residueForbidden (Q.colouring.colourGraph_degree_le_one i)
        (Q.available.internalPart s.part) s.part s.initialExceptions h) v).card := by
  have hv₀ := run.missing_endpoint_ne_saturated i p.centre v
    (by rw [(budget.anchors i).1];decide) hv
  have hv₁ := run.missing_endpoint_ne_saturated i b v
    (by rw [(budget.anchors i).2];decide) hv
  have hSupport := p.ordinary_support_half_bound hCentre v (by simpa only [hCentre] using hv₀)
    (by simpa only [hSecondPos] using hv₁)
  have hd : ((Q.graph.crossingSupport s.part).degree v:ℝ) ≤
      (R.graph.crossingSupport s.part).degree v+(R.colouring.missingPalette v).card+(h:ℝ) := by
    exact_mod_cast run.deleted_degree_budget (budget.residue_cap_of_scale hScale) v
  have hd₀ : ((R.graph.crossingSupport s.part).degree v:ℝ) ≤ 2 := by
    exact_mod_cast r.initial_crossing_support_degree C hFirst hSecond v hv₀ hv₁
  have hMissing := budget.missing_vertex v
  have hDeleted : ((Q.graph.crossingSupport s.part).degree v:ℝ) ≤ (p.pairIndex+1:ℕ)/32 := by linarith
  have hW := (budget.dynamic_forbidden_bound run i hPos).le.trans hForbidden
  let D := if v ∈ s.part then s.partᶜ else s.part
  have hSide : (v ∈ s.part ∧ D=s.partᶜ) ∨ (v ∉ s.part ∧ D=s.part) := by
    by_cases hh : v ∈ s.part <;> simp [D,hh]
  exact Q.bootstrap_card_gt_eighth s.part _ v D hSide (p.pairIndex+1) G.maxDegree
    ((B+c.setᶜ.card:ℕ):ℝ) (η*(p.pairIndex+1:ℕ)) hHalf hSupport (s.simple_discrepancy v) hLoss hW hDeleted

end OverfullWork.NormalizedCanonicalCandidate
