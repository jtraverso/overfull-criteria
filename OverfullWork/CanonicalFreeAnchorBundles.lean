module

public import OverfullWork.ProtectedCentreRowBounds
public import OverfullWork.CanonicalAnchorBundles
public import OverfullWork.CanonicalDynamicBudget

@[expose] public section


/-! # Available centre-bundle reserves after actual seed completion

Only the initial centre-saturation gain can add copies at the centre.
The second anchor stage preserves that row, and the protected saturated
good run leaves it fixed. The middle allocation then supplies the
half-bundle reserve needed by CMS Step 4.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 24000000

theorem Candidate.CaseTwoMiddleCopies.free_centre_bundle_reserve
    (C : r.graph.EdgeColoring r.seedPalette)
    {Q₀ R Q : p.completed.PartialColouring r.seedPalette} {t₁ n₂ t₂ h ell n t : ℕ}
    (hFirst : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q₀
      (C.missingPalette p.centre).card t₁)
    (hSecond : MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q₀ R n₂ t₂)
    (budget : r.InitialRouteBudget R) (E : Finset (Fin (p.pairIndex+1) × Bool)) (haE : p.centre ∈ E)
    (run : MultiGraph.PartialColouring.GoodRouteRun s.part E h ell R Q n t)
    (hw : w ∉ s.part) (v : Fin (p.pairIndex+1) × Bool) (hv : v ∈ s.partᶜ) :
    p.completed.mult s(p.centre,v) ≤ 2*Q.available.mult s(p.centre,v)+B+2+
      2*(C.missingPalette p.centre).card := by
  have hab : p.centre ≠ b := by intro he;exact s.second_not_mem (he ▸ s.centre_mem)
  have hEmpty : R.colouring.missingPalette p.centre=∅ := by
    apply eq_empty_of_forall_notMem
    intro i hi
    have hz := (mem_filter.mp hi).2
    rw [(budget.anchors i).1] at hz
    omega
  have hDegree : R.graph.degree p.centre=r.seedPalette := by
    have hh := R.colouring.missingPalette_card_add_degree p.centre
    rw [hEmpty,card_empty] at hh
    omega
  have hFixed := run.protected_saturated_bundle p.centre haE hDegree v
  have hGrowth := hFirst.centre_bundle_growth_le v
  have hCount : (r.partialSeed C).graph.mult s(p.centre,v)=r.count v :=
    MiddleCopyGraph.crossing_mult p.completed s.part p.centre v r.count
      (r.inside_zero _ s.centre_mem) s.centre_mem (mem_compl.mp hv)
  rw [hCount] at hGrowth
  have hAnchor := hSecond.anchor_bundle hab v
  have hCol : Q.graph.mult s(p.centre,v) ≤ r.count v+(C.missingPalette p.centre).card := by
    rw [hFixed,hAnchor]
    exact hGrowth
  have hUpper := r.bundle_upper v
  simp only [Candidate.CaseTwoPartition.crossWeight,if_pos hv] at hUpper
  have hSmall := p.off_centre_bundle_le b w (Ne.symm hab)
    (by intro he;exact hw (he ▸ s.centre_mem))
  have hCap := Q.le s(p.centre,v)
  have hAvailable : Q.available.mult s(p.centre,v)+Q.graph.mult s(p.centre,v)=p.completed.mult s(p.centre,v) := by
    change p.completed.mult s(p.centre,v)-Q.graph.mult s(p.centre,v)+Q.graph.mult s(p.centre,v)=_
    omega
  omega

end OverfullWork.NormalizedCanonicalCandidate
