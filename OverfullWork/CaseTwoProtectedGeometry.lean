module

public import OverfullWork.CaseTwoProtectedPreparation

@[expose] public section


/-! # Geometry retained throughout the protected first-centre run

All internal centre copies stay colored and no crossing copy away
from the centre is introduced. These are the sided facts used by CMS
when locating a conflicting color edge inside the opposite part.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 12000000

theorem Candidate.CaseTwoMiddleCopies.internal_centre_full (r : p.CaseTwoMiddleCopies s w)
    (v : Fin (p.pairIndex+1) × Bool) (hv : v ∈ s.part) :
    r.graph.mult s(p.centre,v)=p.completed.mult s(p.centre,v) := by
  change (p.completed.internalPart s.part).mult s(p.centre,v)+
    (MultiGraph.starCopies p.centre r.count (r.inside_zero _ s.centre_mem)).mult s(p.centre,v)=_
  rw [MultiGraph.internalPart_mult,MultiGraph.starCopies_mult]
  simp [s.centre_mem,hv,r.inside_zero v hv]

theorem Candidate.CaseTwoMiddleCopies.away_crossing_zero (r : p.CaseTwoMiddleCopies s w)
    (x y : Fin (p.pairIndex+1) × Bool) (hx : x ≠ p.centre) (hy : y ≠ p.centre)
    (hCross : ¬(x ∈ s.part ↔ y ∈ s.part)) : r.graph.mult s(x,y)=0 := by
  change (p.completed.internalPart s.part).mult s(x,y)+
    (MultiGraph.starCopies p.centre r.count (r.inside_zero _ s.centre_mem)).mult s(x,y)=_
  rw [MultiGraph.internalPart_mult,MultiGraph.starCopies_mult]
  simp [hCross,hx,hy]

theorem Candidate.CaseTwoMiddleCopies.protected_run_internal_centre_full
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q : p.completed.PartialColouring r.seedPalette} {n t : ℕ}
    (hRun : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n t)
    (v : Fin (p.pairIndex+1) × Bool) (hv : v ∈ s.part) :
    Q.graph.mult s(p.centre,v)=p.completed.mult s(p.centre,v) := by
  have hh := hRun.centre_bundle_mono v
  change r.graph.mult s(p.centre,v) ≤ Q.graph.mult s(p.centre,v) at hh
  rw [r.internal_centre_full v hv] at hh
  exact Nat.le_antisymm (Q.le _) hh

theorem Candidate.CaseTwoMiddleCopies.protected_run_away_crossing_zero
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q : p.completed.PartialColouring r.seedPalette} {n t : ℕ}
    (hRun : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n t)
    (x y : Fin (p.pairIndex+1) × Bool) (hx : x ≠ p.centre) (hy : y ≠ p.centre)
    (hCross : ¬(x ∈ s.part ↔ y ∈ s.part)) : Q.graph.mult s(x,y)=0 := by
  have ha : p.centre ∉ s(x,y) := by simp only [Sym2.mem_iff];tauto
  have hh := hRun.away_bundle_le s(x,y) ha
  change Q.graph.mult s(x,y) ≤ r.graph.mult s(x,y) at hh
  rw [r.away_crossing_zero x y hx hy hCross] at hh
  omega

theorem Candidate.CaseTwoMiddleCopies.protected_run_bundle_full
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    (hw : w ∉ s.part) {Q : p.completed.PartialColouring r.seedPalette} {n t : ℕ}
    (hRun : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n t) :
    Q.graph.mult s(b,w)=p.completed.mult s(b,w) := by
  have hab : p.centre ≠ b := by intro he;exact s.second_not_mem (he ▸ s.centre_mem)
  have haw : p.centre ≠ w := by intro he;exact hw (he ▸ s.centre_mem)
  exact (hRun.protected_bundle hab haw).trans
    (MiddleCopyGraph.opposite_mult p.completed s.part p.centre b w r.count
      (r.inside_zero _ s.centre_mem) s.centre_mem s.second_not_mem hw)

end OverfullWork.NormalizedCanonicalCandidate
