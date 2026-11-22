module

public import OverfullWork.CaseTwoInitialAnchors

@[expose] public section


/-! # Actual internal residue after both initial anchor runs

Charge every lost seed copy to the copies discarded in the two actual
runs. This avoids treating a bound on the residue as an extra input.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

theorem lost_copies_triangle (P Q R : MultiGraph V) :
    (P.subtractCopies R).edgeCount ≤ (P.subtractCopies Q).edgeCount+(Q.subtractCopies R).edgeCount := by
  unfold edgeCount
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro e _
  change P.mult e-R.mult e ≤ (P.mult e-Q.mult e)+(Q.mult e-R.mult e)
  omega

namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

theorem ProtectedStep.lost_copies_le {P Q : M.PartialColouring k} {a b w : V}
    (h : ProtectedStep P Q a b w) : (P.graph.subtractCopies Q.graph).edgeCount ≤ h.removed.edgeCount := by
  apply sum_le_sum
  intro e _
  have hh := h.balance e
  change P.graph.mult e-Q.graph.mult e ≤ h.removed.mult e
  omega

theorem ProtectedRun.lost_copies_le {P Q : M.PartialColouring k} {a b w : V} {n t : ℕ}
    (h : ProtectedRun a b w P Q n t) : (P.graph.subtractCopies Q.graph).edgeCount ≤ t := by
  induction h with
  | refl P => simp [edgeCount,subtractCopies]
  | @step P Q R n t h tail ih =>
    have hTri := lost_copies_triangle P.graph Q.graph R.graph
    have hStep := h.lost_copies_le
    omega

theorem AnchoredStep.lost_copies_le {P Q : M.PartialColouring k} {A : Finset V} {a b : V}
    (h : AnchoredStep P Q A a b) : (P.graph.subtractCopies Q.graph).edgeCount ≤ h.step.removed.edgeCount := by
  apply sum_le_sum
  intro e _
  have hh := h.bundle_balance e
  change P.graph.mult e-Q.graph.mult e ≤ h.step.removed.mult e
  omega

theorem AnchoredRun.lost_copies_le {P Q : M.PartialColouring k} {A : Finset V} {a b : V} {n t : ℕ}
    (h : AnchoredRun A a b P Q n t) : (P.graph.subtractCopies Q.graph).edgeCount ≤ t := by
  induction h with
  | refl P => simp [edgeCount,subtractCopies]
  | @step P Q R n t h tail ih =>
    have hTri := lost_copies_triangle P.graph Q.graph R.graph
    have hStep := h.lost_copies_le
    omega

end PartialColouring
end SimpleGraph.MultiGraph

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}

theorem Candidate.CaseTwoMiddleCopies.internal_full (r : p.CaseTwoMiddleCopies s w)
    (e : Sym2 (Fin (p.pairIndex+1) × Bool))
    (he : e.toFinset ⊆ s.part ∨ e.toFinset ⊆ s.partᶜ) : r.graph.mult e=p.completed.mult e := by
  have hLower : p.completed.mult e ≤ r.graph.mult e := by
    change p.completed.mult e ≤ (p.completed.internalPart s.part).mult e+
      (MultiGraph.starCopies p.centre r.count (r.inside_zero _ s.centre_mem)).mult e
    change p.completed.mult e ≤ (if e.toFinset ⊆ s.part ∨ e.toFinset ⊆ s.partᶜ then p.completed.mult e else 0)+_
    rw [if_pos he]
    omega
  exact Nat.le_antisymm (r.graph_le e) hLower

theorem Candidate.CaseTwoMiddleCopies.initial_residue_size
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q R : p.completed.PartialColouring r.seedPalette} {n₁ t₁ n₂ t₂ : ℕ}
    (hFirst : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n₁ t₁)
    (hSecond : MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q R n₂ t₂) :
    (R.available.internalPart s.part).edgeCount ≤ t₁+t₂ := by
  have hTri := MultiGraph.lost_copies_triangle r.graph Q.graph R.graph
  have hF := hFirst.lost_copies_le
  have hS := hSecond.lost_copies_le
  have hLe : (R.available.internalPart s.part).edgeCount ≤ (r.graph.subtractCopies R.graph).edgeCount := by
    apply sum_le_sum
    intro e _
    change (if e.toFinset ⊆ s.part ∨ e.toFinset ⊆ s.partᶜ then p.completed.mult e-R.graph.mult e else 0) ≤
      r.graph.mult e-R.graph.mult e
    split_ifs with he
    · rw [r.internal_full e he]
    · exact Nat.zero_le _
  change (r.graph.subtractCopies Q.graph).edgeCount ≤ t₁ at hF
  omega

end OverfullWork.NormalizedCanonicalCandidate
