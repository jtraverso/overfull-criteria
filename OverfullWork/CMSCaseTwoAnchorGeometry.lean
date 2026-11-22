module

public import OverfullWork.CMSCaseTwoEquitableSeed
public import OverfullWork.AnchoredCentreRun
public import OverfullWork.InitialResidueAccounting

@[expose] public section


/-! Bundle inequalities common to the initial runs of CMS Step 3. -/
namespace SimpleGraph.MultiGraph.PartialColouring

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
variable {P Q : M.PartialColouring k} {a : V}

/-- A centre step only adds at the centre and removes away from it. -/
theorem CentreStep.bundle_bounds (h : CentreStep P Q a) (e : Sym2 V) :
    (a ∈ e → P.graph.mult e ≤ Q.graph.mult e) ∧
    (a ∉ e → Q.graph.mult e ≤ P.graph.mult e) := by
  rw [h.updated]
  change (_ → P.graph.mult e ≤
      P.graph.mult e-h.removed.mult e+(unitEdge a h.neighbour h.distinct).mult e) ∧
    (_ → P.graph.mult e-h.removed.mult e+(unitEdge a h.neighbour h.distinct).mult e ≤
      P.graph.mult e)
  constructor
  · intro he
    have hRemoved : h.removed.mult e ≤ h.removed.degree a := by
      exact single_le_sum (f := h.removed.mult) (fun _ _ => Nat.zero_le _)
        (mem_filter.mpr ⟨mem_univ _,he⟩)
    rw [h.centre_free] at hRemoved
    omega
  · intro he
    have hne : e ≠ s(a,h.neighbour) := by
      intro heq
      exact he (heq ▸ (by simp : a ∈ s(a,h.neighbour)))
    change P.graph.mult e-h.removed.mult e+(if e=s(a,h.neighbour) then 1 else 0) ≤ _
    simp [hne]

theorem CentreRun.bundle_bounds {n t : ℕ} (h : CentreRun a P Q n t) (e : Sym2 V) :
    (a ∈ e → P.graph.mult e ≤ Q.graph.mult e) ∧
    (a ∉ e → Q.graph.mult e ≤ P.graph.mult e) := by
  induction h with
  | refl P => exact ⟨fun _ => le_rfl,fun _ => le_rfl⟩
  | step h _ ih =>
    exact ⟨fun he => ((h.bundle_bounds e).1 he).trans (ih.1 he),
      fun he => (ih.2 he).trans ((h.bundle_bounds e).2 he)⟩

theorem CentreRun.lost_copies_le {n t : ℕ} (h : CentreRun a P Q n t) :
    (P.graph.subtractCopies Q.graph).edgeCount ≤ t := by
  induction h with
  | refl P => simp [edgeCount,subtractCopies]
  | @step P Q R n t h tail ih =>
    have hTri := lost_copies_triangle P.graph Q.graph R.graph
    have hStep : (P.graph.subtractCopies Q.graph).edgeCount ≤ h.removed.edgeCount := by
      apply sum_le_sum
      intro e _
      have hh := congrArg (fun S : M.PartialColouring k => S.graph.mult e) h.updated
      change Q.graph.mult e = P.graph.mult e-h.removed.mult e+
        (unitEdge a h.neighbour h.distinct).mult e at hh
      change P.graph.mult e-Q.graph.mult e ≤ h.removed.mult e
      omega
    omega

end SimpleGraph.MultiGraph.PartialColouring

namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V}
variable {a b w : V} {d m L r t k : ℕ} {η : ℝ}
variable {s : CaseTwoPartition M a b d m L r t η}

/-- Regard the equitable seed as a partial colouring of the actual
regular host. -/
noncomputable def CaseTwoMiddleCopies.partialSeed (copies : CaseTwoMiddleCopies s w)
    (C : copies.graph.EdgeColoring k) : M.PartialColouring k :=
  ⟨copies.graph,C,copies.graph_le⟩

theorem CaseTwoMiddleCopies.internal_centre_full (copies : CaseTwoMiddleCopies s w)
    (v : V) (hv : v ∈ s.part) :
    copies.graph.mult s(a,v) = M.mult s(a,v) := by
  change (M.internalPart s.part).mult s(a,v)+
    (MultiGraph.starCopies a copies.count (copies.inside_zero _ s.centre_mem)).mult s(a,v) = _
  rw [MultiGraph.internalPart_mult,MultiGraph.starCopies_mult]
  simp [s.centre_mem,hv,copies.inside_zero v hv]

theorem CaseTwoMiddleCopies.away_crossing_zero (copies : CaseTwoMiddleCopies s w)
    (u v : V) (hu : u ≠ a) (hv : v ≠ a) (hCross : ¬(u ∈ s.part ↔ v ∈ s.part)) :
    copies.graph.mult s(u,v) = 0 := by
  change (M.internalPart s.part).mult s(u,v)+
    (MultiGraph.starCopies a copies.count (copies.inside_zero _ s.centre_mem)).mult s(u,v) = _
  rw [MultiGraph.internalPart_mult,MultiGraph.starCopies_mult]
  simp [hCross,hu,hv]

theorem CaseTwoMiddleCopies.initial_residue_size (copies : CaseTwoMiddleCopies s w)
    (C : copies.graph.EdgeColoring k) {Q R : M.PartialColouring k} {n₁ u n₂ v : ℕ}
    (hFirst : if b = w then
      MultiGraph.PartialColouring.CentreRun a (copies.partialSeed C) Q n₁ u
      else MultiGraph.PartialColouring.ProtectedRun a b w (copies.partialSeed C) Q n₁ u)
    (hSecond : MultiGraph.PartialColouring.AnchoredRun s.part a b Q R n₂ v) :
    (R.available.internalPart s.part).edgeCount ≤ u+v := by
  have hTri := MultiGraph.lost_copies_triangle copies.graph Q.graph R.graph
  have hLostFirst : (copies.graph.subtractCopies Q.graph).edgeCount ≤ u := by
    split_ifs at hFirst <;> exact hFirst.lost_copies_le
  have hLostSecond := hSecond.lost_copies_le
  have hLe : (R.available.internalPart s.part).edgeCount ≤ (copies.graph.subtractCopies R.graph).edgeCount := by
    apply sum_le_sum
    intro e _
    change (if e.toFinset ⊆ s.part ∨ e.toFinset ⊆ s.partᶜ then
      M.mult e-R.graph.mult e else 0) ≤ copies.graph.mult e-R.graph.mult e
    split_ifs with he
    · have hFull : M.mult e ≤ copies.graph.mult e := by
        change M.mult e ≤ (M.internalPart s.part).mult e +
          (MultiGraph.starCopies a copies.count (copies.inside_zero _ s.centre_mem)).mult e
        change M.mult e ≤ (if e.toFinset ⊆ s.part ∨ e.toFinset ⊆ s.partᶜ then M.mult e else 0)+_
        rw [if_pos he]
        omega
      exact Nat.sub_le_sub_right hFull _
    · exact Nat.zero_le _
  omega

end OverfullWork.CMSBalancedCut
