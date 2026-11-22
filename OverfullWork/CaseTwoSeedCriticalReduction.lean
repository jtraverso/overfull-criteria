module

public import OverfullWork.CaseTwoMiddleDegreeProfile
public import OverfullWork.MultigraphCopyCritical
public import OverfullWork.EquitableRecolouring
public import OverfullWork.CopyColouringExtraction
public import OverfullWork.DeletedCopyKempeState
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section


/-! # An equitable Case 2 seed or an actual bounded-row critical witness

The palette is computed from the verified degree profile. The right
alternative is a copy-critical subgraph with a nonisolated bounded-row
root and an actual coloring after deleting one incident edge copy.
Excluding this alternative still needs the multigraph multifan lemma.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 8000000

noncomputable def Candidate.CaseTwoMiddleCopies.seedDegreeBound (r : p.CaseTwoMiddleCopies s w) : ℕ :=
  ⌈((G.maxDegree:ℝ)+η*(p.pairIndex+1:ℕ)+3*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+7)/2⌉₊

noncomputable def Candidate.CaseTwoMiddleCopies.seedPalette (r : p.CaseTwoMiddleCopies s w) : ℕ :=
  r.seedDegreeBound+(B+1)

theorem Candidate.CaseTwoMiddleCopies.degree_le_seed_bound (r : p.CaseTwoMiddleCopies s w)
    (hw : w ∉ s.part) (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T)
    (v : Fin (p.pairIndex+1) × Bool) : r.graph.degree v ≤ r.seedDegreeBound := by
  have hu := (abs_le.mp (r.degree_profile_at_cutoff hw hD hT v)).2
  have hc := Nat.le_ceil (((G.maxDegree:ℝ)+η*(p.pairIndex+1:ℕ)+3*(B:ℝ)+
    ((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+7)/2)
  have hh : (r.graph.degree v:ℝ) ≤ (r.seedDegreeBound:ℝ) := by
    change _ ≤ (r.seedDegreeBound:ℝ) at hc
    linarith
  exact_mod_cast hh

theorem Candidate.CaseTwoMiddleCopies.equitable_seed_or_bounded_row_critical
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T) :
    (∃ C : r.graph.EdgeColoring r.seedPalette, C.IsEquitable) ∨
      ∃ N : MultiGraph (Fin (p.pairIndex+1) × Bool),
        (∀ e, N.mult e ≤ r.graph.mult e) ∧ N.IsCopyCritical r.seedPalette ∧
        (∀ v, N.degree v ≤ r.seedDegreeBound) ∧ ∃ u v,
          u ≠ p.centre ∧ u ≠ v ∧ 0 < N.mult s(u,v) ∧ N.mult s(p.centre,u) < B+1 ∧
          (∀ z, N.mult s(u,z) ≤ B+1) ∧ Nonempty ((N.eraseOne s(u,v)).EdgeColoring r.seedPalette) := by
  by_cases hc : Nonempty (r.graph.EdgeColoring r.seedPalette)
  · obtain ⟨C⟩ := hc
    exact Or.inl C.exists_equitable
  · exact Or.inr (r.graph.exists_bounded_row_critical_witness p.centre r.seedDegreeBound (B+1)
      (r.degree_le_seed_bound hw hD hT) r.off_centre_multiplicity_le hc)

theorem Candidate.CaseTwoMiddleCopies.critical_kempe_witness_of_no_seed
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T)
    (hNo : ¬∃ C : r.graph.EdgeColoring r.seedPalette, C.IsEquitable) :
    ∃ (N : MultiGraph (Fin (p.pairIndex+1) × Bool)) (u v : Fin (p.pairIndex+1) × Bool),
      (∀ e, N.mult e ≤ r.graph.mult e) ∧ N.IsCopyCritical r.seedPalette ∧
      (∀ z, N.degree z ≤ r.seedDegreeBound) ∧
      u ≠ p.centre ∧ u ≠ v ∧ 0 < N.mult s(u,v) ∧ N.mult s(p.centre,u) < B+1 ∧
      (∀ z, N.mult s(u,z) ≤ B+1) ∧
      ∃ col : N.FreshCopies u v → Fin r.seedPalette,
        ShannonColouring.ProperOn (N.freshEnds u v) (univ.erase none) col ∧
        B+2 ≤ (univ.filter (ShannonColouring.Misses (N.freshEnds u v) (univ.erase none) col u)).card ∧
        ∀ z, B+1 ≤ (univ.filter (ShannonColouring.Misses (N.freshEnds u v) (univ.erase none) col z)).card := by
  have hUn : ¬Nonempty (r.graph.EdgeColoring r.seedPalette) := by
    rintro ⟨C⟩
    exact hNo C.exists_equitable
  obtain ⟨N,hNJ,hcrit,hdeg,u,v,hua,huv,hpos,hsmall,hrow,_⟩ :=
    r.graph.exists_bounded_row_critical_witness p.centre r.seedDegreeBound (B+1)
      (r.degree_le_seed_bound hw hD hT) r.off_centre_multiplicity_le hUn
  obtain ⟨col,hcol,hroot,hrest⟩ := hcrit.exists_deleted_kempe_state r.seedDegreeBound (B+1)
    hdeg (by omega) u v hpos
  exact ⟨N,u,v,hNJ,hcrit,hdeg,hua,huv,hpos,hsmall,hrow,col,hcol,
    (show B+2 ≤ B+1+1 by omega).trans hroot,hrest⟩

end OverfullWork.NormalizedCanonicalCandidate
