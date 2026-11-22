module

public import OverfullWork.FirstAnchorUnitMass

@[expose] public section


/-! Source-paid surviving centre bundles for the first Stage I anchor. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun RegularHeavyCutRepair
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 24000000

theorem Candidate.CaseTwoMiddleCopies.fresh_bundle_error_le
    (r : p.CaseTwoMiddleCopies s w) (q h : ℕ) (hq : (q:ℝ) < 5*r.seedError) :
    ((B+2+2*Nat.ceil r.seedError+2*(q+3*h):ℕ):ℝ) ≤ 14*r.seedError+6*(h:ℝ) := by
  have hBasic := r.seed_error_basics
  have hCeil := Nat.ceil_lt_add_one hBasic.2
  push_cast
  linarith [show (0:ℝ) ≤ T from Nat.cast_nonneg _,show (0:ℝ) ≤ B from Nat.cast_nonneg _]

theorem Candidate.CaseTwoMiddleCopies.large_bundle_free_in_fresh_state
    (r : p.CaseTwoMiddleCopies s w) (Q : p.completed.PartialColouring r.seedPalette)
    (q h : ℕ) (S : p.completed.PartialColouring (r.seedPalette+(q+3*h))) (ρ : ℝ)
    (hMono : ∀ e, Q.graph.mult e ≤ S.graph.mult e)
    (hFilled : Q.graph.degree p.centre=r.seedPalette)
    (hRow : ∀ v ∈ s.partᶜ, Q.graph.mult s(p.centre,v) ≤ r.count v+Nat.ceil r.seedError)
    (hw : w ∉ s.part) (hq : (q:ℝ) < 5*r.seedError)
    (hError : r.seedError ≤ ρ*(p.pairIndex+1:ℕ)/10000)
    (hCap : (h:ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/1024)
    (hLoss : ((B+c.setᶜ.card:ℕ):ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/10000)
    (v : Fin (p.pairIndex+1) × Bool) (hv : v ∈ s.partᶜ)
    (hLarge : ρ*(p.pairIndex+1:ℕ)/32 < (p.completed.mult s(p.centre,v):ℝ)+(B+c.setᶜ.card:ℕ)) :
    0 < S.available.mult s(p.centre,v) := by
  have hFree := r.fresh_free_bundle Q (q+3*h) S hMono hFilled hRow hw v hv
  have hFreeR : (p.completed.mult s(p.centre,v):ℝ) ≤
      2*(S.available.mult s(p.centre,v):ℝ)+(B+2+2*Nat.ceil r.seedError+2*(q+3*h):ℕ) := by
    have hh : p.completed.mult s(p.centre,v) ≤ 2*S.available.mult s(p.centre,v)+
      (B+2+2*Nat.ceil r.seedError+2*(q+3*h)) := by omega
    exact_mod_cast hh
  have hErr := r.fresh_bundle_error_le q h hq
  have hρm : 0 < ρ*(p.pairIndex+1:ℕ) := by
    have hBasic := r.seed_error_basics.1
    have hB : (0:ℝ) ≤ B := Nat.cast_nonneg _
    have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
    linarith
  exact_mod_cast (show (0:ℝ) < S.available.mult s(p.centre,v) by linarith)

theorem Candidate.CaseTwoMiddleCopies.large_bundle_across
    (r : p.CaseTwoMiddleCopies s w) (ρ : ℝ)
    (hError : r.seedError ≤ ρ*(p.pairIndex+1:ℕ)/10000)
    (v : Fin (p.pairIndex+1) × Bool) (hvb : v ≠ b)
    (hLarge : ρ*(p.pairIndex+1:ℕ)/32 < (p.completed.mult s(p.centre,v):ℝ)) : v ∈ s.partᶜ := by
  have hη : 0 ≤ η*(p.pairIndex+1:ℕ) := (abs_nonneg _).trans (s.simple_discrepancy p.centre).le
  have hDiv : (((p.pairIndex+1)/T:ℕ):ℝ) ≤ r.seedError := by
    dsimp only [Candidate.CaseTwoMiddleCopies.seedError]
    linarith [show (0:ℝ) ≤ B from Nat.cast_nonneg _,show (0:ℝ) ≤ T from Nat.cast_nonneg _]
  have hBasic := r.seed_error_basics.2
  have hLargeNat : (p.pairIndex+1)/T < p.completed.mult s(p.centre,v) := by
    exact_mod_cast (show (((p.pairIndex+1)/T:ℕ):ℝ) < p.completed.mult s(p.centre,v) by linarith)
  exact mem_compl.mpr (s.heavy_across v hvb hLargeNat)

end OverfullWork.NormalizedCanonicalCandidate
