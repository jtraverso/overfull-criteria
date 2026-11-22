module

public import OverfullWork.ProtectedCanonicalResiduePalette

@[expose] public section


/-! # Pay the fresh palette reserve from the constructed scalar bounds

The seed uses less than Delta/2+A0 colors. The proved q<5A0,
A0<=m/100 and h<=m/32 then put seedPalette+q+3h strictly below Delta.
No additional coloring or matching assumption is used.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 24000000

theorem Candidate.CaseTwoMiddleCopies.seed_palette_lt_half_add_error
    (r : p.CaseTwoMiddleCopies s w) : (r.seedPalette:ℝ) < (G.maxDegree:ℝ)/2+r.seedError := by
  have hη : 0 ≤ η*(p.pairIndex+1:ℕ) :=
    (abs_nonneg _).trans (s.simple_discrepancy p.centre).le
  have hbase : 0 ≤ ((G.maxDegree:ℝ)+η*(p.pairIndex+1:ℕ)+3*(B:ℝ)+
      ((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+7)/2 := by positivity
  have hceil := Nat.ceil_lt_add_one hbase
  change (r.seedDegreeBound:ℝ) < _ at hceil
  have hk : (r.seedPalette:ℝ)=(r.seedDegreeBound:ℝ)+(B:ℝ)+1 := by
    simp only [Candidate.CaseTwoMiddleCopies.seedPalette,Nat.cast_add,Nat.cast_one]
    ring
  have hB : (0:ℝ) ≤ B := Nat.cast_nonneg _
  have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have hDiv : (0:ℝ) ≤ ((p.pairIndex+1)/T:ℕ) := Nat.cast_nonneg _
  dsimp only [Candidate.CaseTwoMiddleCopies.seedError]
  linarith

theorem Candidate.CaseTwoMiddleCopies.residue_palette_lt_delta
    (r : p.CaseTwoMiddleCopies s w) (q h : ℕ)
    (hHalf : p.pairIndex+1 ≤ G.maxDegree) (hCount : (q:ℝ) < 5*r.seedError)
    (hError : r.seedError ≤ (p.pairIndex+1:ℕ)/100) (hCap : (h:ℝ) ≤ (p.pairIndex+1:ℕ)/32) :
    r.seedPalette+(q+3*h) < G.maxDegree := by
  have hk := r.seed_palette_lt_half_add_error
  have hHalfR : ((p.pairIndex+1:ℕ):ℝ) ≤ G.maxDegree := by exact_mod_cast hHalf
  have hm : (0:ℝ) ≤ (p.pairIndex+1:ℕ) := Nat.cast_nonneg _
  have hResult : (r.seedPalette:ℝ)+((q:ℝ)+3*(h:ℝ)) < G.maxDegree := by linarith
  exact_mod_cast hResult

end OverfullWork.NormalizedCanonicalCandidate
