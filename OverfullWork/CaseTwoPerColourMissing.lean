module

public import OverfullWork.CaseTwoSeedReserves
public import OverfullWork.EquitableMissingCounts

@[expose] public section


/-! # CMS (5.11) with the actual seed's explicit quantitative error -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 12000000

theorem Candidate.image_half_order_le_delta (p : Candidate c) (hWeak : Fintype.card V ≤ 2*G.maxDegree) :
    p.pairIndex+1 ≤ G.maxDegree := by
  have hCoords := Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts := card_add_card_compl c.set
  omega

theorem Candidate.CaseTwoMiddleCopies.seed_palette_ge_half (r : p.CaseTwoMiddleCopies s w) :
    G.maxDegree ≤ 2*r.seedPalette := by
  have hη : 0 ≤ η*(p.pairIndex+1:ℕ) :=
    (abs_nonneg _).trans (s.simple_discrepancy p.centre).le
  have hceil := Nat.le_ceil (((G.maxDegree:ℝ)+η*(p.pairIndex+1:ℕ)+3*(B:ℝ)+
    ((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+7)/2)
  change _ ≤ (r.seedDegreeBound:ℝ) at hceil
  have hk : (r.seedPalette:ℝ) = (r.seedDegreeBound:ℝ)+(B:ℝ)+1 := by
    simp only [Candidate.CaseTwoMiddleCopies.seedPalette,Nat.cast_add,Nat.cast_one]
    ring
  have hB : (0:ℝ) ≤ B := Nat.cast_nonneg _
  have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have hL : (0:ℝ) ≤ ((p.pairIndex+1)/T:ℕ) := Nat.cast_nonneg _
  exact_mod_cast (show (G.maxDegree:ℝ) ≤ 2*(r.seedPalette:ℝ) by linarith)

theorem Candidate.CaseTwoMiddleCopies.seed_per_colour_missing
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T)
    (hHalf : p.pairIndex+1 ≤ G.maxDegree)
    (C : r.graph.EdgeColoring r.seedPalette) (hC : C.IsEquitable) (i : Fin r.seedPalette) :
    ((C.missingSet univ i).card:ℝ) ≤
      4*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+2 := by
  have hη : 0 ≤ η*(p.pairIndex+1:ℕ) :=
    (abs_nonneg _).trans (s.simple_discrepancy p.centre).le
  have hratio : 2*(p.pairIndex+1) ≤ 4*r.seedPalette := by
    have hh := r.seed_palette_ge_half
    omega
  have hk : 0 < r.seedPalette := by omega
  apply C.equitable_missing_real_bound hC 4 _ hk (by positivity)
  · have hh : Fintype.card (Fin (p.pairIndex+1) × Bool) ≤ 4*r.seedPalette := by
      simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
      omega
    exact_mod_cast hh
  · simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,
      mul_comm,mul_left_comm,mul_assoc] using r.seed_total_missing_bound hw hD hT C

end OverfullWork.NormalizedCanonicalCandidate
