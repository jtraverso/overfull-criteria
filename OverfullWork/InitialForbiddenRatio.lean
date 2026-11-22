module

public import OverfullWork.InitialForbiddenBudget

@[expose] public section


/-! # An explicit initial analogue of CMS (5.13)

With A0 the proved seed error, the constructed initial state satisfies
|W_i| < 6 A0 + 6 T + 6 + 20 A0 / h for each positive residue cutoff h.
The exceptional set is the actual partner set plus the two anchors.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 16000000

def Candidate.CaseTwoPartition.initialExceptions (s : p.CaseTwoPartition P T η b) :
    Finset (Fin (p.pairIndex+1) × Bool) := insert p.centre (insert b s.partners)

theorem Candidate.CaseTwoPartition.initialExceptions_card (s : p.CaseTwoPartition P T η b)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T) : s.initialExceptions.card ≤ 3*T+2 := by
  have heq := Fintype.card_congr s.partnerEquiv
  simp only [Fintype.card_coe] at heq
  have hHeavy := RegularHeavyCutRepair.heavySet_card_at_scale p.completed p.centre b G.maxDegree
    (p.pairIndex+1) T p.completion.regular hD hT
  have h₁ := card_insert_le p.centre (insert b s.partners)
  have h₂ := card_insert_le b s.partners
  change s.initialExceptions.card ≤ _ at h₁
  omega

theorem Candidate.CaseTwoMiddleCopies.exists_initial_forbidden_ratio
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part) (hbw : b ≠ w)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T) (hHalf : p.pairIndex+1 ≤ G.maxDegree)
    (C : r.graph.EdgeColoring r.seedPalette) (hC : C.IsEquitable) (hPalette : r.seedPalette ≤ G.maxDegree)
    (hGap : (p.completed.mult s(p.centre,b):ℝ)+(B:ℝ)+η*(p.pairIndex+1:ℕ)+
      6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+4 ≤ G.maxDegree) :
    ∃ Q R : p.completed.PartialColouring r.seedPalette, ∃ t₁ t₂,
      MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q
        (C.missingPalette p.centre).card t₁ ∧
      MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q R
        (Q.colouring.missingPalette b).card t₂ ∧
      (∀ i, (R.colouring.colourGraph i).degree p.centre=1 ∧ (R.colouring.colourGraph i).degree b=1) ∧
      ∀ (i : Fin r.seedPalette) (h : ℕ), 0 < h →
        (((R.colouring.colourGraph i).residueForbidden (R.colouring.colourGraph_degree_le_one i)
          (R.available.internalPart s.part) s.part s.initialExceptions h).card:ℝ) <
          6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+6*(T:ℝ)+6+
            20*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)/(h:ℝ) := by
  obtain ⟨Q,R,t₁,t₂,hFirst,hSecond,hSat,_,_,hW⟩ :=
    r.exists_initial_forbidden_state hw hbw hD hT hHalf C hC hPalette hGap
  refine ⟨Q,R,t₁,t₂,hFirst,hSecond,hSat,?_⟩
  intro i h hh
  have hBound := hW i s.initialExceptions (by simp [Candidate.CaseTwoPartition.initialExceptions])
    (by simp [Candidate.CaseTwoPartition.initialExceptions]) h
  have hCard : (s.initialExceptions.card:ℝ) ≤ 3*(T:ℝ)+2 := by
    exact_mod_cast s.initialExceptions_card hD hT
  have hPaid := mul_le_mul_of_nonneg_left hCard (Nat.cast_nonneg h : (0:ℝ) ≤ h)
  have hPos : (0:ℝ) < h := by exact_mod_cast hh
  have hDiv := (div_mul_cancel₀
    (20*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)) (ne_of_gt hPos))
  apply (mul_lt_mul_iff_left₀ hPos).mp
  nlinarith only [hBound,hPaid,hDiv]

end OverfullWork.NormalizedCanonicalCandidate
