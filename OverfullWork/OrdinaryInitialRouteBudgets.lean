module

public import OverfullWork.InitialRouteBudgets

@[expose] public section


/-! # Preserve the ordinary crossing-degree bound in the initial interface

The numerical budget and stronger degree statement refer to the same
state constructed by the two actual anchor runs. Existing interfaces
and proof sources remain unchanged.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 24000000

theorem Candidate.CaseTwoMiddleCopies.exists_initial_route_budget_with_ordinary_degree
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part) (hbw : b ≠ w)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T) (hHalf : p.pairIndex+1 ≤ G.maxDegree)
    (C : r.graph.EdgeColoring r.seedPalette) (hC : C.IsEquitable) (hPalette : r.seedPalette ≤ G.maxDegree)
    (hGap : (p.completed.mult s(p.centre,b):ℝ)+(B:ℝ)+η*(p.pairIndex+1:ℕ)+6*r.seedError+4 ≤ G.maxDegree) :
    ∃ R : p.completed.PartialColouring r.seedPalette, r.InitialRouteBudget R ∧
      (∀ v, v ≠ p.centre → v ≠ b → (R.graph.crossingSupport s.part).degree v ≤ 2) ∧
      (R.available.internalPart s.part).degree p.centre=0 ∧
      R.graph.mult s(b,w)=p.completed.mult s(b,w) := by
  obtain ⟨Q,R,t₁,t₂,hFirst,hSecond,ht₁,ht₂,hSat,hBundle,hInternal,hMissing,D,hColour⟩ :=
    r.exists_initial_anchor_runs hw hbw hD hT hHalf C hC hPalette hGap
  have hSeed := r.seed_missing_bound hw hD hT C p.centre
  change ((C.missingPalette p.centre).card:ℝ) < r.seedError at hSeed
  have hError : 0 < r.seedError := lt_of_le_of_lt (Nat.cast_nonneg _) hSeed
  have ht₁R : (t₁:ℝ) ≤ 2*(C.missingPalette p.centre).card := by exact_mod_cast ht₁
  have ht₂R : (t₂:ℝ) ≤ (Q.colouring.missingPalette b).card := by exact_mod_cast ht₂
  have hQb : ((Q.colouring.missingPalette b).card:ℝ) < 3*r.seedError := by
    have hh := hFirst.missingPalette_growth_le b
    have hhR : ((Q.colouring.missingPalette b).card:ℝ) ≤ (C.missingPalette b).card+(t₁:ℝ) := by exact_mod_cast hh
    have hbSeed := r.seed_missing_bound hw hD hT C b
    change ((C.missingPalette b).card:ℝ) < r.seedError at hbSeed
    linarith
  have hResidue := r.initial_residue_size C hFirst hSecond
  have hResidueR : ((R.available.internalPart s.part).edgeCount:ℝ) ≤ (t₁:ℝ)+(t₂:ℝ) := by exact_mod_cast hResidue
  have hFirstTotal := hFirst.total_missing_growth_le
  change (∑ v, (Q.colouring.missingPalette v).card) ≤
    (∑ v, (C.missingPalette v).card)+2*(C.missingPalette p.centre).card at hFirstTotal
  have hFirstR : ((∑ v, (Q.colouring.missingPalette v).card:ℕ):ℝ) ≤
      ((∑ v, (C.missingPalette v).card:ℕ):ℝ)+2*(C.missingPalette p.centre).card := by exact_mod_cast hFirstTotal
  have hSecondR : ((∑ v, (R.colouring.missingPalette v).card:ℕ):ℝ) ≤
      ((∑ v, (Q.colouring.missingPalette v).card:ℕ):ℝ) := by exact_mod_cast hSecond.total_missing_mono
  have hSeedSum : ((∑ v, (C.missingPalette v).card:ℕ):ℝ) ≤ 2*(p.pairIndex+1:ℕ)*r.seedError := by
    simpa only [Nat.cast_sum,Candidate.CaseTwoMiddleCopies.seedError] using r.seed_total_missing_bound hw hD hT C
  have hCentreZero : (R.available.internalPart s.part).degree p.centre=0 := by
    rw [MultiGraph.degree_internalPart,if_pos s.centre_mem]
    unfold MultiGraph.degreeInto
    apply sum_eq_zero
    intro v hv
    change p.completed.mult s(p.centre,v)-R.graph.mult s(p.centre,v)=0
    rw [hInternal v hv,Nat.sub_self]
  refine ⟨R, ?_, (fun v hva hvb => r.initial_crossing_support_degree C hFirst hSecond v hva hvb),hCentreZero,hBundle⟩
  refine {
    anchors := hSat
    error_pos := hError
    missing_vertex := hMissing
    missing_colour := hColour
    missing_total := ?_
    residue_size := by linarith
    colour_cut := ?_
    deleted_degree := ?_
    exceptions := s.initialExceptions_card hD hT
  }
  · have hm : ((p.pairIndex+2:ℕ):ℝ)=((p.pairIndex+1:ℕ):ℝ)+1 := by push_cast;ring
    rw [hm]
    nlinarith only [hFirstR,hSecondR,hSeedSum,hSeed]
  · intro i
    have hCover := r.initial_colour_crossing_meets_anchors C hFirst hSecond i ({p.centre,b}:Finset _)
      (by simp) (by simp)
    have hh := (R.colouring.colourGraph i).matching_cut_le_cover (R.colouring.colourGraph_degree_le_one i)
      s.part {p.centre,b} hCover
    have hPair : ({p.centre,b}:Finset (Fin (p.pairIndex+1) × Bool)).card ≤ 2 :=
      (card_insert_le _ _).trans (by simp)
    exact hh.trans hPair
  · intro v hv
    have ha : v ≠ p.centre := by intro he;exact hv (by simp [Candidate.CaseTwoPartition.initialExceptions,he])
    have hb : v ≠ b := by intro he;exact hv (by simp [Candidate.CaseTwoPartition.initialExceptions,he])
    exact r.initial_crossing_support_degree C hFirst hSecond v ha hb


end OverfullWork.NormalizedCanonicalCandidate
