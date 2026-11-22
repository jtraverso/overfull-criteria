module

public import OverfullWork.CaseTwoSecondAnchorReserve

@[expose] public section


/-! # Both initial anchors for the actual Case 2 seed

The only added condition is a displayed numerical gap on the center
bundle. It pays the actual neighbor reserve; no coloring or path
existence is supplied as a new oracle. Coupling that gap to the final
global case split and constructing the subsequent paths remain open.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 16000000

theorem Candidate.CaseTwoMiddleCopies.exists_initial_anchor_runs
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part) (hbw : b ≠ w)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T)
    (hHalf : p.pairIndex+1 ≤ G.maxDegree)
    (C : r.graph.EdgeColoring r.seedPalette) (hC : C.IsEquitable)
    (hPalette : r.seedPalette ≤ G.maxDegree)
    (hGap : (p.completed.mult s(p.centre,b):ℝ)+(B:ℝ)+η*(p.pairIndex+1:ℕ)+
      6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+4 ≤ G.maxDegree) :
    ∃ Q R : p.completed.PartialColouring r.seedPalette, ∃ t₁ t₂ : ℕ,
      MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q
        (C.missingPalette p.centre).card t₁ ∧
      MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q R
        (Q.colouring.missingPalette b).card t₂ ∧
      t₁ ≤ 2*(C.missingPalette p.centre).card ∧
      t₂ ≤ (Q.colouring.missingPalette b).card ∧
      (∀ i, (R.colouring.colourGraph i).degree p.centre=1 ∧
        (R.colouring.colourGraph i).degree b=1) ∧
      R.graph.mult s(b,w)=p.completed.mult s(b,w) ∧
      (∀ v ∈ s.part, R.graph.mult s(p.centre,v)=p.completed.mult s(p.centre,v)) ∧
      (∀ v, ((R.colouring.missingPalette v).card:ℝ) <
        6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)) ∧
      ∃ D : PriorityMCCPairing.Family R.colouring s.part, ∀ i,
        ((R.colouring.missingSet univ i).card:ℝ) ≤
          6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+2 := by
  obtain ⟨Q,t₁,hFirst,ht₁,hSatA,_,_,_,hMissing,_,hPerColour⟩ :=
    r.exists_protected_centre_prepared_state hw hbw hD hT hHalf C hC hPalette
  have hReserve := r.second_anchor_reserve C hFirst (hMissing b) hGap
  obtain ⟨R,t₂,hSecond,ht₂,hSatB⟩ :=
    MultiGraph.PartialColouring.exists_anchored_saturated_run s.part p.centre b
      s.second_not_mem Q hReserve
  have hab : p.centre ≠ b := by intro he;exact s.second_not_mem (he ▸ s.centre_mem)
  have hFinalA := hSecond.preserves_saturation hab hSatA
  have ht₂R : (t₂:ℝ) ≤ (Q.colouring.missingPalette b).card := by exact_mod_cast ht₂
  have hV : Even (Fintype.card (Fin (p.pairIndex+1) × Bool)) := by
    refine ⟨p.pairIndex+1,?_⟩
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  obtain ⟨D⟩ := PriorityMCCPairing.exists_family R.colouring s.part hV
  refine ⟨Q,R,t₁,t₂,hFirst,hSecond,ht₁,ht₂,fun i => ⟨hFinalA i,hSatB i⟩,?_,?_,?_,D,?_⟩
  · exact (hSecond.second_bundle w hw).trans (r.protected_run_bundle_full C hw hFirst)
  · intro v hv
    exact (hSecond.anchor_bundle hab v).trans (r.protected_run_internal_centre_full C hFirst v hv)
  · intro v
    have hh := hSecond.toCentreRun.missingPalette_growth_le v
    have hhR : ((R.colouring.missingPalette v).card:ℝ) ≤
        (Q.colouring.missingPalette v).card+(t₂:ℝ) := by exact_mod_cast hh
    have hQv := hMissing v
    have hQb := hMissing b
    linarith
  · intro i
    have hh := hSecond.toCentreRun.missingSet_mono i
    have hhR : ((R.colouring.missingSet univ i).card:ℝ) ≤
        (Q.colouring.missingSet univ i).card := by exact_mod_cast hh
    exact hhR.trans (hPerColour i)

theorem Candidate.CaseTwoMiddleCopies.initial_runs_away_crossing_zero
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q R : p.completed.PartialColouring r.seedPalette} {n₁ t₁ n₂ t₂ : ℕ}
    (hFirst : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n₁ t₁)
    (hSecond : MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q R n₂ t₂)
    (x y : Fin (p.pairIndex+1) × Bool) (hxa : x ≠ p.centre) (hya : y ≠ p.centre)
    (hxb : x ≠ b) (hyb : y ≠ b) (hCross : ¬(x ∈ s.part ↔ y ∈ s.part)) :
    R.graph.mult s(x,y)=0 := by
  have hb : b ∉ s(x,y) := by simp only [Sym2.mem_iff];tauto
  have hh := hSecond.away_bundle_le s(x,y) hb
  have hz := r.protected_run_away_crossing_zero C hFirst x y hxa hya hCross
  omega

end OverfullWork.NormalizedCanonicalCandidate
