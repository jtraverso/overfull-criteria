module

public import OverfullWork.InitialResidueAccounting
public import OverfullWork.GoodMatchingForbidden

@[expose] public section


/-! # Forbidden-set bounds for the constructed initial anchor state

The residue budget is proved from actual run erasures. Crossing colored
edges meet the two anchors, so their endpoints are already excluded by
the exceptional set and its matching partners.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 16000000

theorem Candidate.CaseTwoMiddleCopies.initial_colour_crossing_meets_anchors
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q R : p.completed.PartialColouring r.seedPalette} {n₁ t₁ n₂ t₂ : ℕ}
    (hFirst : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n₁ t₁)
    (hSecond : MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q R n₂ t₂)
    (i : Fin r.seedPalette) (E : Finset (Fin (p.pairIndex+1) × Bool))
    (ha : p.centre ∈ E) (hb : b ∈ E) (x y : Fin (p.pairIndex+1) × Bool)
    (hCross : ¬(x ∈ s.part ↔ y ∈ s.part)) (hPos : 0 < (R.colouring.colourGraph i).mult s(x,y)) :
    x ∈ E ∨ y ∈ E := by
  by_contra! hn
  have hxa : x ≠ p.centre := by intro he;exact hn.1 (he ▸ ha)
  have hya : y ≠ p.centre := by intro he;exact hn.2 (he ▸ ha)
  have hxb : x ≠ b := by intro he;exact hn.1 (he ▸ hb)
  have hyb : y ≠ b := by intro he;exact hn.2 (he ▸ hb)
  have hz := r.initial_runs_away_crossing_zero C hFirst hSecond x y hxa hya hxb hyb hCross
  have hh := R.colouring.col_le_mult s(x,y) i
  change (R.colouring.colourGraph i).mult s(x,y) ≤ R.graph.mult s(x,y) at hh
  omega

theorem Candidate.CaseTwoMiddleCopies.initial_forbidden_weighted_bound
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q R : p.completed.PartialColouring r.seedPalette} {n₁ t₁ n₂ t₂ : ℕ}
    (hFirst : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n₁ t₁)
    (hSecond : MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q R n₂ t₂)
    (i : Fin r.seedPalette) (E : Finset (Fin (p.pairIndex+1) × Bool))
    (ha : p.centre ∈ E) (hb : b ∈ E) (h : ℕ) :
    h*((R.colouring.colourGraph i).residueForbidden (R.colouring.colourGraph_degree_le_one i)
      (R.available.internalPart s.part) s.part E h).card ≤
      h*((R.colouring.missingSet univ i).card+2*E.card)+4*(t₁+t₂) := by
  have hh := (R.colouring.colourGraph i).residueForbidden_weighted_localized
    (R.colouring.colourGraph_degree_le_one i) (R.available.internalPart s.part) s.part E h
    (r.initial_colour_crossing_meets_anchors C hFirst hSecond i E ha hb)
  have he := r.initial_residue_size C hFirst hSecond
  change h*((R.colouring.colourGraph i).residueForbidden (R.colouring.colourGraph_degree_le_one i)
    (R.available.internalPart s.part) s.part E h).card ≤
      h*((R.colouring.missingSet univ i).card+2*E.card)+4*(R.available.internalPart s.part).edgeCount at hh
  omega

theorem Candidate.CaseTwoMiddleCopies.exists_initial_forbidden_state
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
      (R.available.internalPart s.part).edgeCount ≤ t₁+t₂ ∧
      ((t₁+t₂:ℕ):ℝ) < 5*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9) ∧
      ∀ (i : Fin r.seedPalette) (E : Finset (Fin (p.pairIndex+1) × Bool)), p.centre ∈ E → b ∈ E →
        ∀ h : ℕ, (h:ℝ)*(((R.colouring.colourGraph i).residueForbidden
          (R.colouring.colourGraph_degree_le_one i) (R.available.internalPart s.part) s.part E h).card:ℝ) <
          (h:ℝ)*(6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+2+2*(E.card:ℝ))+
            20*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9) := by
  obtain ⟨Q,t₁,hFirst,ht₁,hSatA,_,_,_,hMissing,_,hPerColour⟩ :=
    r.exists_protected_centre_prepared_state hw hbw hD hT hHalf C hC hPalette
  have hReserve := r.second_anchor_reserve C hFirst (hMissing b) hGap
  obtain ⟨R,t₂,hSecond,ht₂,hSatB⟩ := MultiGraph.PartialColouring.exists_anchored_saturated_run
    s.part p.centre b s.second_not_mem Q hReserve
  have hab : p.centre ≠ b := by intro he;exact s.second_not_mem (he ▸ s.centre_mem)
  have ht₁R : (t₁:ℝ) ≤ 2*(C.missingPalette p.centre).card := by exact_mod_cast ht₁
  have ht₂R : (t₂:ℝ) ≤ (Q.colouring.missingPalette b).card := by exact_mod_cast ht₂
  have hSeed := r.seed_missing_bound hw hD hT C p.centre
  have hSum : ((t₁+t₂:ℕ):ℝ) <
      5*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9) := by
    rw [Nat.cast_add]
    linarith [hMissing b]
  refine ⟨Q,R,t₁,t₂,hFirst,hSecond,fun i => ⟨hSecond.preserves_saturation hab hSatA i,hSatB i⟩,
    r.initial_residue_size C hFirst hSecond,hSum,?_⟩
  intro i E ha hb h
  have hh := r.initial_forbidden_weighted_bound C hFirst hSecond i E ha hb h
  have hhR : (h:ℝ)*(((R.colouring.colourGraph i).residueForbidden
      (R.colouring.colourGraph_degree_le_one i) (R.available.internalPart s.part) s.part E h).card:ℝ) ≤
      (h:ℝ)*((R.colouring.missingSet univ i).card+2*(E.card:ℝ))+4*((t₁+t₂:ℕ):ℝ) := by exact_mod_cast hh
  have hMono := hSecond.toCentreRun.missingSet_mono i
  have hFinal : ((R.colouring.missingSet univ i).card:ℝ) ≤
      6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+2 := by
    exact (show ((R.colouring.missingSet univ i).card:ℝ) ≤ (Q.colouring.missingSet univ i).card by exact_mod_cast hMono).trans (hPerColour i)
  have hMul := mul_le_mul_of_nonneg_left hFinal (Nat.cast_nonneg h : (0:ℝ) ≤ h)
  nlinarith only [hhR,hSum,hMul]

end OverfullWork.NormalizedCanonicalCandidate
