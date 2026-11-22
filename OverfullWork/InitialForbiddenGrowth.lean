module

public import OverfullWork.CrossingSupport
public import OverfullWork.BipartiteAlternatingGrowth

@[expose] public section


/-! # Actual matching and deletion data for initial alternating growth

Both the matching permutation and its safe set are constructed from
the current color. The initial deleted-degree loss is proved to be
two; it is not passed in as an unexplained local hypothesis.
This is still a growth-of-sets statement, not a path-existence theorem.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun BipartiteRobustMargin
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 16000000

theorem Candidate.CaseTwoMiddleCopies.initial_alternating_growth
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q R : p.completed.PartialColouring r.seedPalette} {n₁ t₁ n₂ t₂ : ℕ}
    (hFirst : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n₁ t₁)
    (hSecond : MultiGraph.PartialColouring.AnchoredRun s.part p.centre b Q R n₂ t₂)
    (i : Fin r.seedPalette) (E : Finset (Fin (p.pairIndex+1) × Bool))
    (ha : p.centre ∈ E) (hb : b ∈ E) (h : ℕ)
    (A : Finset (Fin (p.pairIndex+1) × Bool)) (hSide : A=s.part ∨ A=s.partᶜ) :
    let L := R.colouring.colourGraph i
    let hL := R.colouring.colourGraph_degree_le_one i
    let W := L.residueForbidden hL (R.available.internalPart s.part) s.part E h
    let τ := L.matchingPartner hL
    let F := R.graph.crossingSupport s.part
    let gain := (p.pairIndex+1)/(2^30*P^3)-4*(3*T+1)
    let cutoff := (p.pairIndex+1)/(1024*P)+2*(3*T+1)
    ∀ X : Finset (Fin (p.pairIndex+1) × Bool), X ⊆ A\W →
      cutoff ≤ X.card → X.card+cutoff ≤ A.card →
      (X.image τ).card=X.card ∧ X.image τ ⊆ A\W ∧
        alternatingStep p.completed.supportGraph F Aᶜ W τ gain 2 X ⊆ Aᶜ\W ∧
        X.card+gain ≤ (alternatingStep p.completed.supportGraph F Aᶜ W τ gain 2 X).card+W.card ∧
        ∀ v ∈ alternatingStep p.completed.supportGraph F Aᶜ W τ gain 2 X,
          gain-2 ≤ PrunedCore.neighboursIn (p.completed.supportGraph\F) (X.image τ) v := by
  dsimp only
  intro X hX hLow hHigh
  apply BipartiteRobustMargin.alternating_growth
    (t := (p.pairIndex+1)/(1024*P)+2*(3*T+1))
  · rcases hSide with hSide|hSide
    · simpa only [hSide] using s.robust.1
    · simpa only [hSide,compl_compl] using s.robust.2
  · exact hX
  · intro v hv
    have hSafe := (R.colouring.colourGraph i).residueForbidden_safe_partner
      (R.colouring.colourGraph_degree_le_one i) (R.available.internalPart s.part) s.part E h v (mem_sdiff.mp hv).2
    have hMate : (R.colouring.colourGraph i).matchingPartner
        (R.colouring.colourGraph_degree_le_one i) v ∈ A := by
      rcases hSide with hSide|hSide
      · rw [hSide] at hv ⊢
        exact hSafe.2.2.1.mp (mem_sdiff.mp hv).1
      · rw [hSide] at hv ⊢
        exact mem_compl.mpr (fun hm => (mem_compl.mp (mem_sdiff.mp hv).1) (hSafe.2.2.1.mpr hm))
    exact mem_sdiff.mpr ⟨hMate,hSafe.1⟩
  · intro v hv
    exact r.initial_crossing_degree_outside_forbidden C hFirst hSecond i E ha hb h v hv
  · exact hLow
  · exact hHigh

end OverfullWork.NormalizedCanonicalCandidate
