module

public import OverfullWork.CaseTwoCentrePreparation
public import OverfullWork.ProtectedCentreRun

@[expose] public section


/-! # Protected first-centre stage for the actual Case 2 seed

This endpoint applies the protected run to the constructed middle-copy
graph, rather than postulating a compatible partial coloring. It pays
the extra erasures in the vertex and per-color missing budgets. The
second anchor and the later alternating paths are separate obligations.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 16000000

theorem Candidate.CaseTwoMiddleCopies.exists_protected_centre_prepared_state
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part) (hbw : b ≠ w)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T)
    (hHalf : p.pairIndex+1 ≤ G.maxDegree)
    (C : r.graph.EdgeColoring r.seedPalette) (hC : C.IsEquitable)
    (hPalette : r.seedPalette ≤ G.maxDegree) :
    ∃ Q : p.completed.PartialColouring r.seedPalette, ∃ t : ℕ,
      MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q
        (C.missingPalette p.centre).card t ∧
      t ≤ 2*(C.missingPalette p.centre).card ∧
      (∀ i, (Q.colouring.colourGraph i).degree p.centre=1) ∧
      Q.graph.mult s(b,w)=r.graph.mult s(b,w) ∧
      Q.graph.edgesWithin {p.centre,b,w} ≤ Q.graph.degree p.centre ∧
      Q.graph.edgeCount+t=r.graph.edgeCount+(C.missingPalette p.centre).card ∧
      (∀ v, ((Q.colouring.missingPalette v).card:ℝ) <
        3*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)) ∧
      ∃ D : PriorityMCCPairing.Family Q.colouring s.part, ∀ i,
        ((Q.colouring.missingSet univ i).card:ℝ) ≤
          6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+2 := by
  let P₀ := r.partialSeed C
  have hab : p.centre ≠ b := by intro he;exact s.second_not_mem (he ▸ s.centre_mem)
  have haw : p.centre ≠ w := by intro he;exact hw (he ▸ s.centre_mem)
  have hk : r.seedPalette ≤ p.completed.degree p.centre := by
    have hreg : p.completed.degree p.centre=G.maxDegree := p.completion.regular p.centre
    rwa [hreg]
  obtain ⟨Q,t,hRun,ht,hSat,hBundle,hTri⟩ :=
    MultiGraph.PartialColouring.exists_protected_centre_saturated_run
      p.centre b w hab haw hbw hk P₀ (r.protected_triangle hw hbw)
  have htR : (t:ℝ) ≤ 2*(C.missingPalette p.centre).card := by exact_mod_cast ht
  have hCentre := r.seed_missing_bound hw hD hT C p.centre
  have hV : Even (Fintype.card (Fin (p.pairIndex+1) × Bool)) := by
    refine ⟨p.pairIndex+1,?_⟩
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  obtain ⟨D⟩ := PriorityMCCPairing.exists_family Q.colouring s.part hV
  refine ⟨Q,t,hRun,ht,hSat,hBundle,hTri,hRun.edgeCount_balance,?_,D,?_⟩
  · intro v
    have hh := hRun.missingPalette_growth_le v
    have hhR : ((Q.colouring.missingPalette v).card:ℝ) ≤ (C.missingPalette v).card+(t:ℝ) := by
      exact_mod_cast hh
    have hOld := r.seed_missing_bound hw hD hT C v
    linarith
  · intro i
    have hh := hRun.missingSet_growth_le i
    have hhR : ((Q.colouring.missingSet univ i).card:ℝ) ≤
        (C.missingSet univ i).card+2*(C.missingPalette p.centre).card := by exact_mod_cast hh
    have hOld := r.seed_per_colour_missing hw hD hT hHalf C hC i
    linarith

end OverfullWork.NormalizedCanonicalCandidate
