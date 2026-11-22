module

public import OverfullWork.UniformPaperSeedCompletion
public import OverfullWork.ResiduePaletteReserve
public import OverfullWork.ClearedNeighbourAvailability

@[expose] public section


/-! # Pay the small-centre Stage II first-anchor condition for actual states

Construct the residue palette with the full paper Z protected. The
fresh palette fits strictly below Delta. For every later actual partial
state which covers the internal copies and has not changed the selected
Stage II color, all available centre neighbors are still missing that
color. The required positive first-row mass is therefore proved.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 32000000

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.exists_paper_stage_two_anchor_availability
    {R Q : p.completed.PartialColouring r.seedPalette} {h ell n t : ℕ}
    (budget : r.InitialRouteBudget R)
    (run : MultiGraph.PartialColouring.GoodRouteRun s.part s.paperCompletionExceptions h ell R Q n t)
    (hFactors : ∀ i v, (Q.colouring.colourGraph i).degree v=1)
    (hCap : ∀ v, (Q.available.internalPart s.part).degree v ≤ h)
    (hCentre : (Q.available.internalPart s.part).degree p.centre=0)
    (hHalf : p.pairIndex+1 ≤ G.maxDegree)
    (hError : r.seedError ≤ (p.pairIndex+1:ℕ)/100) (hCapSmall : (h:ℝ) ≤ (p.pairIndex+1:ℕ)/32) :
    ∃ q : ℕ, (q:ℝ) < 5*r.seedError ∧
      ∃ C : (Q.available.internalPart s.part).EdgeColoring (q+3*h),
        (∀ i, (C.colourGraph i).edgesWithin s.part=(C.colourGraph i).edgesWithin s.partᶜ) ∧
        r.seedPalette+(q+3*h) < G.maxDegree ∧
        (Q.attach_internal_residue s.part C).CoversInternal s.part ∧
        ∀ S : p.completed.PartialColouring (r.seedPalette+(q+3*h)), ∀ i : Fin (3*h),
          S.CoversInternal s.part →
          S.colouring.colourGraph (Fin.natAdd r.seedPalette (Fin.natAdd q i))=C.colourGraph (Fin.natAdd q i) →
          p.completed.supportGraph.degree p.centre < (p.pairIndex+1)/(64*(2^30*P^3)) →
          0 < S.available.degreeInto
            (S.colouring.missingSet s.partᶜ (Fin.natAdd r.seedPalette (Fin.natAdd q i))) p.centre := by
  obtain ⟨q,hCount,C,hBalance,hStageOne,hStageTwo,hClear,hZero,hOld,hCover⟩ :=
    budget.exists_two_stage_residue_palette_for_set s.paperCompletionExceptions run hFactors hCap hCentre
  have hPalette := r.residue_palette_lt_delta q h hHalf hCount hError hCapSmall
  refine ⟨q,hCount,C,hBalance,hPalette,hCover,?_⟩
  intro S i hInternal hUnchanged hSmall
  apply S.first_anchor_mass_of_cleared_neighbours s.part s.paperCompletionExceptions p.centre
    G.maxDegree (Fin.natAdd r.seedPalette (Fin.natAdd q i)) s.centre_mem p.completion.regular hPalette hInternal
  · exact fun v hv => s.paper_contains_centre_neighbour hSmall v hv
  · intro v hv hvPart
    rw [hUnchanged]
    exact hClear v hv hvPart i

end OverfullWork.NormalizedCanonicalCandidate
