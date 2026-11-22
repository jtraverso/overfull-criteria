module

public import OverfullWork.ResidueOccupiedVertexBudget

@[expose] public section


/-! # Actual paper-aligned residue anchor conditions throughout monotone extension

Construct one residue palette. Derive the occupied-set budget for all
its unchanged colors and pay the second-anchor inequality in every
monotone actual fresh state. For small-centre Stage II, construct the
actual prescribed matching with neither availability inequality assumed.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 32000000

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.exists_paper_residue_anchor_conditions
    {R Q : p.completed.PartialColouring r.seedPalette} {h ell n t : ℕ}
    (budget : r.InitialRouteBudget R)
    (run : MultiGraph.PartialColouring.GoodRouteRun s.part s.paperCompletionExceptions h ell R Q n t)
    (hFactors : ∀ i v, (Q.colouring.colourGraph i).degree v=1)
    (hCap : ∀ v, (Q.available.internalPart s.part).degree v ≤ h)
    (hCentre : (Q.available.internalPart s.part).degree p.centre=0) (hHalf : p.pairIndex+1 ≤ G.maxDegree)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hNonheavy : (p.completed.mult s(p.centre,b):ℝ)+ρ*(p.pairIndex+1:ℕ) ≤ G.maxDegree)
    (hError : r.seedError ≤ (p.pairIndex+1:ℕ)/100) (hCapSmall : (h:ℝ) ≤ (p.pairIndex+1:ℕ)/32)
    (hErrorRho : r.seedError ≤ ρ*(p.pairIndex+1:ℕ)/10000) (hCapRho : (h:ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/1024)
    (hLoss : ((B+c.setᶜ.card:ℕ):ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/10000) (hOrder : 100 ≤ ρ*(p.pairIndex+1:ℕ))
    (hRatio : 4*((Q.available.internalPart s.part).edgeCount:ℝ) ≤ ρ*(p.pairIndex+1:ℕ)*(h:ℝ)/1024)
    (hCross : (Q.graph.crossingSupport s.part).degree b ≤ 1+Nat.ceil (3*r.seedError)) :
    ∃ q : ℕ, (q:ℝ) < 5*r.seedError ∧
      ∃ C : (Q.available.internalPart s.part).EdgeColoring (q+3*h),
        (∀ i, (C.colourGraph i).edgesWithin s.part=(C.colourGraph i).edgesWithin s.partᶜ) ∧
        r.seedPalette+(q+3*h) < G.maxDegree ∧
        (Q.attach_internal_residue s.part C).CoversInternal s.part ∧
        ∀ S : p.completed.PartialColouring (r.seedPalette+(q+3*h)),
          (∀ e, Q.graph.mult e ≤ S.graph.mult e) →
          (∀ j : Fin (q+3*h), S.colouring.colourGraph (Fin.natAdd r.seedPalette j)=C.colourGraph j →
            1 < (S.available.neighboursInto (S.colouring.missingSet s.part (Fin.natAdd r.seedPalette j)) b).card) ∧
          (∀ i : Fin (3*h), S.CoversInternal s.part →
            S.colouring.colourGraph (Fin.natAdd r.seedPalette (Fin.natAdd q i))=C.colourGraph (Fin.natAdd q i) →
            p.completed.supportGraph.degree p.centre < (p.pairIndex+1)/(64*(2^30*P^3)) →
            Nonempty (MultiGraph.PartialColouring.AnchorPrescription S
              (Fin.natAdd r.seedPalette (Fin.natAdd q i)) s.part p.centre b)) := by
  obtain ⟨q,hCount,C,hBalance,hFirst,hSecond,hClear,hZero,hOld,hCover⟩ :=
    budget.exists_two_stage_residue_palette_for_set s.paperCompletionExceptions run hFactors hCap hCentre
  have hPalette := r.residue_palette_lt_delta q h hHalf hCount hError hCapSmall
  have hFilled : Q.graph.degree b=r.seedPalette := by
    rw [←Q.colouring.sum_colour_degree b]
    simp_rw [hFactors]
    simp
  have hRhoM : 0 ≤ ρ*(p.pairIndex+1:ℕ) := by positivity
  have hOccupied := C.occupied_bound_of_two_stage (ρ*(p.pairIndex+1:ℕ)) hRhoM hFirst hSecond hRatio
  refine ⟨q,hCount,C,hBalance,hPalette,hCover,?_⟩
  intro S hMono
  have hSecondReady : ∀ j : Fin (q+3*h),
      S.colouring.colourGraph (Fin.natAdd r.seedPalette j)=C.colourGraph j →
      1 < (S.available.neighboursInto (S.colouring.missingSet s.part (Fin.natAdd r.seedPalette j)) b).card := by
    intro j hSame
    have hMissing : S.colouring.missingSet s.part (Fin.natAdd r.seedPalette j)=C.missingSet s.part j := by
      ext v
      simp only [MultiGraph.EdgeColoring.missingSet,mem_filter]
      rw [hSame]
    have hOcc : ((s.part\S.colouring.missingSet s.part (Fin.natAdd r.seedPalette j)).card:ℝ) ≤
        ρ*(p.pairIndex+1:ℕ)/100+2 := by rw [hMissing];exact hOccupied j
    exact r.second_anchor_neighbours_in_fresh_state Q q h S _ ρ hρ hMono hFilled hCross hNonheavy
      budget.error_pos.le hErrorRho hCapRho hCount hLoss hOrder hOcc
  refine ⟨hSecondReady,?_⟩
  intro i hInternal hSame hSmall
  have hFirstReady : 0 < S.available.degreeInto
      (S.colouring.missingSet s.partᶜ (Fin.natAdd r.seedPalette (Fin.natAdd q i))) p.centre := by
    apply S.first_anchor_mass_of_cleared_neighbours s.part s.paperCompletionExceptions p.centre
      G.maxDegree _ s.centre_mem p.completion.regular hPalette hInternal
    · exact fun v hv => s.paper_contains_centre_neighbour hSmall v hv
    · intro v hv hvPart
      rw [hSame]
      exact hClear v hv hvPart i
  apply S.exists_anchor_prescription _ s.part p.centre b s.centre_mem s.second_not_mem
    (by rw [hSame];exact hZero _) hFirstReady
  exact fun _ => hSecondReady (Fin.natAdd q i) hSame

end OverfullWork.NormalizedCanonicalCandidate
