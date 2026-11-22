module

public import OverfullWork.ComplementOccupiedBudget

@[expose] public section


/-! The first and second actual anchors for every unchanged fresh colour.

Stage I uses CMS's zero/one/multiple-large-bundle split. Stage II clears
the complete residual neighbourhood when small. Otherwise the actual
centre-copy budget pays every lost neighbour. No availability oracle is
assumed.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 32000000

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.exists_complete_residue_anchor_conditions
    {R Q : p.completed.PartialColouring r.seedPalette} {h ell n t : ℕ}
    (budget : r.InitialRouteBudget R)
    (run : MultiGraph.PartialColouring.GoodRouteRun s.part (s.completionExceptions ∪ r.anchorClearSet) h ell R Q n t)
    (hFactors : ∀ i v, (Q.colouring.colourGraph i).degree v=1)
    (hCap : ∀ v, (Q.available.internalPart s.part).degree v ≤ h)
    (hCentre : (Q.available.internalPart s.part).degree p.centre=0)
    (hProtected : (Q.available.internalPart s.part).mult s(b,w)=0)
    (hHalf : p.pairIndex+1 ≤ G.maxDegree) (hD : G.maxDegree ≤ 3*(p.pairIndex+1))
    (hP : 8 ≤ P) (hT : 1 ≤ T) (hw : w ∉ s.part) (hbw : b ≠ w)
    (hCentreId : p.centre=(0,false)) (hSecondId : b=(0,true))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hNonheavy : (p.completed.mult s(p.centre,b):ℝ)+FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ) ≤ G.maxDegree)
    (hError : r.seedError ≤ (p.pairIndex+1:ℕ)/100) (hCapSmall : (h:ℝ) ≤ (p.pairIndex+1:ℕ)/32)
    (hErrorRho : r.seedError ≤ FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ)/10000)
    (hCapRho : (h:ℝ) ≤ FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ)/1024)
    (hLoss : ((B+c.setᶜ.card:ℕ):ℝ) ≤ FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ)/10000)
    (hOrder : 100 ≤ FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ))
    (hRatio : 4*((Q.available.internalPart s.part).edgeCount:ℝ) ≤ FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ)*(h:ℝ)/1024)
    (hRow : ∀ v ∈ s.partᶜ, r.count v ≤ Q.graph.mult s(p.centre,v) ∧
      Q.graph.mult s(p.centre,v) ≤ r.count v+Nat.ceil r.seedError)
    (hCross : (Q.graph.crossingSupport s.part).degree b ≤ 1+Nat.ceil (3*r.seedError))
    (hChoice : ∀ v, v ≠ p.centre → v ≠ b →
      FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ)/32 < (p.completed.mult s(p.centre,v):ℝ) →
      (∀ u, u ≠ p.centre → u ≠ b →
        FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ)/32 < (p.completed.mult s(p.centre,u):ℝ) → u=v) → v=w) :
    ∃ q : ℕ, (q:ℝ) < 5*r.seedError ∧
      ∃ C : (Q.available.internalPart s.part).EdgeColoring (q+3*h),
        (∀ i, (C.colourGraph i).edgesWithin s.part=(C.colourGraph i).edgesWithin s.partᶜ) ∧
        r.seedPalette+(q+3*h) < G.maxDegree ∧
        (Q.attach_internal_residue s.part C).CoversInternal s.part ∧
        ∀ S : p.completed.PartialColouring (r.seedPalette+(q+3*h)),
          (∀ e, Q.graph.mult e ≤ S.graph.mult e) → S.CoversInternal s.part →
          ∀ j : Fin (q+3*h),
            S.colouring.colourGraph (Fin.natAdd r.seedPalette j)=C.colourGraph j →
            Nonempty (MultiGraph.PartialColouring.AnchorPrescription S
              (Fin.natAdd r.seedPalette j) s.part p.centre b) := by
  let τ := FirstAnchorScale.rate P ρ
  have hτ : 0 < τ := FirstAnchorScale.rate_pos P hP ρ hρ
  obtain ⟨q,hCount,C,hBalance,hFirst,hSecond,hClear,hZero,hOld,hCover⟩ :=
    budget.exists_two_stage_residue_palette_for_set (s.completionExceptions ∪ r.anchorClearSet) run hFactors hCap hCentre
  have hPalette := r.residue_palette_lt_delta q h hHalf hCount hError hCapSmall
  have hFilled : ∀ v, Q.graph.degree v=r.seedPalette := by
    intro v
    rw [←Q.colouring.sum_colour_degree v]
    simp_rw [hFactors]
    simp
  have hRhoM : 0 ≤ τ*(p.pairIndex+1:ℕ) := by positivity
  have hOccupied := C.occupied_bound_of_two_stage (τ*(p.pairIndex+1:ℕ)) hRhoM hFirst hSecond hRatio
  refine ⟨q,hCount,C,hBalance,hPalette,hCover,?_⟩
  intro S hMono hInternal
  have hMissing : ∀ j, S.colouring.colourGraph (Fin.natAdd r.seedPalette j)=C.colourGraph j →
      ∀ A, S.colouring.missingSet A (Fin.natAdd r.seedPalette j)=C.missingSet A j := by
    intro j hSame A
    ext v
    simp only [MultiGraph.EdgeColoring.missingSet,mem_filter]
    rw [hSame]
  have hSecondReady : ∀ j, S.colouring.colourGraph (Fin.natAdd r.seedPalette j)=C.colourGraph j →
      1 < (S.available.neighboursInto (S.colouring.missingSet s.part (Fin.natAdd r.seedPalette j)) b).card := by
    intro j hSame
    have hOcc : ((s.part\S.colouring.missingSet s.part (Fin.natAdd r.seedPalette j)).card:ℝ) ≤ τ*(p.pairIndex+1:ℕ)/100+2 := by
      rw [hMissing j hSame];exact hOccupied j
    exact r.second_anchor_neighbours_in_fresh_state Q q h S _ τ hτ hMono (hFilled b) hCross
      hNonheavy budget.error_pos.le hErrorRho hCapRho hCount hLoss hOrder hOcc
  have hRowMono := r.centre_row_le_fresh_state Q (q+3*h) S hMono (fun v hv => (hRow v hv).1) hInternal
  have hFirstReady : ∀ j, S.colouring.colourGraph (Fin.natAdd r.seedPalette j)=C.colourGraph j →
      0 < S.available.degreeInto
      (S.colouring.missingSet s.partᶜ (Fin.natAdd r.seedPalette j)) p.centre := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i hSame
      exact r.stage_one_first_anchor_mass Q q h C S i τ hMono (hFilled p.centre) hRow hInternal
        hSame (by rw [←hBalance,hFirst]) hProtected hw hbw hD hT hCentreId hSecondId hCount hErrorRho hCapRho hLoss hNonheavy hChoice
    · intro i hSame
      by_cases hSmall : r.residualCentreNeighbours.card < (p.pairIndex+1)/(32*(2^30*P^3))
      · apply S.first_anchor_mass_of_cleared_available_neighbours s.part r.anchorClearSet p.centre G.maxDegree
          _ s.centre_mem p.completion.regular hPalette hInternal
        · intro v hv
          rw [Candidate.CaseTwoMiddleCopies.anchorClearSet,if_pos hSmall]
          exact r.available_neighbour_in_residual_set S hRowMono hInternal v hv
        · intro v hv hvB
          rw [hSame]
          exact hClear v (mem_union_right _ hv) hvB i
      · have hCut := FirstAnchorScale.cut_large P (p.pairIndex+1) r.residualCentreNeighbours.card hP ρ (by omega)
        have hLossSupport := r.residual_centre_support_loss S hRowMono
        have hOccB : ((s.partᶜ\S.colouring.missingSet s.partᶜ
            (Fin.natAdd r.seedPalette (Fin.natAdd q i))).card:ℝ) ≤ τ*(p.pairIndex+1:ℕ)/100+2 := by
          rw [hMissing _ hSame,C.occupied_compl_eq_of_internal_balance _ (hBalance _)]
          exact hOccupied _
        apply S.first_anchor_mass_of_many_neighbours s.part p.centre _ s.centre_mem
        have hFresh : ((q+3*h:ℕ):ℝ)=(q:ℝ)+3*(h:ℝ) := by push_cast;ring
        rw [hFresh] at hLossSupport
        have hNatReal : ((s.partᶜ\S.colouring.missingSet s.partᶜ
            (Fin.natAdd r.seedPalette (Fin.natAdd q i))).card:ℝ) <
            (S.available.crossingSupport s.part).degree p.centre := by
          change 100*τ*(p.pairIndex+1:ℕ) < (r.residualCentreNeighbours.card:ℝ)+1 at hCut
          linarith
        exact_mod_cast hNatReal
  intro j hSame
  apply S.exists_anchor_prescription _ s.part p.centre b s.centre_mem s.second_not_mem
    (by rw [hSame];exact hZero _) (hFirstReady j hSame)
  exact fun _ => hSecondReady j hSame

end OverfullWork.NormalizedCanonicalCandidate
