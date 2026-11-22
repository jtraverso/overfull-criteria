module

public import OverfullWork.UniformProtectedSeedCompletion
public import OverfullWork.CanonicalPaperCentreSet

@[expose] public section


/-! # Uniform actual seed completion with the paper's full small-centre Z

Instantiate the added-set construction with the complete simple
neighbourhood in the small-degree branch. Its cardinality is proved
from the chosen cutoff, not assumed on the resulting source graph.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
set_option maxHeartbeats 32000000

theorem exists_uniform_paper_case_two_seed_completion (P : ℕ) (hP : 8 ≤ P) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ell : ℕ, ∃ δ : ℝ, ∃ Qs : ℕ, 0 < δ ∧ P ≤ Qs ∧
      ∀ T : ℕ, 16 ≤ T → 4 ≤ δ*(T:ℝ) → ∀ η : ℝ, 0 ≤ η → η ≤ min (δ/4) (1/32) →
        ∃ N : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
          (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
          (c : Certificate G B K) (p : Candidate c),
          N ≤ Fintype.card W → Fintype.card W ≤ 2*G.maxDegree →
          B ≤ 6*(Fintype.card W/(4096*Qs^2))+6 → K ≤ Fintype.card W/(4096*Qs^2)+1 →
          p.centre=(0,false) → ∀ b : Fin (p.pairIndex+1) × Bool, b=(0,true) →
          ∀ s : p.CaseTwoPartition P T η b, ∀ w, w ∉ s.part → b ≠ w →
          ∀ r : p.CaseTwoMiddleCopies s w,
            (p.completed.mult s(p.centre,b):ℝ)+ρ*(p.pairIndex+1:ℕ) ≤ G.maxDegree →
            ∃ R Q : p.completed.PartialColouring r.seedPalette, ∃ h n t : ℕ,
              r.InitialRouteBudget R ∧
              MultiGraph.PartialColouring.GoodRouteRun s.part s.paperCompletionExceptions h ell R Q n t ∧
              (∀ i v, (Q.colouring.colourGraph i).degree v=1) ∧
              (∀ v, (Q.available.internalPart s.part).degree v ≤ h) ∧
              (h:ℝ) ≤ (p.pairIndex+1:ℕ)/32 ∧ r.seedError ≤ (p.pairIndex+1:ℕ)/100 ∧
              (h:ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/1024 ∧ r.seedError ≤ ρ*(p.pairIndex+1:ℕ)/10000 ∧
              ((B+c.setᶜ.card:ℕ):ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/10000 ∧
              100 ≤ ρ*(p.pairIndex+1:ℕ) ∧
              4*((Q.available.internalPart s.part).edgeCount:ℝ) ≤ ρ*(p.pairIndex+1:ℕ)*(h:ℝ)/1024 ∧
              (∀ v ∈ s.partᶜ, r.count v ≤ Q.graph.mult s(p.centre,v) ∧
                Q.graph.mult s(p.centre,v) ≤ r.count v+Nat.ceil r.seedError) ∧
              (Q.graph.crossingSupport s.part).degree b ≤ 1+Nat.ceil (3*r.seedError) ∧
              (∀ v, v ≠ p.centre → v ≠ b →
                (Q.graph.crossingSupport s.part).degree v ≤ 2+Nat.ceil (6*r.seedError)+h) ∧
              (Q.available.internalPart s.part).degree p.centre=0 ∧
              (Q.available.internalPart s.part).mult s(b,w)=0 ∧
              ((Q.available.internalPart s.part).edgeCount:ℝ) <
                r.seedError*(5+(ell:ℝ)*(p.pairIndex+2:ℕ)) ∧
              Nonempty { sc : AdditionalProtectedCompletionScalars P T (p.pairIndex+1) r.seedError (ρ/128) ell (p.paperCentreSet P).card // sc.h=h } ∧
              ∀ v ∈ s.paperCompletionExceptions,
                (Q.available.internalPart s.part).degree v=(R.available.internalPart s.part).degree v := by
  obtain ⟨ell,δ,Qs,hδ,hPQ,hUniform⟩ := exists_uniform_case_two_seed_completion_with_protected_set P hP ρ hρ
  refine ⟨ell,δ,Qs,hδ,hPQ,?_⟩
  intro T hT hTδ η hη₀ hη
  obtain ⟨N,hN⟩ := hUniform T hT hTδ η hη₀ hη
  refine ⟨N,?_⟩
  intro W _ _ G _ B K c p hn hWeak hB hK hCentre b hSecond s w hw hbw r hNonheavy
  exact hN G c p hn hWeak hB hK hCentre b hSecond s w hw hbw r (p.paperCentreSet P)
    (p.paperCentreSet_card P hP) hNonheavy

end OverfullWork.NormalizedCanonicalCandidate
