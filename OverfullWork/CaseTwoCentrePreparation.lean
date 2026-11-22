module

public import OverfullWork.CaseTwoPerColourMissing
public import OverfullWork.PriorityMCCPairing
public import OverfullWork.CentreSaturation

@[expose] public section


/-! # Actual seed-to-centre preparation, preserving the missing budgets

The ambient partial coloring is built from the constructed J. A finite
copy-exchange run saturates its centre; total colored size and each
color's coverage do not decrease. MCC pairs are reconstructed for the
resulting coloring. Saturation of the second anchor and preservation of
the paper's protected-triangle invariant are not asserted here.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 12000000

noncomputable def Candidate.CaseTwoMiddleCopies.partialSeed (r : p.CaseTwoMiddleCopies s w)
    (C : r.graph.EdgeColoring r.seedPalette) : p.completed.PartialColouring r.seedPalette :=
  ⟨r.graph,C,r.graph_le⟩

theorem Candidate.CaseTwoMiddleCopies.exists_centre_prepared_state
    (r : p.CaseTwoMiddleCopies s w) (hw : w ∉ s.part)
    (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T)
    (hHalf : p.pairIndex+1 ≤ G.maxDegree)
    (C : r.graph.EdgeColoring r.seedPalette) (hC : C.IsEquitable) (hPalette : r.seedPalette ≤ G.maxDegree) :
    ∃ Q : p.completed.PartialColouring r.seedPalette, ∃ t : ℕ,
      MultiGraph.PartialColouring.CentreRun p.centre (r.partialSeed C) Q (C.missingPalette p.centre).card t ∧
      t ≤ (C.missingPalette p.centre).card ∧
      (∀ i, (Q.colouring.colourGraph i).degree p.centre=1) ∧
      r.graph.edgeCount ≤ Q.graph.edgeCount ∧
      (∀ v, ((Q.colouring.missingPalette v).card:ℝ) <
        2*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)) ∧
      ∃ D : PriorityMCCPairing.Family Q.colouring s.part, ∀ i,
        ((Q.colouring.missingSet univ i).card:ℝ) ≤
          4*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+2 := by
  let P₀ := r.partialSeed C
  have hk : r.seedPalette ≤ p.completed.degree p.centre := by
    have hreg : p.completed.degree p.centre=G.maxDegree := p.completion.regular p.centre
    rwa [hreg]
  obtain ⟨Q,t,hRun,ht,hSat,hSize⟩ := MultiGraph.PartialColouring.exists_centre_saturated_run p.centre hk P₀
  have htR : (t:ℝ) ≤ (C.missingPalette p.centre).card := by exact_mod_cast ht
  have hCentre := r.seed_missing_bound hw hD hT C p.centre
  have hV : Even (Fintype.card (Fin (p.pairIndex+1) × Bool)) := by
    refine ⟨p.pairIndex+1,?_⟩
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  obtain ⟨D⟩ := PriorityMCCPairing.exists_family Q.colouring s.part hV
  refine ⟨Q,t,hRun,ht,hSat,hSize,?_,D,?_⟩
  · intro v
    have hh := hRun.missingPalette_growth_le v
    have hhR : ((Q.colouring.missingPalette v).card:ℝ) ≤ (C.missingPalette v).card+(t:ℝ) := by
      exact_mod_cast hh
    have hOld := r.seed_missing_bound hw hD hT C v
    linarith
  · intro i
    have hh := hRun.missingSet_mono i
    have hhR : ((Q.colouring.missingSet univ i).card:ℝ) ≤ (C.missingSet univ i).card := by
      exact_mod_cast hh
    exact hhR.trans (r.seed_per_colour_missing hw hD hT hHalf C hC i)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_uniform_case_two_mcc_seed (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 8 ≤ P ∧ ∃ Q : ℕ, P ≤ Q ∧ ∀ T : ℕ, 16 ≤ T →
      ∀ η : ℝ, 0 < η → η ≤ 1/16 → ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
          ∃ s : p.CaseTwoPartition P T η b,
            ∀ w, w ∉ s.part → b ≠ w → ∃ r : p.CaseTwoMiddleCopies s w,
              ∃ C : r.graph.EdgeColoring r.seedPalette,
                C.IsEquitable ∧ r.seedPalette < G.maxDegree ∧
                ∃ D : PriorityMCCPairing.Family C s.part, ∀ i,
                  ((C.missingSet univ i).card:ℝ) ≤
                    4*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+2 := by
  obtain ⟨P,hP,Q,hPQ,hConstruct⟩ := exists_uniform_case_two_proper_seed.{u} ε hε
  refine ⟨P,hP,Q,hPQ,?_⟩
  intro T hT η hη hηsmall
  obtain ⟨N₀,hN₀⟩ := hConstruct T hT η hη hηsmall
  refine ⟨max N₀ (64*Q),?_⟩
  intro W _ _ G _ B K c p hn hcrit hdense hB hK hMin b hab
  obtain ⟨s,hs⟩ := hN₀ G c p (by omega) hcrit hdense hB hK hMin b hab
  have hD := p.maxDegree_lt_image_order_at_source_scale Q (by omega) (by omega) hB hK
  have hWeak : Fintype.card W ≤ 2*G.maxDegree := by
    have he : 0 ≤ ε*(Fintype.card W:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card W:ℝ) ≤ 2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hHalf := p.image_half_order_le_delta hWeak
  have hV : Even (Fintype.card (Fin (p.pairIndex+1) × Bool)) := by
    refine ⟨p.pairIndex+1,?_⟩
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  refine ⟨s,?_⟩
  intro w hw hbw
  obtain ⟨r,C,hC,hPalette,_⟩ := hs w hw hbw
  obtain ⟨D⟩ := PriorityMCCPairing.exists_family C s.part hV
  exact ⟨r,C,hC,hPalette,D,fun i => r.seed_per_colour_missing hw (by omega) (by omega) hHalf C hC i⟩

end OverfullWork.NormalizedCanonicalCandidate
