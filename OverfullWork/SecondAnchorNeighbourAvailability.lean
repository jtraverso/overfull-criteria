module

public import OverfullWork.CrossingSupportGrowth
public import OverfullWork.PaperStageTwoAnchorAvailability

@[expose] public section


/-! # Pay the second-anchor neighbor reserve in every monotone fresh state

The initial second-anchor crossing degree is retained in the source
interface. Monotone fresh additions cost at most the fresh palette size.
The nonheavy degree profile, partition discrepancy and occupied-vertex
bound then prove two available missing-color neighbors, as in CMS Step 4.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 24000000

theorem bootstrap_eq_missing_neighbours (P : M.PartialColouring k) (A : Finset V) (b : V)
    (hb : b ∉ A) (i : Fin k) :
    P.bootstrapSet A (A\P.colouring.missingSet A i) b=
      P.available.neighboursInto (P.colouring.missingSet A i) b := by
  ext x
  simp only [bootstrapSet,neighboursInto,mem_sdiff,mem_neighborFinset,mem_filter,EdgeColoring.missingSet]
  change ((0 < P.available.mult s(b,x) ∧ ¬(b ∈ A ↔ x ∈ A)) ∧
      ¬(x ∈ A ∧ ¬(x ∈ A ∧ (P.colouring.colourGraph i).degree x=0))) ↔
      ((x ∈ A ∧ (P.colouring.colourGraph i).degree x=0) ∧ 0 < P.available.mult s(b,x))
  tauto

theorem two_missing_neighbours_of_support_budget (P : M.PartialColouring k) (A : Finset V) (b : V)
    (hb : b ∉ A) (i : Fin k) (d ξ : ℝ) (hSupport : d ≤ (M.supportGraph.degree b:ℝ))
    (hDis : |(OverfullWork.PrunedCore.neighboursIn M.supportGraph A b:ℝ)-
      (OverfullWork.PrunedCore.neighboursIn M.supportGraph Aᶜ b:ℝ)| < ξ)
    (hMargin : ξ+2*((A\P.colouring.missingSet A i).card:ℝ)+
      2*((P.graph.crossingSupport A).degree b:ℝ)+2 ≤ d) :
    1 < (P.available.neighboursInto (P.colouring.missingSet A i) b).card := by
  have hh := P.bootstrap_from_support_discrepancy A (A\P.colouring.missingSet A i) b A
    (Or.inr ⟨hb,rfl⟩) d ξ hSupport hDis
  rw [P.bootstrap_eq_missing_neighbours A b hb i] at hh
  have hResult : (1:ℝ) < (P.available.neighboursInto (P.colouring.missingSet A i) b).card := by linarith
  exact_mod_cast hResult

end SimpleGraph.MultiGraph.PartialColouring

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 32000000

theorem Candidate.CaseTwoMiddleCopies.second_anchor_neighbours_in_fresh_state
    (seed : p.completed.PartialColouring r.seedPalette) (q h : ℕ)
    (state : p.completed.PartialColouring (r.seedPalette+(q+3*h)))
    (i : Fin (r.seedPalette+(q+3*h))) (ρ : ℝ) (hρ : 0 < ρ)
    (hMono : ∀ e, seed.graph.mult e ≤ state.graph.mult e) (hFilled : seed.graph.degree b=r.seedPalette)
    (hSeedCross : (seed.graph.crossingSupport s.part).degree b ≤ 1+Nat.ceil (3*r.seedError))
    (hNonheavy : (p.completed.mult s(p.centre,b):ℝ)+ρ*(p.pairIndex+1:ℕ) ≤ G.maxDegree)
    (hError₀ : 0 ≤ r.seedError) (hError : r.seedError ≤ ρ*(p.pairIndex+1:ℕ)/10000)
    (hCap : (h:ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/1024) (hCount : (q:ℝ) < 5*r.seedError)
    (hLoss : ((B+c.setᶜ.card:ℕ):ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/10000)
    (hOrder : 100 ≤ ρ*(p.pairIndex+1:ℕ))
    (hOccupied : ((s.part\state.colouring.missingSet s.part i).card:ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/100+2) :
    1 < (state.available.neighboursInto (state.colouring.missingSet s.part i) b).card := by
  have hb : b ≠ p.centre := by intro he;exact s.second_not_mem (he ▸ s.centre_mem)
  have hProfile := p.completed_neighbour_profile b hb
  have hProfileR : (G.maxDegree:ℝ) ≤ p.completed.supportGraph.degree b+
      (p.completed.mult s(p.centre,b):ℝ)+(B:ℝ) := by exact_mod_cast hProfile
  have hSupport : ρ*(p.pairIndex+1:ℕ)-(B:ℝ) ≤ p.completed.supportGraph.degree b := by linarith
  have hGrowth := seed.crossing_degree_after_fresh_palette state s.part b hMono hFilled
  have hGrowthR : ((state.graph.crossingSupport s.part).degree b:ℝ) ≤
      1+(Nat.ceil (3*r.seedError):ℝ)+(q:ℝ)+3*(h:ℝ) := by
    have hh : (state.graph.crossingSupport s.part).degree b ≤ 1+Nat.ceil (3*r.seedError)+q+3*h := by omega
    exact_mod_cast hh
  have hCeil : (Nat.ceil (3*r.seedError):ℝ) < 3*r.seedError+1 := Nat.ceil_lt_add_one (by positivity)
  have hDeleted : ((state.graph.crossingSupport s.part).degree b:ℝ) ≤ 2+ρ*(p.pairIndex+1:ℕ)/100 := by linarith
  have hB : (B:ℝ) ≤ ρ*(p.pairIndex+1:ℕ)/10000 := by
    have hBY : (B:ℝ) ≤ ((B+c.setᶜ.card:ℕ):ℝ) := by exact_mod_cast Nat.le_add_right B c.setᶜ.card
    exact hBY.trans hLoss
  have hEta : η*(p.pairIndex+1:ℕ) ≤ r.seedError := by
    dsimp only [Candidate.CaseTwoMiddleCopies.seedError]
    have hb₀ : (0:ℝ) ≤ B := Nat.cast_nonneg _
    have ht₀ : (0:ℝ) ≤ T := Nat.cast_nonneg _
    have hdiv₀ : (0:ℝ) ≤ ((p.pairIndex+1)/T:ℕ) := Nat.cast_nonneg _
    linarith
  apply state.two_missing_neighbours_of_support_budget s.part b s.second_not_mem i
    (ρ*(p.pairIndex+1:ℕ)-(B:ℝ)) (η*(p.pairIndex+1:ℕ)) hSupport (s.simple_discrepancy b)
  linarith

end OverfullWork.NormalizedCanonicalCandidate
