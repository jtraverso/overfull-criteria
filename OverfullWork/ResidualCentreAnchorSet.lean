module

public import OverfullWork.CentreResidualSupport

@[expose] public section


/-! A paid protected set of centre neighbours after the middle selection. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 24000000

noncomputable def Candidate.CaseTwoMiddleCopies.residualCentreNeighbours (r : p.CaseTwoMiddleCopies s w) :
    Finset (Fin (p.pairIndex+1) × Bool) :=
  ((p.completed.subtractCopies r.graph).crossingSupport s.part).neighborFinset p.centre

noncomputable def Candidate.CaseTwoMiddleCopies.anchorClearSet (r : p.CaseTwoMiddleCopies s w) :
    Finset (Fin (p.pairIndex+1) × Bool) :=
  if r.residualCentreNeighbours.card < (p.pairIndex+1)/(32*(2^30*P^3))
  then r.residualCentreNeighbours else ∅

theorem Candidate.CaseTwoMiddleCopies.anchorClearSet_card (r : p.CaseTwoMiddleCopies s w) :
    r.anchorClearSet.card ≤ (p.pairIndex+1)/(32*(2^30*P^3)) := by
  dsimp only [Candidate.CaseTwoMiddleCopies.anchorClearSet]
  split_ifs with hh
  · omega
  · simp

theorem Candidate.CaseTwoMiddleCopies.centre_row_le_fresh_state
    (r : p.CaseTwoMiddleCopies s w) (Q : p.completed.PartialColouring r.seedPalette)
    (f : ℕ) (S : p.completed.PartialColouring (r.seedPalette+f))
    (hMono : ∀ e, Q.graph.mult e ≤ S.graph.mult e)
    (hRow : ∀ v ∈ s.partᶜ, r.count v ≤ Q.graph.mult s(p.centre,v))
    (hCover : S.CoversInternal s.part) (v : Fin (p.pairIndex+1) × Bool) :
    r.graph.mult s(p.centre,v) ≤ S.graph.mult s(p.centre,v) := by
  by_cases hv : v ∈ s.part
  · rw [hCover p.centre v (iff_of_true s.centre_mem hv)]
    exact r.graph_le _
  · have hh := MiddleCopyGraph.crossing_mult p.completed s.part p.centre v r.count
      (r.inside_zero _ s.centre_mem) s.centre_mem hv
    change r.graph.mult s(p.centre,v)=r.count v at hh
    rw [hh]
    exact (hRow v (mem_compl.mpr hv)).trans (hMono _)

theorem Candidate.CaseTwoMiddleCopies.available_neighbour_in_residual_set
    (r : p.CaseTwoMiddleCopies s w) {f : ℕ}
    (S : p.completed.PartialColouring (r.seedPalette+f))
    (hRow : ∀ v, r.graph.mult s(p.centre,v) ≤ S.graph.mult s(p.centre,v))
    (hCover : S.CoversInternal s.part) (v : Fin (p.pairIndex+1) × Bool)
    (hCopy : 0 < S.available.mult s(p.centre,v)) : v ∈ r.residualCentreNeighbours := by
  apply (mem_neighborFinset _ _ _).mpr
  have hv : v ∉ s.part := by
    intro hv
    change 0 < p.completed.mult s(p.centre,v)-S.graph.mult s(p.centre,v) at hCopy
    rw [hCover p.centre v (iff_of_true s.centre_mem hv),Nat.sub_self] at hCopy
    omega
  refine ⟨?_,by have ha := s.centre_mem;tauto⟩
  change 0 < p.completed.mult s(p.centre,v)-r.graph.mult s(p.centre,v)
  have hh := hRow v
  change 0 < p.completed.mult s(p.centre,v)-S.graph.mult s(p.centre,v) at hCopy
  omega

theorem Candidate.CaseTwoMiddleCopies.residual_centre_support_loss
    (r : p.CaseTwoMiddleCopies s w) {f : ℕ}
    (S : p.completed.PartialColouring (r.seedPalette+f))
    (hRow : ∀ v, r.graph.mult s(p.centre,v) ≤ S.graph.mult s(p.centre,v)) :
    (r.residualCentreNeighbours.card:ℝ) ≤ (S.available.crossingSupport s.part).degree p.centre+
      2*r.seedError+(f:ℝ) := by
  have hGrowth := MultiGraph.crossing_support_row_growth S.available (p.completed.subtractCopies r.graph)
    s.part p.centre (fun v => by
      change p.completed.mult s(p.centre,v)-S.graph.mult s(p.centre,v) ≤
        p.completed.mult s(p.centre,v)-r.graph.mult s(p.centre,v)
      exact Nat.sub_le_sub_left (hRow v) _)
  have hInitial := MultiGraph.degree_subtract_add p.completed r.graph r.graph_le p.centre
  have hCurrent := S.available_degree p.centre
  have hReg : p.completed.degree p.centre=G.maxDegree := p.completion.regular p.centre
  rw [hReg] at hInitial hCurrent
  have hPalette := S.colouring.degree_le_palette p.centre
  have hCard : r.residualCentreNeighbours.card=
      ((p.completed.subtractCopies r.graph).crossingSupport s.part).degree p.centre := card_neighborFinset_eq_degree _ _
  rw [←hCard] at hGrowth
  have hNat : r.residualCentreNeighbours.card+r.graph.degree p.centre ≤
      (S.available.crossingSupport s.part).degree p.centre+(r.seedPalette+f) := by omega
  have hNatR : (r.residualCentreNeighbours.card:ℝ)+(r.graph.degree p.centre:ℝ) ≤
      ((S.available.crossingSupport s.part).degree p.centre:ℝ)+((r.seedPalette:ℝ)+(f:ℝ)) := by exact_mod_cast hNat
  have hk := r.seed_palette_lt_half_add_error
  have hLower : G.maxDegree ≤ 2*r.graph.degree p.centre+1 := by have hh := r.centre_bounds.1;omega
  have hLowerR : (G.maxDegree:ℝ) ≤ 2*(r.graph.degree p.centre:ℝ)+1 := by exact_mod_cast hLower
  have hBasic := r.seed_error_basics.1
  have hB : (0:ℝ) ≤ B := Nat.cast_nonneg _
  have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
  linarith

end OverfullWork.NormalizedCanonicalCandidate
