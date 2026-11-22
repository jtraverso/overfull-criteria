module

public import OverfullWork.WeakVALIdentificationEdges
public import OverfullWork.CanonicalCandidateNoOverfull

@[expose] public section


/-! The actual canonical completion is no-overfull under weak VAL.
Criticality is replaced by precisely the local inequalities it supplied. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ}
variable {c : Certificate G B K}
set_option maxHeartbeats 12000000

theorem Candidate.weak_val_centre_balanced (p : Candidate c) (hWeak : ∀ u v, G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) :
    ∀v,2*p.orderedBase.mult s(p.centre,v)≤p.orderedBase.degree p.centre := by
  intro v
  change 2*c.image.mult s(p.coordinates p.centre,p.coordinates v)≤_
  have hCoord:p.coordinates p.centre=none:=p.coordinates.apply_symm_apply none
  rw [hCoord,p.centre_degree]
  cases hv:p.coordinates v with
  | none => rw [c.image.loopless _ (by simp)];omega
  | some w =>
    have hh:=centre_bundle_balanced_of_weak_val G hWeak c.setᶜ (by simpa using c.independent) w
    simpa only [Certificate.image,degree_none] using hh

theorem Candidate.weak_val_edge_degree_sum (p : Candidate c) (hWeak : ∀ u v, G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) :
    ∀a b,0<p.orderedBase.mult s(a,b) →
      G.maxDegree+2≤p.orderedBase.degree a+p.orderedBase.degree b := by
  intro a b hEdge
  simp only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex]
  exact image_edge_degree_sum_of_weak_val G hWeak c.setᶜ (by simpa using c.independent)
    (p.coordinates a) (p.coordinates b) hEdge

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem above_half_weak_val_completion_no_overfull (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*Q^2))+6 → K ≤ Fintype.card W/(4096*Q^2)+1 →
        (∀ u v, G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) →
        (∀ x ∈ c.set, (∑ y ∈ c.setᶜ, G.degree y) ≤ G.degree x) →
        ¬p.completed.HasOverfullSubset G.maxDegree := by
  obtain ⟨Q,hQ,N₀,hTriples⟩ := above_half_completion_no_overfull_iff_triples.{u} ε hε
  refine ⟨Q,hQ,max N₀ 32,?_⟩
  intro W _ _ G _ B K c p hn hDense hB hK hWeak hMin
  obtain ⟨hIff,_⟩ := hTriples G c p (by omega) hDense hB hK
  have hOrder : Fintype.card W ≤ 2*G.maxDegree := by
    have hMul : (0:ℝ) ≤ ε*(Fintype.card W:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card W:ℝ) ≤ 2*(G.maxDegree:ℝ) by nlinarith only [hDense,hMul])
  have hScale := CriticalCanonicalTripleScales.complement_scale Q (Fintype.card W)
    G.maxDegree c.setᶜ.card hQ (by omega) hOrder (c.complement_small.trans hK)
  have hBudgetScale := CanonicalResidualFirstPair.budget_scale Q (Fintype.card W)
    G.maxDegree B hQ (by omega) hOrder hB
  apply hIff.mpr
  intro S hS hz
  by_cases hZero : p.orderedBase.twiceInternal S=0
  · exact p.no_unsafe_independent_centre_triple hMin hBudgetScale S hS hz hZero
  · have hBase := CriticalCentreTriples.cut_of_internal_positive p.orderedBase G.maxDegree
      c.setᶜ.card p.centre p.ordered_star p.centre_multiplicity
      (p.centre_min_of_source_min hMin) (p.weak_val_centre_balanced hWeak)
      (p.weak_val_edge_degree_sum hWeak) hScale S hS hz (by omega)
    apply hBase.trans (StarBudgetOddCuts.cut_mono p.orderedBase p.completed ?_ S)
    intro e
    change p.orderedBase.mult e ≤ p.orderedBase.mult e+p.completion.L.mult e+p.completion.N.mult e
    omega

end OverfullWork.NormalizedCanonicalCandidate
