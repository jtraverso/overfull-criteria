module

public import OverfullWork.AboveHalfCompletionTripleCriterion
public import OverfullWork.CanonicalTripleAddition

@[expose] public section


/-! # Residual critical triples are independent in the base and use N

The source minimum inequality is the very small-centre branch condition
used by exists_candidate. It was not recorded as a Candidate field, so it
is transported explicitly here, rather than inferred from arbitrary candidates.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ}
variable {c : Certificate G B K}
set_option maxHeartbeats 6000000

theorem Candidate.centre_min_of_source_min (p : Candidate c)
    (hMin : ∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) :
    ∀v,p.orderedBase.degree p.centre≤p.orderedBase.degree v := by
  intro v
  rw [p.centre_degree]
  simp only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex]
  cases hv:p.coordinates v with
  | none => rw [Certificate.image,degree_none]
  | some w =>
    rw [Certificate.image,degree_some]
    exact hMin w.val (by have hh:=w.property;simpa only [mem_compl,not_not] using hh)

theorem Candidate.critical_centre_balanced (p : Candidate c) (hc : Overfull.IsDeltaCritical G) :
    ∀v,2*p.orderedBase.mult s(p.centre,v)≤p.orderedBase.degree p.centre := by
  intro v
  change 2*c.image.mult s(p.coordinates p.centre,p.coordinates v)≤_
  have hCoord:p.coordinates p.centre=none:=p.coordinates.apply_symm_apply none
  rw [hCoord,p.centre_degree]
  cases hv:p.coordinates v with
  | none => rw [c.image.loopless _ (by simp)];omega
  | some w =>
    have hh:=centre_bundle_balanced G hc c.setᶜ (by simpa using c.independent) w
    simpa only [Certificate.image,degree_none] using hh

theorem Candidate.critical_edge_degree_sum (p : Candidate c) (hc : Overfull.IsDeltaCritical G) :
    ∀a b,0<p.orderedBase.mult s(a,b) →
      G.maxDegree+2≤p.orderedBase.degree a+p.orderedBase.degree b := by
  intro a b hEdge
  simp only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex]
  exact image_edge_degree_sum G hc c.setᶜ (by simpa using c.independent)
    (p.coordinates a) (p.coordinates b) hEdge

theorem Candidate.unsafe_triple_base_independent (p : Candidate c)
    (hc : Overfull.IsDeltaCritical G)
    (hMin : ∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x)
    (hScale : 8*c.setᶜ.card≤G.maxDegree+2)
    (S : Finset (Fin (p.pairIndex+1)×Bool)) (hS : S.card=3) (hz : p.centre∈S)
    (hCut : p.completed.cutSize S<G.maxDegree) : p.orderedBase.twiceInternal S=0 := by
  by_contra hn
  have hBase:=CriticalCentreTriples.cut_of_internal_positive p.orderedBase G.maxDegree
    c.setᶜ.card p.centre p.ordered_star p.centre_multiplicity
    (p.centre_min_of_source_min hMin) (p.critical_centre_balanced hc)
    (p.critical_edge_degree_sum hc) hScale S hS hz (by omega)
  have hMono:=StarBudgetOddCuts.cut_mono p.orderedBase p.completed (by
    intro e
    change p.orderedBase.mult e≤p.orderedBase.mult e+p.completion.L.mult e+p.completion.N.mult e
    omega) S
  omega

end OverfullWork.NormalizedCanonicalCandidate

namespace OverfullWork.CriticalCanonicalTripleScales
set_option maxHeartbeats 6000000

theorem complement_scale (Q n Δ Y : ℕ) (hQ : 2≤Q) (hn : 32≤n) (hΔ : n≤2*Δ)
    (hY : Y≤n/(4096*Q^2)+1) : 8*Y≤Δ+2 := by
  have hCoeff:64≤4096*Q^2:=by nlinarith only [hQ]
  have hh:64*(n/(4096*Q^2))≤n:=
    (Nat.mul_le_mul_right (n/(4096*Q^2)) hCoeff).trans (Nat.mul_div_le n (4096*Q^2))
  omega

end OverfullWork.CriticalCanonicalTripleScales

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u

/-- The remaining actual overfull witness uses an independent base
triple and a positive edge contribution from the explicit canonical N. -/
theorem above_half_critical_completion_overfull_witness (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),N≤Fintype.card V →
      Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*Q^2))+6 → K≤Fintype.card V/(4096*Q^2)+1 →
      (∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) →
      p.completed.HasOverfullSubset G.maxDegree →
      (∃S : Finset (Fin (p.pairIndex+1)×Bool),S.card=3 ∧ p.centre∈S ∧
        p.completed.cutSize S<G.maxDegree ∧ p.orderedBase.twiceInternal S=0 ∧
        0<p.completion.N.twiceInternal S) ∧
      2*(∑y∈c.setᶜ,G.degree y)<B+4*c.setᶜ.card+6 := by
  obtain ⟨Q,hQ,N₀,hN₀⟩:=above_half_completion_overfull_witness.{u} ε hε
  refine ⟨Q,hQ,max N₀ 32,?_⟩
  intro V _ _ G _ B K c p hn hc hdense hB hK hMin hOF
  obtain ⟨⟨S,hS,hz,hCut⟩,hMass⟩:=hN₀ G c p (by omega) hdense hB hK hOF
  have hWeak:Fintype.card V≤2*G.maxDegree:=by
    have hMul:0≤ε*(Fintype.card V:ℝ):=by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,hMul])
  have hScale:=CriticalCanonicalTripleScales.complement_scale Q (Fintype.card V)
    G.maxDegree c.setᶜ.card hQ (by omega) hWeak (c.complement_small.trans hK)
  have hBase:=p.unsafe_triple_base_independent hc hMin hScale S hS hz hCut
  exact ⟨⟨S,hS,hz,hCut,hBase,
    p.completion.N_internal_positive_of_unsafe_triple S hS hBase hCut⟩,hMass⟩

end OverfullWork.NormalizedCanonicalCandidate
