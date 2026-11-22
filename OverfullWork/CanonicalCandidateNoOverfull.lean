module

public import OverfullWork.CanonicalOnePairPreservation

@[expose] public section


/-! # Close no-overfullness of the actual small-centre canonical candidate

This closes the previously open positive-q local obligation. It does not
construct a Delta-edge-colouring or eliminate the other terminal branches.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ}
variable {c : Certificate G B K}
set_option maxHeartbeats 8000000

theorem Candidate.ordered_no_overfull (p : Candidate c) :
    ¬p.orderedBase.HasOverfullSubset G.maxDegree :=
  OrderedCanonicalTransport.no_overfull_reindex c.image p.coordinates G.maxDegree p.no_overfull

/-- With the three-vertex reduction already in hand, the local positive
triangle obstruction is impossible under the real certificate budget. -/
theorem Candidate.no_unsafe_independent_centre_triple (p : Candidate c)
    (hMin : ∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x)
    (hScale : 3*B≤2*G.maxDegree)
    (S : Finset (Fin (p.pairIndex+1)×Bool)) (hS : S.card=3) (hz : p.centre∈S)
    (hBase : p.orderedBase.twiceInternal S=0) : G.maxDegree≤p.completed.cutSize S := by
  by_contra hn
  have hCut:p.completed.cutSize S<G.maxDegree:=Nat.lt_of_not_ge hn
  have hk:=p.prefix_one_of_unsafe_independent_triple hMin hScale S hS hz hBase hCut
  have hOrderSize:S.card≤2*(p.pairIndex+1):=by
    have hh:=card_le_univ S
    simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm] using hh
  have hkm:p.completion.k<p.pairIndex+1:=by omega
  have hOrder:p.orderedBase.degree p.completion.lastTrue≤
      p.orderedBase.degree (p.completion.middleVertex hkm):=by
    apply p.ordered_pair_mono
    change p.completion.k-1<p.completion.k
    have hh:=p.completion.positive
    omega
  have hSet:=p.completion.unsafe_independent_triple_eq_triangle hkm p.ordered_degree_le
    hOrder S hS hBase hCut
  have hSafe:=p.completion.triangle_safe_of_prefix_one hkm hk p.ordered_degree_le p.ordered_no_overfull
  change G.maxDegree≤p.completed.cutSize (p.completion.triangle hkm) at hSafe
  rw [←hSet] at hSafe
  omega

/-- No restriction on q, no extra centre-mass assumption, and no assumed
no-overfullness of the completion. The source minimum inequality is the
small-centre branch condition already used by exists_candidate. -/
theorem above_half_small_centre_completion_no_overfull (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),N≤Fintype.card V →
      Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*Q^2))+6 → K≤Fintype.card V/(4096*Q^2)+1 →
      (∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) →
      ¬p.completed.HasOverfullSubset G.maxDegree := by
  obtain ⟨Q,hQ,N₀,hN₀⟩:=above_half_critical_completion_overfull_witness.{u} ε hε
  refine ⟨Q,hQ,max N₀ 32,?_⟩
  intro V _ _ G _ B K c p hn hc hdense hB hK hMin hOF
  obtain ⟨⟨S,hS,hz,hCut,hBase,hNPositive⟩,hMass⟩:=hN₀ G c p (by omega) hc hdense hB hK hMin hOF
  have hWeak:Fintype.card V≤2*G.maxDegree:=by
    have hMul:0≤ε*(Fintype.card V:ℝ):=by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,hMul])
  have hScale:=CanonicalResidualFirstPair.budget_scale Q (Fintype.card V) G.maxDegree B
    hQ (by omega) hWeak hB
  have hSafe:=p.no_unsafe_independent_centre_triple hMin hScale S hS hz hBase
  omega

end OverfullWork.NormalizedCanonicalCandidate
