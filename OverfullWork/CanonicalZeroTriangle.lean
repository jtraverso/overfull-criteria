module

public import OverfullWork.CriticalCanonicalTripleWitness

@[expose] public section


/-! # Close the canonical zero-triangle branch

If the canonical triangle weight q is zero, L+N is bipartite: flip the
prefix true endpoints, whose L degrees are zero. Thus an independent
base triple cannot become overfull. This is an actual construction from
Completion fields, not an assumed colouring or bipartition.
-/
namespace OverfullWork.CanonicalZeroTriangle
open SimpleGraph Finset CanonicalPairTriangle CanonicalRegularization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem mult_le_degree (M : MultiGraph V) (v w : V) : M.mult s(v,w)≤M.degree v := by
  rw [M.degree_eq_sum_mult]
  exact single_le_sum (f:=fun x=>M.mult s(v,x)) (fun _ _=>Nat.zero_le _) (mem_univ w)

omit [Fintype V] in
theorem weightedPairs_support {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k→ℕ)
    (u v : V) (hEdge : 0<(weightedPairs e r).mult s(u,v)) :
    ∃i : Fin k,s(u,v)=s(e (i,false),e (i,true)) := by
  by_contra hn
  have hZero:(weightedPairs e r).mult s(u,v)=0:=by
    change (∑i : Fin k,(copiesOn (e (i,false)) (e (i,true)) _ (r i)).mult s(u,v))=0
    apply sum_eq_zero
    intro i hi
    have hh:s(u,v)≠s(e (i,false),e (i,true)):=fun he=>hn ⟨i,he⟩
    simp only [copiesOn,scaledCopies,MultiGraph.unitEdge,if_neg hh,Nat.mul_zero]
  omega

omit [Fintype V] in
theorem pairTriangle_zero {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k→ℕ)
    (j : Fin k) (w : V) (hw : ∀z,w≠e z) :
    pairTriangle e r j w hw 0=weightedPairs e r := by
  apply MultiGraph.ext_mult
  intro a
  simp only [pairTriangle,MultiGraph.addCopies,copiesOn,scaledCopies,Nat.zero_mul,
    Nat.add_zero,ite_self,Nat.sub_zero]

end OverfullWork.CanonicalZeroTriangle

namespace OverfullWork.CanonicalRegularization
open SimpleGraph Finset CanonicalPairTriangle CanonicalTripleAddition CanonicalZeroTriangle
open scoped Classical
variable {m Δ : ℕ} {D : MultiGraph (Fin m×Bool)}
set_option maxHeartbeats 6000000

theorem Completion.N_eq_weightedPairs_of_q_zero (C : Completion D Δ) (hq : C.q=0) :
    C.N=weightedPairs (prefixEmbedding C.cut_le) (pairResidue D Δ C.cut_le) := by
  by_cases hk:C.k=m
  · exact C.canonical_N.1 hk
  · obtain ⟨hw,hN⟩:=C.canonical_N.2 (by have hh:=C.cut_le;omega)
    rw [hN,hq,pairTriangle_zero]

theorem Completion.L_prefix_true_zero (C : Completion D Δ) (v w : Fin m×Bool)
    (hv : v.1.val<C.k) (hTrue : v.2=true) : C.L.mult s(v,w)=0 := by
  have hZero:C.L.degree v=0:=by
    have hh:=(C.prefix_degrees v.1 hv).2
    obtain ⟨i,b⟩:=v
    simp only at hTrue
    subst b
    exact hh
  have hh:=mult_le_degree C.L v w
  omega

theorem Completion.additions_bipartite_of_q_zero (C : Completion D Δ) (hq : C.q=0) :
    ∃P : Finset (Fin m×Bool),∀u v,0<(C.L.addCopies C.N).mult s(u,v) →
      (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P) := by
  obtain ⟨P,hPrefix,hTail,hEven,hCross⟩:=C.bipartite
  let P':=P.filter fun v=>v.2=false ∨ C.k≤v.1.val
  have hLGood:∀u v,0<C.L.mult s(u,v) → u.2=false ∨ C.k≤u.1.val:=by
    intro u v hEdge
    by_contra hn
    have hTrue:u.2=true:=by cases hh:u.2 <;> simp_all
    have hIndex:u.1.val<C.k:=by omega
    have hh:=C.L_prefix_true_zero u v hIndex hTrue
    omega
  have hPair:∀i : Fin C.k,
      prefixEmbedding C.cut_le (i,false)∈P' ∧ prefixEmbedding C.cut_le (i,true)∉P':=by
    intro i
    have hIn:=(hPrefix ⟨i.val,i.isLt.trans_le C.cut_le⟩ i.isLt).1
    constructor
    · exact mem_filter.mpr ⟨hIn,Or.inl rfl⟩
    · intro hh
      have hBad : ((true : Bool) = false) ∨ (C.k ≤ i.val) := (mem_filter.mp hh).2
      rcases hBad with hh|hh
      · cases hh
      · omega
  refine ⟨P',?_⟩
  intro u v hEdge
  change 0<C.L.mult s(u,v)+C.N.mult s(u,v) at hEdge
  by_cases hL:0<C.L.mult s(u,v)
  · have hu:=hLGood u v hL
    have hv:=hLGood v u (by simpa only [Sym2.eq_swap] using hL)
    have hU:(u∈P' ↔ u∈P):=by simp only [P',mem_filter,and_iff_left hu]
    have hV:(v∈P' ↔ v∈P):=by simp only [P',mem_filter,and_iff_left hv]
    simpa only [hU,hV] using hCross u v hL
  · have hN:0<C.N.mult s(u,v):=by omega
    rw [C.N_eq_weightedPairs_of_q_zero hq] at hN
    obtain ⟨i,hi⟩:=weightedPairs_support _ _ u v hN
    rcases Sym2.eq_iff.mp hi with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inl (hPair i)
    · exact Or.inr (hPair i)

theorem Completion.independent_triple_safe_of_q_zero (C : Completion D Δ) (hq : C.q=0)
    (S : Finset (Fin m×Bool)) (hS : S.card=3) (hBase : D.twiceInternal S=0) :
    Δ≤((D.addCopies C.L).addCopies C.N).cutSize S := by
  obtain ⟨z,a,b,hza,hzb,hab,hSet⟩:=card_eq_three.mp hS
  obtain ⟨P,hCross⟩:=C.additions_bipartite_of_q_zero hq
  have hdeg:∀v,(C.L.addCopies C.N).degree v≤Δ:=by
    intro v
    have hh:=C.regular v
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies] at hh
    rw [MultiGraph.degree_addCopies]
    omega
  have hAdded:(C.L.addCopies C.N).twiceInternal S≤2*Δ:=by
    rw [hSet]
    exact bipartite_triple_bound _ Δ P hCross hdeg z a b hza hzb hab
  have hId:=((D.addCopies C.L).addCopies C.N).regular_cut_identity C.regular S
  rw [twiceInternal_addCopies,twiceInternal_addCopies,hBase,hS] at hId
  rw [twiceInternal_addCopies] at hAdded
  omega

end OverfullWork.CanonicalRegularization

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u

/-- The zero-q canonical branch is now no-overfull, including small
centre degrees: it does not require the earlier centre-mass condition. -/
theorem above_half_zero_q_completion_no_overfull (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),N≤Fintype.card V →
      Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*Q^2))+6 → K≤Fintype.card V/(4096*Q^2)+1 →
      (∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) → p.completion.q=0 →
      ¬p.completed.HasOverfullSubset G.maxDegree := by
  obtain ⟨Q,hQ,N,hN⟩:=above_half_critical_completion_overfull_witness.{u} ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro V _ _ G _ B K c p hn hc hdense hB hK hMin hq hOF
  obtain ⟨⟨S,hS,hz,hCut,hBase,hNPositive⟩,hMass⟩:=hN G c p hn hc hdense hB hK hMin hOF
  have hh:=p.completion.independent_triple_safe_of_q_zero hq S hS hBase
  change G.maxDegree≤p.completed.cutSize S at hh
  omega

/-- Every remaining actual overfull candidate in this branch has a
positive canonical triangle parameter and a proper completion prefix. -/
theorem above_half_residual_positive_triangle (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),N≤Fintype.card V →
      Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*Q^2))+6 → K≤Fintype.card V/(4096*Q^2)+1 →
      (∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) →
      p.completed.HasOverfullSubset G.maxDegree →
      (0<p.completion.q ∧ p.completion.k<p.pairIndex+1) ∧
      (∃S : Finset (Fin (p.pairIndex+1)×Bool),S.card=3 ∧ p.centre∈S ∧
        p.completed.cutSize S<G.maxDegree ∧ p.orderedBase.twiceInternal S=0 ∧
        0<p.completion.N.twiceInternal S) ∧
      2*(∑y∈c.setᶜ,G.degree y)<B+4*c.setᶜ.card+6 := by
  obtain ⟨Q,hQ,N,hN⟩:=above_half_critical_completion_overfull_witness.{u} ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro V _ _ G _ B K c p hn hc hdense hB hK hMin hOF
  obtain ⟨⟨S,hS,hz,hCut,hBase,hNPositive⟩,hMass⟩:=hN G c p hn hc hdense hB hK hMin hOF
  have hq:0<p.completion.q:=by
    by_contra hh
    have hZero:p.completion.q=0:=by omega
    have hSafe:=p.completion.independent_triple_safe_of_q_zero hZero S hS hBase
    change G.maxDegree≤p.completed.cutSize S at hSafe
    omega
  have hk:p.completion.k<p.pairIndex+1:=by
    have hLe:=p.completion.cut_le
    by_contra hh
    have hFull:p.completion.k=p.pairIndex+1:=by omega
    have hZero:=p.completion.paired_q_zero hFull
    omega
  exact ⟨⟨hq,hk⟩,⟨S,hS,hz,hCut,hBase,hNPositive⟩,hMass⟩

end OverfullWork.NormalizedCanonicalCandidate
