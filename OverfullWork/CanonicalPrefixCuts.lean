module

public import OverfullWork.CanonicalResidualFirstPair

@[expose] public section


/-! # Different prefix pairs cannot form a residual independent triangle -/
namespace OverfullWork.CanonicalPrefixCuts
open SimpleGraph Finset CanonicalPairTriangle CanonicalTriangleSplit CanonicalZeroTriangle
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

omit [Fintype V] in
theorem copiesOn_zero_avoiding_endpoint (a b : V) (hab : a≠b) (q : ℕ) (u v : V)
    (hu : u≠a) (hv : v≠a) : (copiesOn a b hab q).mult s(u,v)=0 := by
  by_contra hn
  have hh:=copiesOn_support a b hab q u v (by omega)
  rcases Sym2.eq_iff.mp hh with ⟨he,_⟩|⟨_,he⟩
  · exact hu he
  · exact hv he

omit [Fintype V] [DecidableEq V] in
theorem mult_zero_of_internal_zero (M : MultiGraph V) (S : Finset V)
    (hZero : M.twiceInternal S=0) (u v : V) (hu : u∈S) (hv : v∈S) : M.mult s(u,v)=0 := by
  have hRow:M.mult s(u,v)≤∑w∈S,M.mult s(u,w):=
    single_le_sum (f:=fun w=>M.mult s(u,w)) (fun _ _=>Nat.zero_le _) hv
  have hSum:(∑w∈S,M.mult s(u,w))≤M.twiceInternal S:=
    single_le_sum (f:=fun z=>∑w∈S,M.mult s(z,w)) (fun _ _=>Nat.zero_le _) hu
  omega

theorem regular_triple_cut_of_zero_pair (M : MultiGraph V) (Δ : ℕ)
    (hreg : M.IsRegularOfDegree Δ) (z a b : V)
    (hza : z≠a) (hzb : z≠b) (hab : a≠b) (hZero : M.mult s(z,a)=0) :
    Δ≤M.cutSize {z,a,b} := by
  have hId:=CriticalCentreTriples.triple_cut_identity M z a b hza hzb hab
  have hRow:=CanonicalTripleAddition.two_bundles_le_degree M b z a hza
  have hbz:M.mult s(b,z)=M.mult s(z,b):=congrArg M.mult Sym2.eq_swap
  have hba:M.mult s(b,a)=M.mult s(a,b):=congrArg M.mult Sym2.eq_swap
  rw [hbz,hba,hreg b] at hRow
  rw [hZero,hreg z,hreg a,hreg b] at hId
  omega

end OverfullWork.CanonicalPrefixCuts

namespace OverfullWork.CanonicalRegularization
open SimpleGraph Finset CanonicalPairTriangle CanonicalTriangleSplit CanonicalZeroTriangle CanonicalPrefixCuts
open scoped Classical
variable {m Δ : ℕ} {D : MultiGraph (Fin m×Bool)}
set_option maxHeartbeats 6000000

theorem Completion.added_between_distinct_prefix_zero (C : Completion D Δ)
    (u v : Fin m×Bool) (hu : u.1.val<C.k) (hv : v.1.val<C.k)
    (hDifferent : u.1.val≠v.1.val) : (C.L.addCopies C.N).mult s(u,v)=0 := by
  have hL:C.L.mult s(u,v)=0:=by
    obtain ⟨P,hPrefix,hTail,hEven,hCross⟩:=C.bipartite
    have hU:u∈P:=by obtain ⟨i,b⟩:=u;cases b;exact (hPrefix i hu).1;exact (hPrefix i hu).2
    have hV:v∈P:=by obtain ⟨i,b⟩:=v;cases b;exact (hPrefix i hv).1;exact (hPrefix i hv).2
    by_contra hn
    have hh:=hCross u v (by omega)
    tauto
  have hPairs:∀r : Fin C.k→ℕ,
      (weightedPairs (prefixEmbedding C.cut_le) r).mult s(u,v)=0:=by
    intro r
    by_contra hn
    obtain ⟨i,hi⟩:=weightedPairs_support (prefixEmbedding C.cut_le) r u v (Nat.pos_of_ne_zero hn)
    rcases Sym2.eq_iff.mp hi with ⟨hU,hV⟩|⟨hU,hV⟩
    all_goals
      have h₁:=congrArg (fun x : Fin m×Bool=>x.1.val) hU
      have h₂:=congrArg (fun x : Fin m×Bool=>x.1.val) hV
      exact hDifferent (h₁.trans h₂.symm)
  have hN:C.N.mult s(u,v)=0:=by
    by_cases hFull:C.k=m
    · rw [C.canonical_N.1 hFull]
      exact hPairs _
    · have hkm:C.k<m:=by have hh:=C.cut_le;omega
      obtain ⟨hw,hN⟩:=C.canonical_N.2 hkm
      have hUw:u≠(⟨C.k,hkm⟩,false):=by
        intro hh
        have he:=congrArg (fun x : Fin m×Bool=>x.1.val) hh
        change u.1.val=C.k at he
        omega
      have hVw:v≠(⟨C.k,hkm⟩,false):=by
        intro hh
        have he:=congrArg (fun x : Fin m×Bool=>x.1.val) hh
        change v.1.val=C.k at he
        omega
      rw [hN]
      change (weightedPairs _ _).mult s(u,v)+
        ((copiesOn _ _ (hw _) C.q).mult s(u,v)+(copiesOn _ _ (hw _) C.q).mult s(u,v))=0
      rw [hPairs,copiesOn_zero_avoiding_endpoint _ _ _ C.q u v hUw hVw,
        copiesOn_zero_avoiding_endpoint _ _ _ C.q u v hUw hVw]
  change C.L.mult s(u,v)+C.N.mult s(u,v)=0
  omega

end OverfullWork.CanonicalRegularization

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun CanonicalPrefixCuts
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ}
variable {c : Certificate G B K}
set_option maxHeartbeats 8000000

theorem Candidate.prefix_one_of_unsafe_independent_triple (p : Candidate c)
    (hMin : ∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) (hScale : 3*B≤2*G.maxDegree)
    (S : Finset (Fin (p.pairIndex+1)×Bool)) (hS : S.card=3) (hz : p.centre∈S)
    (hBase : p.orderedBase.twiceInternal S=0)
    (hCut : p.completed.cutSize S<G.maxDegree) : p.completion.k=1 := by
  have hFirst:=p.centre_first_pair_of_unsafe_independent_triple hMin hScale S hS hBase hCut
  have hq:0<p.completion.q:=by
    by_contra hh
    have hSafe:=p.completion.independent_triple_safe_of_q_zero (by omega) S hS hBase
    change G.maxDegree≤p.completed.cutSize S at hSafe
    omega
  have hkm:p.completion.k<p.pairIndex+1:=by
    have hLe:=p.completion.cut_le
    by_contra hh
    have hZero:=p.completion.paired_q_zero (show p.completion.k=p.pairIndex+1 by omega)
    omega
  obtain ⟨hw,ht⟩:=p.completion.unsafe_independent_triple_contains_middle hkm S hS hBase hCut
  obtain ⟨t,htS,htPair⟩:∃t,t∈S ∧ (t=p.completion.lastFalse ∨ t=p.completion.lastTrue):=by
    rcases ht with ht|ht
    · exact ⟨_,ht,Or.inl rfl⟩
    · exact ⟨_,ht,Or.inr rfl⟩
  have hTIndex:t.1.val=p.completion.k-1:=by
    rcases htPair with rfl|rfl <;> rfl
  have hWIndex:(p.completion.middleVertex hkm).1.val=p.completion.k:=rfl
  by_contra hn
  have hLong:1<p.completion.k:=by have hh:=p.completion.positive;omega
  have hzt:p.centre≠t:=by
    intro hh;have he:=congrArg (fun x : Fin (p.pairIndex+1)×Bool=>x.1.val) hh;omega
  have hzw:p.centre≠p.completion.middleVertex hkm:=by
    intro hh;have he:=congrArg (fun x : Fin (p.pairIndex+1)×Bool=>x.1.val) hh;omega
  have htw:t≠p.completion.middleVertex hkm:=by
    intro hh;have he:=congrArg (fun x : Fin (p.pairIndex+1)×Bool=>x.1.val) hh;omega
  have hSet:S={p.centre,t,p.completion.middleVertex hkm}:=by
    apply (eq_of_subset_of_card_le (show {p.centre,t,p.completion.middleVertex hkm}⊆S by
      intro v hv;simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl|rfl|rfl <;> assumption) ?_).symm
    simp [hS,hzt,hzw,htw]
  have hAdded:=p.completion.added_between_distinct_prefix_zero p.centre t
    (by omega) (by omega) (by omega)
  have hOriginal:=mult_zero_of_internal_zero p.orderedBase S hBase p.centre t hz htS
  have hZero:p.completed.mult s(p.centre,t)=0:=by
    change p.orderedBase.mult s(p.centre,t)+p.completion.L.mult s(p.centre,t)+p.completion.N.mult s(p.centre,t)=0
    change p.completion.L.mult s(p.centre,t)+p.completion.N.mult s(p.centre,t)=0 at hAdded
    omega
  have hSafe:=regular_triple_cut_of_zero_pair p.completed G.maxDegree p.completion.regular
    p.centre t (p.completion.middleVertex hkm) hzt hzw htw hZero
  rw [←hSet] at hSafe
  omega

end OverfullWork.NormalizedCanonicalCandidate
