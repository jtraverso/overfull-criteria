module

public import OverfullWork.CanonicalTriangleSplit
public import OverfullWork.PerturbationAccounting

@[expose] public section


/-! # Exact triangle cuts for a bipartite graph plus one weighted edge -/
namespace OverfullWork.TriangleBundleCuts
open SimpleGraph Finset CanonicalPairTriangle CanonicalTripleAddition
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

omit [Fintype V] [DecidableEq V] in
theorem twiceInternal_scaledCopies (q : ℕ) (M : MultiGraph V) (S : Finset V) :
    (scaledCopies q M).twiceInternal S=q*M.twiceInternal S := by
  unfold MultiGraph.twiceInternal
  change (∑v∈S,∑w∈S,q*M.mult s(v,w))=_
  simp_rw [←mul_sum]

theorem copiesOn_internal (a b : V) (hab : a≠b) (q : ℕ) (S : Finset V) :
    (copiesOn a b hab q).twiceInternal S=if a∈S ∧ b∈S then 2*q else 0 := by
  rw [copiesOn,twiceInternal_scaledCopies,MultiGraph.twiceInternal_eq,
    MultiGraph.edgesWithin_unitEdge]
  split_ifs <;> omega

theorem bipartite_set_three_bound (J : MultiGraph V) (d : ℕ) (P S : Finset V)
    (hCross : ∀u v,0<J.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P))
    (hdeg : ∀v,J.degree v≤d) (hS : S.card=3) : J.twiceInternal S≤2*d := by
  obtain ⟨z,a,b,hza,hzb,hab,hSet⟩:=card_eq_three.mp hS
  rw [hSet]
  exact bipartite_triple_bound J d P hCross hdeg z a b hza hzb hab

/-- A positive unsafe independent triple must contain BOTH endpoints of
the actual exceptional bundle. In particular it contains the middle vertex. -/
theorem unsafe_triple_contains_bundle (D J : MultiGraph V) (a b : V) (hab : a≠b)
    (q Δ : ℕ) (P S : Finset V)
    (hCross : ∀u v,0<J.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P))
    (hreg : (D.addCopies (J.addCopies (copiesOn a b hab q))).IsRegularOfDegree Δ)
    (hS : S.card=3) (hBase : D.twiceInternal S=0)
    (hCut : (D.addCopies (J.addCopies (copiesOn a b hab q))).cutSize S<Δ) :
    a∈S ∧ b∈S ∧ 0<q := by
  have hdeg:∀v,J.degree v≤Δ:=by
    intro v
    have hh:=hreg v
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies] at hh
    omega
  have hJ:=bipartite_set_three_bound J Δ P S hCross hdeg hS
  have hId:=(D.addCopies (J.addCopies (copiesOn a b hab q))).regular_cut_identity hreg S
  rw [twiceInternal_addCopies,twiceInternal_addCopies,hBase,copiesOn_internal,hS] at hId
  split_ifs at hId with hIn
  · exact ⟨hIn.1,hIn.2,by omega⟩
  · omega

/-- The base degree pays for the single-bundle perturbation. This covers
positive q as well as zero, without constructing a colouring of D+J+bundle. -/
theorem independent_triple_safe_of_degree_room (D J : MultiGraph V)
    (a b : V) (hab : a≠b) (q Δ : ℕ) (P S : Finset V)
    (hCross : ∀u v,0<J.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P))
    (hreg : (D.addCopies (J.addCopies (copiesOn a b hab q))).IsRegularOfDegree Δ)
    (hRoom : ∀v,q≤D.degree v) (hS : S.card=3) (hBase : D.twiceInternal S=0) :
    Δ≤(D.addCopies (J.addCopies (copiesOn a b hab q))).cutSize S := by
  have hdeg:∀v,J.degree v≤Δ-q:=by
    intro v
    have hh:=hreg v
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies] at hh
    have hr:=hRoom v
    omega
  obtain ⟨v,hv⟩:=card_pos.mp (show 0<S.card by omega)
  have hq:q≤Δ:=by
    have hh:=hreg v
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies] at hh
    have hr:=hRoom v
    omega
  have hJ:=bipartite_set_three_bound J (Δ-q) P S hCross hdeg hS
  have hB:(copiesOn a b hab q).twiceInternal S≤2*q:=by rw [copiesOn_internal];split_ifs <;> omega
  have hId:=(D.addCopies (J.addCopies (copiesOn a b hab q))).regular_cut_identity hreg S
  rw [twiceInternal_addCopies,twiceInternal_addCopies,hBase,hS] at hId
  omega

end OverfullWork.TriangleBundleCuts

namespace OverfullWork.CanonicalRegularization
open SimpleGraph Finset CanonicalPairTriangle TriangleBundleCuts
open scoped Classical
variable {m Δ : ℕ} {D : MultiGraph (Fin m×Bool)}
set_option maxHeartbeats 6000000

theorem Completion.unsafe_independent_triple_contains_middle (C : Completion D Δ)
    (hkm : C.k<m) (S : Finset (Fin m×Bool)) (hS : S.card=3)
    (hBase : D.twiceInternal S=0)
    (hCut : ((D.addCopies C.L).addCopies C.N).cutSize S<Δ) :
    C.middleVertex hkm∈S ∧ (C.lastFalse∈S ∨ C.lastTrue∈S) := by
  obtain ⟨P,J,t,hPair,hne,hSplit,hCross⟩:=C.exists_triangle_bundle_split hkm
  have hGraph:(D.addCopies C.L).addCopies C.N=
      D.addCopies (J.addCopies (copiesOn (C.middleVertex hkm) t hne C.q)):=by
    apply MultiGraph.ext_mult
    intro e
    have hh:=congrArg (fun M : MultiGraph (Fin m×Bool)=>M.mult e) hSplit
    change C.L.mult e+C.N.mult e=J.mult e+(copiesOn (C.middleVertex hkm) t hne C.q).mult e at hh
    change D.mult e+C.L.mult e+C.N.mult e=D.mult e+
      (J.mult e+(copiesOn (C.middleVertex hkm) t hne C.q).mult e)
    omega
  have hReg:=C.regular
  rw [hGraph] at hReg hCut
  obtain ⟨hw,ht,hq⟩:=unsafe_triple_contains_bundle D J _ t hne C.q Δ P S hCross hReg hS hBase hCut
  exact ⟨hw,hPair.elim (fun hh=>Or.inl (hh ▸ ht)) (fun hh=>Or.inr (hh ▸ ht))⟩

theorem Completion.independent_triple_safe_of_q_le_base (C : Completion D Δ)
    (hRoom : ∀v,C.q≤D.degree v) (S : Finset (Fin m×Bool)) (hS : S.card=3)
    (hBase : D.twiceInternal S=0) : Δ≤((D.addCopies C.L).addCopies C.N).cutSize S := by
  by_cases hFull:C.k=m
  · exact C.independent_triple_safe_of_q_zero (C.paired_q_zero hFull) S hS hBase
  · have hkm:C.k<m:=by have hh:=C.cut_le;omega
    obtain ⟨P,J,t,hPair,hne,hSplit,hCross⟩:=C.exists_triangle_bundle_split hkm
    have hGraph:(D.addCopies C.L).addCopies C.N=
        D.addCopies (J.addCopies (copiesOn (C.middleVertex hkm) t hne C.q)):=by
      apply MultiGraph.ext_mult
      intro e
      have hh:=congrArg (fun M : MultiGraph (Fin m×Bool)=>M.mult e) hSplit
      change C.L.mult e+C.N.mult e=J.mult e+(copiesOn (C.middleVertex hkm) t hne C.q).mult e at hh
      change D.mult e+C.L.mult e+C.N.mult e=D.mult e+
        (J.mult e+(copiesOn (C.middleVertex hkm) t hne C.q).mult e)
      omega
    have hReg:=C.regular
    rw [hGraph] at hReg ⊢
    exact independent_triple_safe_of_degree_room D J _ t hne C.q Δ P S hCross hReg hRoom hS hBase

end OverfullWork.CanonicalRegularization
