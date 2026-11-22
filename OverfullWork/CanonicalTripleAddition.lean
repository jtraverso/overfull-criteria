module

public import OverfullWork.CriticalCentreTriples
public import OverfullWork.CanonicalRegularization

@[expose] public section


/-! # A residual independent triple must use the explicit N layer

The bipartite L layer alone cannot make a triple overfull. Both its
bipartition and degree bounds come from the actual Completion fields.
-/
namespace OverfullWork.CanonicalTripleAddition
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem two_bundles_le_degree (M : MultiGraph V) (v a b : V) (hab : a≠b) :
    M.mult s(v,a)+M.mult s(v,b)≤M.degree v := by
  rw [M.degree_eq_sum_mult]
  have hh:(∑w∈({a,b}:Finset V),M.mult s(v,w))≤∑w:V,M.mult s(v,w):=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)
  simpa only [sum_insert,mem_singleton,hab,not_false_eq_true,sum_singleton] using hh

theorem bipartite_triple_bound (L : MultiGraph V) (Δ : ℕ) (P : Finset V)
    (hCross : ∀u v,0<L.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P))
    (hdeg : ∀v,L.degree v≤Δ) (z a b : V)
    (hza : z≠a) (hzb : z≠b) (hab : a≠b) :
    L.twiceInternal {z,a,b}≤2*Δ := by
  rw [CriticalCentreTriples.triple_internal L z a b hza hzb hab]
  have haz:L.mult s(a,z)=L.mult s(z,a):=congrArg L.mult (Sym2.eq_swap)
  have hbz:L.mult s(b,z)=L.mult s(z,b):=congrArg L.mult (Sym2.eq_swap)
  have hba:L.mult s(b,a)=L.mult s(a,b):=congrArg L.mult (Sym2.eq_swap)
  by_cases hA:0<L.mult s(z,a)
  · by_cases hB:0<L.mult s(z,b)
    · have hAB:L.mult s(a,b)=0:=by
        by_contra hn
        have hC:=hCross a b (by omega)
        have h₁:=hCross z a hA
        have h₂:=hCross z b hB
        tauto
      have hh:=(two_bundles_le_degree L z a b hab).trans (hdeg z)
      omega
    · have hh:=(two_bundles_le_degree L a z b hzb).trans (hdeg a)
      rw [haz] at hh
      omega
  · have hh:=(two_bundles_le_degree L b z a hza).trans (hdeg b)
    rw [hbz,hba] at hh
    omega

omit [Fintype V] [DecidableEq V] in
theorem twiceInternal_addCopies (M N : MultiGraph V) (S : Finset V) :
    (M.addCopies N).twiceInternal S=M.twiceInternal S+N.twiceInternal S := by
  change (∑v∈S,∑w∈S,(M.mult s(v,w)+N.mult s(v,w)))=_
  simp_rw [sum_add_distrib]
  rfl

end OverfullWork.CanonicalTripleAddition

namespace OverfullWork.CanonicalRegularization
open SimpleGraph Finset CanonicalTripleAddition
open scoped Classical
variable {m Δ : ℕ} {D : MultiGraph (Fin m×Bool)}

theorem Completion.N_internal_positive_of_unsafe_triple (C : Completion D Δ)
    (S : Finset (Fin m×Bool)) (hS : S.card=3)
    (hBase : D.twiceInternal S=0)
    (hCut : ((D.addCopies C.L).addCopies C.N).cutSize S<Δ) :
    0<C.N.twiceInternal S := by
  obtain ⟨z,hz⟩:=card_pos.mp (show 0<S.card by omega)
  have hErase:(S.erase z).card=2:=by have hh:=card_erase_add_one hz;omega
  obtain ⟨a,b,hab,hAB⟩:=card_eq_two.mp hErase
  have hza:z≠a:=by
    have ha:a∈S.erase z:=by rw [hAB];simp
    exact (mem_erase.mp ha).1.symm
  have hzb:z≠b:=by
    have hb:b∈S.erase z:=by rw [hAB];simp
    exact (mem_erase.mp hb).1.symm
  have hSet:S={z,a,b}:=by rw [←insert_erase hz,hAB]
  obtain ⟨P,h₁,h₂,h₃,hCross⟩:=C.bipartite
  have hL:C.L.twiceInternal S≤2*Δ:=by
    rw [hSet]
    exact bipartite_triple_bound C.L Δ P hCross
      (fun v=>(C.additions_bounded v).trans (Nat.sub_le _ _)) z a b hza hzb hab
  have hId:=((D.addCopies C.L).addCopies C.N).regular_cut_identity C.regular S
  rw [twiceInternal_addCopies,twiceInternal_addCopies,hBase,hS] at hId
  omega

end OverfullWork.CanonicalRegularization
