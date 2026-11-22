module

public import OverfullWork.FirstPhaseCompletion
public import OverfullWork.SeedThreshold

@[expose] public section


namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Double counting the missing incidences, by vertex or by colour. -/
theorem EdgeColoring.sum_missing_eq {M : MultiGraph V} {k : ℕ} (C : M.EdgeColoring k) (S : Finset V) :
    (∑ i,(C.missingSet S i).card)=∑ v∈S,(C.missingPalette v).card := by
  simp only [EdgeColoring.missingSet,EdgeColoring.missingPalette,card_eq_sum_ones,sum_filter]
  rw [sum_comm]

namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

def internalSeed (S : Finset V) (C : (M.internalPart S).EdgeColoring k) : M.PartialColouring k :=
  ⟨M.internalPart S,C,M.internalPart_le S⟩

theorem internalSeed_remainder_zero (S : Finset V) (C : (M.internalPart S).EdgeColoring k) :
    ∀ e,((internalSeed S C).remainder S).mult e=0 := by
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    change ((M.subtractCopies (M.internalPart S)).internalPart S).mult s(u,v)=0
    rw [internalPart_mult]
    change (if u∈S ↔ v∈S then M.mult s(u,v)-(M.internalPart S).mult s(u,v) else 0)=0
    rw [internalPart_mult]
    split_ifs <;> omega

theorem internalSeed_invariant (S : Finset V) (x : V) (m t : ℕ) (hS : S.card=m)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t)
    (hc : ∀ i,(C.missingSet S i).card≤t) :
    (internalSeed S C).CompletionInvariant S x m t := by
  have hz:=internalSeed_remainder_zero S C
  have hd : ∀ v,((internalSeed S C).remainder S).degree v=0 := by
    intro v
    simp only [degree,hz,sum_const_zero]
  have he : ((internalSeed S C).remainder S).edgeCount=0 := by
    simp only [edgeCount,hz,sum_const_zero]
  refine ⟨hbal,fun v => by rw [hd]; omega,hd x,?_,?_⟩
  · rw [he,Nat.zero_add]
    have hdef : (internalSeed S C).deficit S≤m*t := by
      change (∑ i,(C.missingSet S i).card)≤m*t
      rw [C.sum_missing_eq]
      have hh:=sum_le_sum (s:=S) (fun v _ => hv v)
      simpa only [sum_const,hS,Nat.nsmul_eq_mul] using hh
    nlinarith [hdef]
  · intro i
    change (C.colourGraph i).cutSize S+3*(C.missingSet S i).card≤3*t
    rw [C.internal_colour_cut_zero S i]
    have h:=hc i
    omega

end PartialColouring

/-- All initial colours are completed by bounded matching perturbations.
The uncovered internal copies form an explicitly bounded residue. -/
theorem exists_regular_partial_from_internal (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t k : ℕ) (ht : 0<t) (hsize : 1000*t≤m)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤2) (hstar : M.HasParallelBudget x 3)
    (hdense : 12*m≤7*D) (hk : k≤D/2+t)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hc : ∀ i,(C.missingSet S i).card≤t) :
    ∃ F : MultiGraph V,(∀ e,F.mult e≤M.mult e) ∧ F.IsRegularOfDegree k ∧
      Nonempty (F.EdgeColoring k) ∧
      (∀ v,((M.subtractCopies F).internalPart S).degree v≤100*t) ∧
      ((M.subtractCopies F).internalPart S).degree x=0 ∧
      ((M.subtractCopies F).internalPart S).edgeCount≤2*m*t := by
  let P:=PartialColouring.internalSeed S C
  have hP : P.CompletionInvariant S x m t:=PartialColouring.internalSeed_invariant S x m t hS C hbal hv hc
  obtain ⟨Q,hQ,hz⟩:=PartialColouring.exists_zero_deficit S x m D t ht hsize hS (hS.trans hSc.symm) hx
    hreg hmu hstar hdense hk P hP
  have hfact:=Q.factorization_of_zero_deficit S (hS.trans hSc.symm) hQ.balance hz
  refine ⟨Q.graph,Q.le,Q.regular_of_factorization hfact,⟨Q.colouring⟩,hQ.remainder_degree,hQ.centre,?_⟩
  have hh:=hQ.potential
  change (Q.remainder S).edgeCount≤2*m*t
  omega

end SimpleGraph.MultiGraph
