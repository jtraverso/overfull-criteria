module

public import OverfullWork.CentreFirstCompletion
public import OverfullWork.AfterCentreCompletion

@[expose] public section


/-! # Regular partial factor after centre-first and ordinary completion

The only weighted condition concerns the original internal seed's missing
sets. No weighted balance of later states or full factorization is assumed.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- The centre is filled first; the remaining deficit is then removed
with additive ordinary expansion, despite unbounded excess at the centre. -/
theorem exists_regular_partial_weighted_centre (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t c k β d B : ℕ) (ht : 0<t) (hc : 2≤c)
    (hnum : PartialColouring.AdditiveFirstBudget β c m D t k d)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hstar : M.HasParallelBudget x β)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hcol : ∀ i,(C.missingSet S i).card≤t)
    (hweighted : ∀ i,(C.colourGraph i).degree x=0 → (∑ z∈C.missingSet Sᶜ i,M.mult s(x,z))≤B)
    (hroom : k+B<D) :
    ∃ F : MultiGraph V,(∀ e,F.mult e≤M.mult e) ∧ F.IsRegularOfDegree k ∧
      Nonempty (F.EdgeColoring k) ∧
      (∀ v,((M.subtractCopies F).internalPart S).degree v≤c*t) ∧
      ((M.subtractCopies F).internalPart S).degree x=0 ∧
      ((M.subtractCopies F).internalPart S).edgeCount≤2*m*t := by
  have hinit : (PartialColouring.internalSeed S C).ScaledCompletionInvariant S x m t c:=
    PartialColouring.internalSeed_scaled_invariant S x m t c hS C hbal hv hcol
  obtain ⟨P,hP,_,hfilled⟩:=PartialColouring.centre_first_precompletion S x C m D t c β d B
    hS hSc hx ht hc hreg hstar hnum hinit (hv x) hweighted hroom
  obtain ⟨Q,hQ,hz⟩:=PartialColouring.filled_centre_exists_zero_deficit S x m D t c β d
    ht (by omega) hnum hS (hS.trans hSc.symm) hx hreg hstar P hP hfilled
  have hfact:=Q.factorization_of_zero_deficit S (hS.trans hSc.symm) hQ.balance hz
  refine ⟨Q.graph,Q.le,Q.regular_of_factorization hfact,⟨Q.colouring⟩,hQ.remainder_degree,hQ.centre,?_⟩
  have hh:=hQ.potential
  change (Q.remainder S).edgeCount≤2*m*t
  omega

end SimpleGraph.MultiGraph
