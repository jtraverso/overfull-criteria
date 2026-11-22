module

public import OverfullWork.ResidueColouring

@[expose] public section


namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The regular internal cover is constructed, with both perturbation
phases included. No internal-cover or completion hypothesis is assumed. -/
theorem exists_dense_star_internal_cover (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t k : ℕ) (ht : 0<t) (hsize : 1000*t≤m)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤2) (hstar : M.HasParallelBudget x 3)
    (hdense : 12*m≤7*D) (hk : k≤D/2+t)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hc : ∀ i,(C.missingSet S i).card≤t) :
    ∃ (H : MultiGraph V) (q : ℕ),q<D ∧ (∀ e,H.mult e≤M.mult e) ∧
      H.IsRegularOfDegree q ∧ Nonempty (H.EdgeColoring q) ∧
      ∀ u v,(u∈S ↔ v∈S) → H.mult s(u,v)=M.mult s(u,v) := by
  obtain ⟨F,hF,hFreg,⟨CF⟩,hdegree,hcentre,hcount⟩:=M.exists_regular_partial_from_internal S x
    m D t k ht hsize hS hSc hx hreg hmu hstar hdense hk C hbal hv hc
  let N:=M.subtractCopies F
  have hNreg : N.IsRegularOfDegree (D-k):=M.regular_subtract F hF hreg hFreg
  have hNmu : ∀ e,N.mult e≤2:=fun e => (Nat.sub_le _ _).trans (hmu e)
  have hNstar : N.HasParallelBudget x 3:=M.parallelBudget_mono N x 3 (fun _ => Nat.sub_le _ _) hstar
  obtain ⟨B,hBx,hBbal,hBsmall⟩:=N.exists_small_residue_colouring S x m (D-k) t ht
    (hS.trans hSc.symm) hNreg hdegree hcentre hcount
  have hroom : m+2*(300*t)+4*(m/300+1)+8≤2*(D-k):=by omega
  have hcentreRoom : 300*t+4*(m/300+1)<D-k:=by omega
  obtain ⟨J,hJ,hJreg,⟨CJ⟩,hcover⟩:=N.exists_sparse_internal_cover S x m (D-k) (m/300+1) (300*t)
    hS hSc hx hNreg hNmu hNstar hroom hcentreRoom B hBx hBbal hBsmall
  let H:=F.addCopies J
  have hH : ∀ e,H.mult e≤M.mult e := by
    intro e
    have hf:=hF e
    have hj:=hJ e
    change J.mult e≤M.mult e-F.mult e at hj
    change F.mult e+J.mult e≤M.mult e
    omega
  have hHreg : H.IsRegularOfDegree (k+300*t) := by
    intro v
    change (F.addCopies J).degree v=k+300*t
    rw [degree_addCopies,hFreg v,hJreg v]
  refine ⟨H,k+300*t,by omega,hH,hHreg,⟨CF.addCopies CJ⟩,?_⟩
  intro u v huv
  change F.mult s(u,v)+J.mult s(u,v)=M.mult s(u,v)
  rw [hcover u v huv]
  exact Nat.add_sub_of_le (hF s(u,v))

end SimpleGraph.MultiGraph
