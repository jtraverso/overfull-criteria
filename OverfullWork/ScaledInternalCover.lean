module

public import OverfullWork.ScaledFirstPhase
public import OverfullWork.ResidueColouring

@[expose] public section


/-! # Sparse residue colouring and internal cover at a variable cutoff -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Equitable alignment gives small classes in a sparse balanced residue. -/
theorem exists_scaled_residue_colouring (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t c : ℕ) (ht : 0<t) (hc : 0<c) (hbal : S.card=Sᶜ.card) (hreg : M.IsRegularOfDegree D)
    (hdeg : ∀ v,(M.internalPart S).degree v≤c*t)
    (hcentre : (M.internalPart S).degree x=0)
    (hcount : (M.internalPart S).edgeCount≤2*m*t) :
    ∃ C : (M.internalPart S).EdgeColoring (3*c*t),
      (∀ i,(C.colourGraph i).degree x=0) ∧
      (∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) ∧
      ∀ i,(C.colourGraph i).edgesWithin S≤m/(3*c)+1 := by
  obtain ⟨A⟩:=(M.internalPart S).exists_edgeColoring_shannon (2*c*t) (fun v => (hdeg v).trans (by nlinarith))
  have hpalette : 3*(2*c*t)/2=3*c*t:=by
    rw [show 3*(2*c*t)=2*(3*c*t) by ring]
    omega
  rw [hpalette] at A
  have hA : Nonempty ((M.restrict S).EdgeColoring (3*c*t)) := by
    rw [←M.internalPart_restrict S]
    exact ⟨A.restrictColouring S⟩
  have hB : Nonempty ((M.restrict Sᶜ).EdgeColoring (3*c*t)) := by
    rw [←M.internalPart_restrict_compl S]
    exact ⟨A.restrictColouring Sᶜ⟩
  obtain ⟨C,hclasses,heq⟩:=M.exists_balanced_internal_colouring S D (3*c*t) hreg hbal hA hB
  have hsum : (∑ i,(C.colourGraph i).edgesWithin S)≤m*t := by
    rw [C.sum_edgesWithin,internalPart_edgesWithin]
    have hi:=M.internal_edge_counts_eq_of_regular S D hreg hbal
    rw [internalPart_edgeCount,←hi] at hcount
    nlinarith
  refine ⟨C,?_,hclasses,?_⟩
  · intro i
    have h:=C.incidence_le_degree x i
    rw [hcentre] at h
    omega
  · intro i
    have hs : (3*c*t)*(C.colourGraph i).edgesWithin S≤
        (∑ j,(C.colourGraph j).edgesWithin S)+3*c*t := by
      have hh:=sum_le_sum (s:=univ) (fun j _ => heq i j)
      simpa only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,Nat.mul_one] using hh
    have hm : t*((3*c)*(C.colourGraph i).edgesWithin S)≤t*(m+3*c) := by nlinarith
    have hle:=Nat.le_of_mul_le_mul_left hm ht
    rw [←Nat.add_div_right m (show 0<3*c by omega)]
    apply (Nat.le_div_iff_mul_le (show 0<3*c by omega)).mpr
    nlinarith only [hle]

/-- The regular internal cover is constructed, with both perturbation
phases included. No internal-cover or completion hypothesis is assumed. -/
theorem exists_scaled_internal_cover (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t c k : ℕ) (ht : 0<t) (hcpos : 0<c) (hnum : OverfullWork.ScaledMargins.Budget c m D t k)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7) (hcontrol : M.CentreControl x 7)
    (hk : k≤D/2+t)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hc : ∀ i,(C.missingSet S i).card≤t) :
    ∃ (H : MultiGraph V) (q : ℕ),q<D ∧ (∀ e,H.mult e≤M.mult e) ∧
      H.IsRegularOfDegree q ∧ Nonempty (H.EdgeColoring q) ∧
      ∀ u v,(u∈S ↔ v∈S) → H.mult s(u,v)=M.mult s(u,v) := by
  obtain ⟨F,hF,hFreg,⟨CF⟩,hdegree,hcentre,hcount⟩:=M.exists_regular_partial_scaled S x
    m D t c k ht hcpos hnum hS hSc hx hreg hmu hstar hcontrol hk C hbal hv hc
  let N:=M.subtractCopies F
  have hNreg : N.IsRegularOfDegree (D-k):=M.regular_subtract F hF hreg hFreg
  have hNmu : ∀ e,N.mult e≤8:=fun e => (Nat.sub_le _ _).trans (hmu e)
  have hNstar : N.HasParallelBudget x 7:=M.parallelBudget_mono N x 7 (fun _ => Nat.sub_le _ _) hstar
  obtain ⟨B,hBx,hBbal,hBsmall⟩:=N.exists_scaled_residue_colouring S x m (D-k) t c ht hcpos
    (hS.trans hSc.symm) hNreg hdegree hcentre hcount
  have hroom : m+2*(3*c*t)+4*(m/(3*c)+1)+16≤2*(D-k):=by have hh:=hnum.residual_hall;omega
  have hcentreRoom : 3*c*t+16*(m/(3*c)+1)<D-k:=by have hh:=hnum.residual_centre;omega
  obtain ⟨J,hJ,hJreg,⟨CJ⟩,hcover⟩:=N.exists_sparse_internal_cover_eight S x m (D-k) (m/(3*c)+1) (3*c*t)
    hS hSc hx hNreg hNmu hNstar hroom hcentreRoom B hBx hBbal hBsmall
  let H:=F.addCopies J
  have hH : ∀ e,H.mult e≤M.mult e := by
    intro e
    have hf:=hF e
    have hj:=hJ e
    change J.mult e≤M.mult e-F.mult e at hj
    change F.mult e+J.mult e≤M.mult e
    omega
  have hHreg : H.IsRegularOfDegree (k+3*c*t) := by
    intro v
    change (F.addCopies J).degree v=k+3*c*t
    rw [degree_addCopies,hFreg v,hJreg v]
  refine ⟨H,k+3*c*t,by have hh:=hnum.residual_centre;omega,hH,hHreg,⟨CF.addCopies CJ⟩,?_⟩
  intro u v huv
  change F.mult s(u,v)+J.mult s(u,v)=M.mult s(u,v)
  rw [hcover u v huv]
  exact Nat.add_sub_of_le (hF s(u,v))

end SimpleGraph.MultiGraph
