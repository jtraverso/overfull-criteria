module

public import OverfullWork.WeightedCentreSeed
public import OverfullWork.CentreFirstFactor
public import OverfullWork.WeightedCentreHall
public import OverfullWork.WeightedResidueColouring
public import OverfullWork.WeightedMargins

@[expose] public section


/-! # Completing an exceptional centre with a fixed remainder cutoff

The weighted recolourings, centre-first prefix, ordinary completion and
residual Hall matchings are all constructed. The cutoff c is independent
of the maximum multiplicity at the centre.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

theorem exists_internal_cover_weighted_centre (M : MultiGraph V) (A : Finset V) (x : V)
    (m D t c k b W : ℕ) (hc : 1000≤c) (ht : 0<t) (hb : b≤t) (hW : W≤t)
    (hnum : OverfullWork.ScaledMargins.Budget c m D (2*t) k)
    (hsmall : 1000*c*c*(2*t)≤m) (hmD : m≤D) (hk : k≤D/2+t)
    (hkpos : 0<k) (hD : D≤4*k)
    (hA : A.card=m) (hAc : Aᶜ.card=m) (hx : x∈A)
    (hreg : M.IsRegularOfDegree D) (hbudget : M.HasParallelBudget x b)
    (hweight : ∀ v∈Aᶜ,M.mult s(x,v)≤W)
    (C : (M.internalPart A).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin A=(C.colourGraph i).edgesWithin Aᶜ)
    (heq : ∀ i j,(C.colourGraph i).edgesWithin A≤(C.colourGraph j).edgesWithin A+1)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hcol : ∀ i,(C.missingSet A i).card≤t) :
    ∃ (H : MultiGraph V) (q : ℕ),q<D ∧ (∀ e,H.mult e≤M.mult e) ∧
      H.IsRegularOfDegree q ∧ Nonempty (H.EdgeColoring q) ∧
      ∀ u v,(u∈A ↔ v∈A) → H.mult s(u,v)=M.mult s(u,v) := by
  have hcpos : 0<c:=by omega
  obtain ⟨hfirst,hfirstW,hHall,hHallW⟩:=OverfullWork.Gate8J2C.weighted_numerics_of_scaled
    c m D t k b W hc ht hb hW hnum hsmall hmD hk
  obtain ⟨B,hBbal,hBv,hBcol,hBweight⟩:=M.exists_weighted_centre_seed A x k D t W
    hkpos hD hreg hweight C hbal heq hv hcol
  obtain ⟨F,hF,hFreg,⟨CF⟩,hdegree,hcentre,hcount⟩:=M.exists_regular_partial_weighted_centre A x
    m D t c k b (OverfullWork.ScaledMargins.degreeBound c m) (4*t+2*W)
    ht (by omega) hfirst hA hAc hx hreg hbudget B hBbal hBv hBcol
    (fun i _ => hBweight i) (by omega)
  let N:=M.subtractCopies F
  have hNreg : N.IsRegularOfDegree (D-k):=M.regular_subtract F hF hreg hFreg
  have hNbudget : N.HasParallelBudget x b:=
    M.parallelBudget_mono N x b (fun _ => Nat.sub_le _ _) hbudget
  let w : V → ℕ:=fun v => M.mult s(x,v)
  have hw : ∀ v∈Aᶜ,w v≤W:=hweight
  have hsum : (∑ v∈Aᶜ,w v)≤D := by
    have hh:=M.degreeInto_add_compl A x
    rw [hreg x] at hh
    change M.degreeInto Aᶜ x≤D
    omega
  obtain ⟨R,hRx,hRbal,hRsmall,hRweight⟩:=N.exists_weighted_residue_colouring A x
    m (D-k) t c D W ht hcpos (hA.trans hAc.symm) hNreg hdegree hcentre hcount w hw hsum
  have hroom : m+2*(3*c*t)+4*(m/(3*c)+1)+2*b+2≤2*(D-k):=by omega
  have hcentreRoom : 3*c*t+(D/3+2*W)<D-k:=by omega
  obtain ⟨J,hJ,hJreg,⟨CJ⟩,hcover⟩:=N.exists_sparse_internal_cover_weighted_majorant A x
    m (D-k) (m/(3*c)+1) (3*c*t) b (D/3+2*W)
    hA hAc hx hNreg hNbudget hroom hcentreRoom R hRx hRbal hRsmall w
    (fun _ => Nat.sub_le _ _) hRweight
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
  refine ⟨H,k+3*c*t,by omega,hH,hHreg,⟨CF.addCopies CJ⟩,?_⟩
  intro u v huv
  change F.mult s(u,v)+J.mult s(u,v)=M.mult s(u,v)
  rw [hcover u v huv]
  exact Nat.add_sub_of_le (hF s(u,v))

/-- A balanced equitable seed gives an actual factorization, with both
exceptional-centre phases solved by weighted recolouring. -/
theorem factorization_of_weighted_centre_seed (M : MultiGraph V) (A : Finset V) (x : V)
    (m D t c k b W : ℕ) (hc : 1000≤c) (ht : 0<t) (hb : b≤t) (hW : W≤t)
    (hnum : OverfullWork.ScaledMargins.Budget c m D (2*t) k)
    (hsmall : 1000*c*c*(2*t)≤m) (hmD : m≤D) (hk : k≤D/2+t)
    (hkpos : 0<k) (hD : D≤4*k)
    (hA : A.card=m) (hAc : Aᶜ.card=m) (hx : x∈A)
    (hreg : M.IsRegularOfDegree D) (hbudget : M.HasParallelBudget x b)
    (hweight : ∀ v∈Aᶜ,M.mult s(x,v)≤W)
    (C : (M.internalPart A).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin A=(C.colourGraph i).edgesWithin Aᶜ)
    (heq : ∀ i j,(C.colourGraph i).edgesWithin A≤(C.colourGraph j).edgesWithin A+1)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hcol : ∀ i,(C.missingSet A i).card≤t) :
    ∃ F : M.EdgeColoring D,F.IsFactorization := by
  obtain ⟨H,q,hq,hsub,hH,hcolour,hcover⟩:=M.exists_internal_cover_weighted_centre A x
    m D t c k b W hc ht hb hW hnum hsmall hmD hk hkpos hD hA hAc hx hreg hbudget
    hweight C hbal heq hv hcol
  exact exists_factorization_of_internal_cover M H A D q hq hsub hreg hH hcolour hcover

end SimpleGraph.MultiGraph
