module

public import OverfullWork.GeneralFirstPhase
public import OverfullWork.GeneralSparseInternalCompletion
public import OverfullWork.ScaledInternalCover
public import OverfullWork.GeneralEfficientSeed

@[expose] public section


/-! # Internal cover and factorization with arbitrary fixed budgets -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The regular internal cover is constructed, with both perturbation
phases included. No internal-cover or completion hypothesis is assumed. -/
theorem exists_bounded_internal_cover (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t c k μ b d : ℕ) (hb : 1≤b) (ht : 0<t) (hcpos : 0<c) (hnum : OverfullWork.BoundedMargins.Budget μ b c m D t k d)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤μ) (hstar : M.HasParallelBudget x b) (hcontrol : M.CentreControl x b)
    (hk : k≤D/2+t)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hc : ∀ i,(C.missingSet S i).card≤t) :
    ∃ (H : MultiGraph V) (q : ℕ),q<D ∧ (∀ e,H.mult e≤M.mult e) ∧
      H.IsRegularOfDegree q ∧ Nonempty (H.EdgeColoring q) ∧
      ∀ u v,(u∈S ↔ v∈S) → H.mult s(u,v)=M.mult s(u,v) := by
  obtain ⟨F,hF,hFreg,⟨CF⟩,hdegree,hcentre,hcount⟩:=M.exists_regular_partial_bounded S x
    m D t c k μ b d hb ht hcpos hnum hS hSc hx hreg hstar hcontrol hk C hbal hv hc
  let N:=M.subtractCopies F
  have hNreg : N.IsRegularOfDegree (D-k):=M.regular_subtract F hF hreg hFreg
  have hNmu : ∀ e,N.mult e≤μ:=fun e => (Nat.sub_le _ _).trans (hmu e)
  have hNstar : N.HasParallelBudget x b:=M.parallelBudget_mono N x b (fun _ => Nat.sub_le _ _) hstar
  obtain ⟨B,hBx,hBbal,hBsmall⟩:=N.exists_scaled_residue_colouring S x m (D-k) t c ht hcpos
    (hS.trans hSc.symm) hNreg hdegree hcentre hcount
  have hroom : m+2*(3*c*t)+4*(m/(3*c)+1)+2*b+2≤2*(D-k):=by have hh:=hnum.residual_hall;omega
  have hcentreRoom : 3*c*t+2*μ*(m/(3*c)+1)<D-k:=by have hh:=hnum.residual_centre;omega
  obtain ⟨J,hJ,hJreg,⟨CJ⟩,hcover⟩:=N.exists_sparse_internal_cover_bounded S x m (D-k) (m/(3*c)+1) (3*c*t) μ b
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

/-- Given the five numerical margins, a small-deficiency seed is
completed to an actual factorization of the whole multigraph. -/
theorem exists_factorization_of_bounded_seed (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t c k μ b d : ℕ) (hb : 1≤b) (ht : 0<t) (hcpos : 0<c)
    (hnum : OverfullWork.BoundedMargins.Budget μ b c m D t k d)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤μ)
    (hstar : M.HasParallelBudget x b) (hcontrol : M.CentreControl x b)
    (hk : k≤D/2+t) (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hc : ∀ i,(C.missingSet S i).card≤t) :
    ∃ C : M.EdgeColoring D,C.IsFactorization := by
  obtain ⟨H,q,hq,hsub,hH,hcol,hcover⟩:=M.exists_bounded_internal_cover S x
    m D t c k μ b d hb ht hcpos hnum hS hSc hx hreg hmu hstar hcontrol hk C hbal hv hc
  exact exists_factorization_of_internal_cover M H S D q hq hsub hreg hH hcol hcover

/-- Arbitrary binary depth: the seed is constructed from the balanced
partition, and both completion phases and the bipartite residual are
solved. Only explicit numerical margins remain as hypotheses. -/
theorem factorization_of_binary_seed_budget (M : MultiGraph V) (S : Finset V) (x : V)
    (j m D r t c b d : ℕ) (hr : 1≤r) (hb : 1≤b) (hcpos : 0<c)
    (hcard : Fintype.card V=2*m) (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤2^j)
    (hstar : M.HasParallelBudget x b) (hcontrol : M.CentreControl x b) (hdense : m≤D)
    (hdis : ∀ v, |(M.degreeInto S v:ℝ)-(M.degreeInto Sᶜ v:ℝ)|<2*(r:ℝ))
    (hsize : 15*(2*m:ℝ)*(D/2+r+j*r+1:ℕ)^3<(2*r:ℝ)^6)
    (ht : 2*((2*2^j)*(r+1))+2≤t)
    (hnum : OverfullWork.BoundedMargins.Budget (2^j) b c m D t
      (D/2+(2*2^j-1)*r+2^j) d) :
    ∃ C : M.EdgeColoring D,C.IsFactorization := by
  obtain ⟨k,C,hk,_,hbal,_,hv,_,hcol⟩:=M.exists_efficient_balanced_internal_power_two S
    j m D r hr hcard hS hSc hreg hmu hdense hdis hsize
  have hpow : 1≤2^j:=Nat.one_le_pow j 2 (by omega)
  have hsub : 2*2^j-1+1=2*2^j:=by omega
  have herr : (2*2^j-1)*r+2^j≤t := by
    nlinarith only [ht,hpow,hsub]
  exact M.exists_factorization_of_bounded_seed S x m D t c k (2^j) b d hb
    (by omega) hcpos (OverfullWork.BoundedMargins.budget_palette_mono hk hnum)
    hS hSc hx hreg hmu hstar hcontrol (by omega) C hbal
    (fun v => (hv v).trans (by omega)) (fun i => (hcol i).trans ht)

/-- Full bounded-multiplicity engine with no preselected partition,
colouring, internal cover, or factorization. The hypotheses left to the
asymptotic arithmetic step are two moments and five scalar inequalities. -/
theorem factorization_of_binary_moments (M : MultiGraph V) (x y : V) (hxy : x≠y)
    (j m D r t c b d : ℕ) (hm : 1≤m) (hr : 1≤r) (hb : 1≤b) (hcpos : 0<c)
    (hcard : Fintype.card V=2*m) (hreg : M.IsRegularOfDegree D)
    (hmu : ∀ e,M.mult e≤2^j) (hstar : M.HasParallelBudget x b)
    (hcontrol : M.CentreControl x b) (hdense : m≤D)
    (hpartition : 30*(m:ℝ)^4<(2*(r:ℝ)/(2^j:ℕ))^6)
    (hpalette : 15*(2*m:ℝ)*(D/2+r+j*r+1:ℕ)^3<(2*r:ℝ)^6)
    (ht : 2*((2*2^j)*(r+1))+2≤t)
    (hnum : OverfullWork.BoundedMargins.Budget (2^j) b c m D t
      (D/2+(2*2^j-1)*r+2^j) d) :
    ∃ C : M.EdgeColoring D,C.IsFactorization := by
  let p:=pairEmbedding x y hxy
  have hp : (0:ℝ)<((2^j:ℕ):ℝ):=by positivity
  have hmuR : ∀ u v,(M.mult s(u,v):ℝ)≤((2^j:ℕ):ℝ):=fun u v => by
    exact_mod_cast hmu s(u,v)
  obtain ⟨S,hS,hSc,_,hx,_,hdis⟩:=M.exists_balanced_degree_partition_center m hcard hm
    p 0 ((2^j:ℕ):ℝ) hp hmuR (2*(r:ℝ)/(2^j:ℕ)) (by positivity) hpartition
  have hxS : x∈S := by
    have he : p (0,true)=x:=by
      change (if (true : Bool) then x else y)=x
      simp only [ite_true]
    exact he ▸ hx
  have hdis' : ∀ v, |(M.degreeInto S v:ℝ)-(M.degreeInto Sᶜ v:ℝ)|<2*(r:ℝ) := by
    intro v
    have h:=hdis v
    have he : ((2^j:ℕ):ℝ)*(2*(r:ℝ)/(2^j:ℕ))=2*(r:ℝ):=by
      field_simp
    rwa [he] at h
  exact M.factorization_of_binary_seed_budget S x j m D r t c b d hr hb hcpos
    hcard hS hSc hxS hreg hmu hstar hcontrol hdense hdis' hpalette ht hnum

end SimpleGraph.MultiGraph
