module

public import OverfullWork.CompensatedReduction
public import OverfullWork.GeneralInternalCover

@[expose] public section


/-! # Completion when every vertex has bounded parallel excess -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

theorem all_budget_exists_zero_deficit (S : Finset V) (x : V) (m D t c β d : ℕ)
    (ht : 0<t) (hcpos : 0<c) (hnum : AdditiveFirstBudget β c m D t k d) (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hstar : ∀ v,M.parallelExcess v≤β)
    (P : M.PartialColouring k) (h : P.ScaledCompletionInvariant S x m t c) :
    ∃ Q : M.PartialColouring k,Q.ScaledCompletionInvariant S x m t c ∧ Q.deficit S=0 := by
  generalize he : P.deficit S=n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hn : n=0
    · exact ⟨P,h,he.trans hn⟩
    · have hpos : 0<∑ i,(P.colouring.missingSet S i).card := by
        change 0<P.deficit S
        omega
      obtain ⟨i,_,hi⟩:=sum_pos_iff.mp hpos
      obtain ⟨u,hu⟩:=card_pos.mp hi
      have heq:=P.colouring.missing_balance_general S hbal h.balance i
      have hvpos : 0<(P.colouring.missingSet Sᶜ i).card:=by omega
      obtain ⟨v,hv⟩:=card_pos.mp hvpos
      obtain ⟨huS,hu0⟩:=mem_filter.mp hu
      obtain ⟨hvS,hv0⟩:=mem_filter.mp hv
      obtain ⟨f⟩:=P.all_budget_invariant_find_five S x m D t c β d h ht hcpos hnum hS hbal hx hreg hstar
        i u v huS hvS hu0 hv0
      let Q:=P.perturb S (P.scaledForbidden S x t c) i u v f hu0 hv0
      have hQ : Q.ScaledCompletionInvariant S x m t c:=P.scaled_perturb_preserves S x m t c h i u v f hu0 hv0
      have hd : P.deficit S=Q.deficit S+1:=P.perturb_deficit_drop S _ i u v f hu0 hv0
      exact ih (Q.deficit S) (by omega) Q hQ rfl


end PartialColouring

theorem exists_regular_partial_all_budget (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t c k β d : ℕ) (ht : 0<t) (hcpos : 0<c) (hnum : PartialColouring.AdditiveFirstBudget β c m D t k d)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hstar : ∀ v,M.parallelExcess v≤β)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hc : ∀ i,(C.missingSet S i).card≤t) :
    ∃ F : MultiGraph V,(∀ e,F.mult e≤M.mult e) ∧ F.IsRegularOfDegree k ∧
      Nonempty (F.EdgeColoring k) ∧
      (∀ v,((M.subtractCopies F).internalPart S).degree v≤c*t) ∧
      ((M.subtractCopies F).internalPart S).degree x=0 ∧
      ((M.subtractCopies F).internalPart S).edgeCount≤2*m*t := by
  let P:=PartialColouring.internalSeed S C
  have hP : P.ScaledCompletionInvariant S x m t c:=PartialColouring.internalSeed_scaled_invariant S x m t c hS C hbal hv hc
  obtain ⟨Q,hQ,hz⟩:=PartialColouring.all_budget_exists_zero_deficit S x m D t c β d ht hcpos hnum hS (hS.trans hSc.symm) hx
    hreg hstar P hP
  have hfact:=Q.factorization_of_zero_deficit S (hS.trans hSc.symm) hQ.balance hz
  refine ⟨Q.graph,Q.le,Q.regular_of_factorization hfact,⟨Q.colouring⟩,hQ.remainder_degree,hQ.centre,?_⟩
  have hh:=hQ.potential
  change (Q.remainder S).edgeCount≤2*m*t
  omega


theorem exists_sparse_internal_cover_all_budget (M : MultiGraph V) (S : Finset V)
    (m D a k b : ℕ) (hS : S.card=m) (hSc : Sᶜ.card=m)
    (hreg : M.IsRegularOfDegree D) (hstar : ∀ v,M.parallelExcess v≤b)
    (hroom : m+2*k+4*a+2*b≤2*D)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hsmall : ∀ i,(C.colourGraph i).edgesWithin S≤a) :
    ∃ H : MultiGraph V,(∀ e,H.mult e≤M.mult e) ∧ H.IsRegularOfDegree k ∧
      Nonempty (H.EdgeColoring k) ∧
      ∀ u v,(u∈S ↔ v∈S) → H.mult s(u,v)=M.mult s(u,v) := by
  classical
  have hprocess : ∀ T : Finset (Fin k),∃ P : M.PartialColouring k,
      P.CoversInternal S ∧
      (∀ j∈T,(P.colouring.colourGraph j).IsRegularOfDegree 1) ∧
      (∀ j,j∉T → P.colouring.colourGraph j=C.colourGraph j) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      refine ⟨PartialColouring.internalSeed S C,?_,by simp,fun _ _ => rfl⟩
      intro u v huv
      exact M.internalPart_covers S u v huv
    | @insert i T hi ih =>
      obtain ⟨P,hcover,hfilled,hunfilled⟩:=ih
      have hCi:=hunfilled i hi
      obtain ⟨J,hJ,hdegree,hcross⟩:=P.exists_free_colour_matching_all_budget S m D a b hS hSc hreg hstar
        hcover hroom i
        (by rw [hCi];exact C.internal_colour_cut_zero S i)
        (by rw [hCi];exact hbal i) (by rw [hCi];exact hsmall i)
      have hp : ∀ z,(P.colouring.colourGraph i).degree z+J.degree z≤1 := by
        intro z
        rw [hdegree]
        have hc:=P.colouring.colourGraph_degree_le_one i z
        split_ifs <;> omega
      let Q:=P.addMatching i J hJ hp
      have ho : ∀ j,j≠i → Q.colouring.colourGraph j=P.colouring.colourGraph j:=
        P.addMatching_other i J hJ hp
      have hselected : ∀ z,(Q.colouring.colourGraph i).degree z=1 := by
        intro z
        rw [P.addMatching_selected,degree_addCopies,hdegree]
        have hc:=P.colouring.colourGraph_degree_le_one i z
        split_ifs <;> omega
      refine ⟨Q,?_,?_,?_⟩
      · intro u v huv
        change P.graph.mult s(u,v)+J.mult s(u,v)=M.mult s(u,v)
        rw [hcover u v huv,hcross u v huv,Nat.add_zero]
      · intro j hj
        rcases mem_insert.mp hj with hj|hj
        · subst j
          exact hselected
        · have hji : j≠i:=fun he => hi (he ▸ hj)
          rw [ho j hji]
          exact hfilled j hj
      · intro j hj
        simp only [mem_insert,not_or] at hj
        rw [ho j hj.1]
        exact hunfilled j hj.2
  obtain ⟨P,hcover,hall,_⟩:=hprocess univ
  have hf : P.colouring.IsFactorization:=fun v i => hall i (mem_univ i) v
  exact ⟨P.graph,P.le,P.regular_of_factorization hf,⟨P.colouring⟩,hcover⟩


/-- The earlier scaled certificate at twice the error pays all additive
first-phase and ordinary Hall margins. -/
theorem all_budget_numerics_of_scaled (c m D t k b : ℕ) (hb : b≤t)
    (ht : 0<t) (hc : 1≤c) (hnum : OverfullWork.ScaledMargins.Budget c m D (2*t) k) :
    PartialColouring.AdditiveFirstBudget b c m D t k (OverfullWork.ScaledMargins.degreeBound c m) ∧
    (m+2*(3*c*t)+4*(m/(3*c)+1)+2*b+2*k≤2*D) ∧ k+3*c*t<D := by
  have hct : t≤c*t:=by simpa using Nat.mul_le_mul_right t hc
  have he : c*(2*t)=2*(c*t):=by ring
  have hf:=hnum.first
  have ho:=hnum.ordinary
  have hv:=hnum.overlap
  have hr:=hnum.residual_hall
  have hp:=hnum.residual_centre
  simp only [OverfullWork.ScaledMargins.badBound,Nat.mul_assoc,he] at hf ho hv hr hp
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · unfold OverfullWork.ScaledMargins.badBound
    omega
  · omega
  · unfold OverfullWork.ScaledMargins.badBound
    omega
  · simp only [Nat.mul_assoc]
    omega
  · simp only [Nat.mul_assoc]
    omega

/-- A regular internal cover under a budget at every vertex; neither a
multiplicity cap nor an exceptional-centre inequality is needed. -/
theorem exists_internal_cover_all_budget (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t c k b : ℕ) (hb : b≤t) (ht : 0<t) (hc : 1000≤c)
    (hnum : OverfullWork.ScaledMargins.Budget c m D (2*t) k)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hbudget : ∀ v,M.parallelExcess v≤b)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hcol : ∀ i,(C.missingSet S i).card≤t) :
    ∃ (H : MultiGraph V) (q : ℕ),q<D ∧ (∀ e,H.mult e≤M.mult e) ∧
      H.IsRegularOfDegree q ∧ Nonempty (H.EdgeColoring q) ∧
      ∀ u v,(u∈S ↔ v∈S) → H.mult s(u,v)=M.mult s(u,v) := by
  have hcpos : 0<c:=by omega
  obtain ⟨hfirst,hHall,hpalette⟩:=all_budget_numerics_of_scaled c m D t k b hb ht (by omega) hnum
  obtain ⟨F,hF,hFreg,⟨CF⟩,hdegree,hcentre,hcount⟩:=M.exists_regular_partial_all_budget S x
    m D t c k b (OverfullWork.ScaledMargins.degreeBound c m) ht hcpos hfirst
    hS hSc hx hreg hbudget C hbal hv hcol
  let N:=M.subtractCopies F
  have hNreg : N.IsRegularOfDegree (D-k):=M.regular_subtract F hF hreg hFreg
  have hNbudget : ∀ v,N.parallelExcess v≤b:=fun v =>
    (M.parallelExcess_mono N (fun _ => Nat.sub_le _ _) v).trans (hbudget v)
  obtain ⟨B,_,hBbal,hBsmall⟩:=N.exists_scaled_residue_colouring S x m (D-k) t c ht hcpos
    (hS.trans hSc.symm) hNreg hdegree hcentre hcount
  have hroom : m+2*(3*c*t)+4*(m/(3*c)+1)+2*b≤2*(D-k):=by omega
  obtain ⟨J,hJ,hJreg,⟨CJ⟩,hcover⟩:=N.exists_sparse_internal_cover_all_budget S m (D-k)
    (m/(3*c)+1) (3*c*t) b hS hSc hNreg hNbudget hroom B hBbal hBsmall
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
  refine ⟨H,k+3*c*t,hpalette,hH,hHreg,⟨CF.addCopies CJ⟩,?_⟩
  intro u v huv
  change F.mult s(u,v)+J.mult s(u,v)=M.mult s(u,v)
  rw [hcover u v huv]
  exact Nat.add_sub_of_le (hF s(u,v))

/-- Actual factorization from a balanced small-deficiency seed and a
uniform excess budget, including the centre. -/
theorem factorization_of_all_budget_seed (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t c k b : ℕ) (hb : b≤t) (ht : 0<t) (hc : 1000≤c)
    (hnum : OverfullWork.ScaledMargins.Budget c m D (2*t) k)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hbudget : ∀ v,M.parallelExcess v≤b)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hcol : ∀ i,(C.missingSet S i).card≤t) :
    ∃ F : M.EdgeColoring D,F.IsFactorization := by
  obtain ⟨H,q,hq,hsub,hH,hcolour,hcover⟩:=M.exists_internal_cover_all_budget S x m D t c k b
    hb ht hc hnum hS hSc hx hreg hbudget C hbal hv hcol
  exact exists_factorization_of_internal_cover M H S D q hq hsub hreg hH hcolour hcover

end SimpleGraph.MultiGraph
