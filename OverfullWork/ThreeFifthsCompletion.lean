module

public import OverfullWork.CentreControl
public import OverfullWork.EightDenseInternalCover

@[expose] public section


/-! # Completion at density three fifths using regularization structure -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

/-- All local expansion premises follow from the global budget, including
using the sharper regularization centre control. -/
theorem invariant_find_five_three_fifths (P : M.PartialColouring k) (S : Finset V) (x : V) (m D t : ℕ)
    (h : P.CompletionInvariant S x m t) (ht : 0<t) (hsize : 10000*t≤m)
    (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7) (hcontrol : M.CentreControl x 7)
    (hdense : 6*m≤5*D) (hk : k≤D/2+t)
    (i : Fin k) (u v : V) (hu : u∈S) (hv : v∈Sᶜ)
    (hmissU : (P.colouring.colourGraph i).degree u=0)
    (hmissV : (P.colouring.colourGraph i).degree v=0) :
    Nonempty (P.SafeFive S (P.forbidden S x t) i u v) := by
  let Z:=P.forbidden S x t
  let b:=4*t+2*Z.card
  have hz : 25*Z.card≤m+25:=P.forbidden_card S x m t h ht
  have hmiss : (P.colouring.missingSet S i).card≤t := by have hh:=h.colour_budget i; omega
  have hcut : (P.colouring.colourGraph i).cutSize S≤3*t := by have hh:=h.colour_budget i; omega
  have hmeq:=P.colouring.missing_balance_general S hbal h.balance i
  have hbA : (S\(P.colouring.colourGraph i).eligibleVertices
      (P.colouring.colourGraph_degree_le_one i) S Z).card≤b := by
    have hb:=(P.colouring.colourGraph i).ineligible_card_bound (P.colouring.colourGraph_degree_le_one i) S Z
    change _≤(P.colouring.missingSet S i).card+(P.colouring.colourGraph i).cutSize S+2*Z.card at hb
    dsimp [b]
    omega
  have hbB : (Sᶜ\(P.colouring.colourGraph i).eligibleVertices
      (P.colouring.colourGraph_degree_le_one i) Sᶜ Z).card≤b := by
    have hb:=(P.colouring.colourGraph i).ineligible_card_bound (P.colouring.colourGraph_degree_le_one i) Sᶜ Z
    rw [cutSize_compl] at hb
    change _≤(P.colouring.missingSet Sᶜ i).card+(P.colouring.colourGraph i).cutSize S+2*Z.card at hb
    dsimp [b]
    omega
  have havail : ∀ e,P.available.mult e≤M.mult e:=fun e => Nat.sub_le _ _
  have hfirst : b<(P.available.neighboursInto Sᶜ u).card := by
    have hbudget:=P.crossing_degree_budget S D (100*t) hreg h.remainder_degree u
    rw [if_pos hu] at hbudget
    have hcount:=P.available.degreeInto_le_scaled_neighbours Sᶜ x u 7 (by decide)
      (M.parallelBudget_mono P.available x 7 havail hstar)
      (M.centreControl_mono P.available x 7 havail hcontrol)
    dsimp [b]
    omega
  have hOrd : ∀ z∈Sᶜ,7*m/12≤(P.available.neighboursInto S z).card := by
    intro z hzS
    have hnot : z∉S:=mem_compl.mp hzS
    have hzx : z≠x:=fun he => hnot (he ▸ hx)
    have hbudget:=P.crossing_degree_budget S D (100*t) hreg h.remainder_degree z
    rw [if_neg hnot] at hbudget
    have hcount:=P.available.degreeInto_le_neighbours_add_budget S z x 7
      (M.parallelBudget_mono P.available x 7 havail hstar) hzx
    omega
  have hroom : m+2*b<2*(7*m/12) := by dsimp [b]; omega
  exact P.exists_safe_five S Z i u v m (7*m/12) b b hS hu hv hmissU hmissV hbA hbB
    hfirst (hOrd v hv) (fun z hz _ => hOrd z hz) hroom

/-- Termination of the perturbation process: every colour becomes a
perfect matching, while the exact small internal remainder is retained. -/
theorem exists_zero_deficit_three_fifths (S : Finset V) (x : V) (m D t : ℕ)
    (ht : 0<t) (hsize : 10000*t≤m) (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7) (hcontrol : M.CentreControl x 7)
    (hdense : 6*m≤5*D) (hk : k≤D/2+t)
    (P : M.PartialColouring k) (h : P.CompletionInvariant S x m t) :
    ∃ Q : M.PartialColouring k,Q.CompletionInvariant S x m t ∧ Q.deficit S=0 := by
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
      obtain ⟨f⟩:=P.invariant_find_five_three_fifths S x m D t h ht hsize hS hbal hx hreg hmu hstar hcontrol hdense hk
        i u v huS hvS hu0 hv0
      let Q:=P.perturb S (P.forbidden S x t) i u v f hu0 hv0
      have hQ : Q.CompletionInvariant S x m t:=P.perturb_preserves S x m t h i u v f hu0 hv0
      have hd : P.deficit S=Q.deficit S+1:=P.perturb_deficit_drop S _ i u v f hu0 hv0
      exact ih (Q.deficit S) (by omega) Q hQ rfl

end PartialColouring

/-- All initial colours are completed by bounded matching perturbations.
The uncovered internal copies form an explicitly bounded residue. -/
theorem exists_regular_partial_three_fifths (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t k : ℕ) (ht : 0<t) (hsize : 10000*t≤m)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7) (hcontrol : M.CentreControl x 7)
    (hdense : 6*m≤5*D) (hk : k≤D/2+t)
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
  obtain ⟨Q,hQ,hz⟩:=PartialColouring.exists_zero_deficit_three_fifths S x m D t ht hsize hS (hS.trans hSc.symm) hx
    hreg hmu hstar hcontrol hdense hk P hP
  have hfact:=Q.factorization_of_zero_deficit S (hS.trans hSc.symm) hQ.balance hz
  refine ⟨Q.graph,Q.le,Q.regular_of_factorization hfact,⟨Q.colouring⟩,hQ.remainder_degree,hQ.centre,?_⟩
  have hh:=hQ.potential
  change (Q.remainder S).edgeCount≤2*m*t
  omega

/-- The regular internal cover is constructed, with both perturbation
phases included. No internal-cover or completion hypothesis is assumed. -/
theorem exists_dense_three_fifths_internal_cover (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t k : ℕ) (ht : 0<t) (hsize : 10000*t≤m)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7) (hcontrol : M.CentreControl x 7)
    (hdense : 6*m≤5*D) (hk : k≤D/2+t)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t) (hc : ∀ i,(C.missingSet S i).card≤t) :
    ∃ (H : MultiGraph V) (q : ℕ),q<D ∧ (∀ e,H.mult e≤M.mult e) ∧
      H.IsRegularOfDegree q ∧ Nonempty (H.EdgeColoring q) ∧
      ∀ u v,(u∈S ↔ v∈S) → H.mult s(u,v)=M.mult s(u,v) := by
  obtain ⟨F,hF,hFreg,⟨CF⟩,hdegree,hcentre,hcount⟩:=M.exists_regular_partial_three_fifths S x
    m D t k ht hsize hS hSc hx hreg hmu hstar hcontrol hdense hk C hbal hv hc
  let N:=M.subtractCopies F
  have hNreg : N.IsRegularOfDegree (D-k):=M.regular_subtract F hF hreg hFreg
  have hNmu : ∀ e,N.mult e≤8:=fun e => (Nat.sub_le _ _).trans (hmu e)
  have hNstar : N.HasParallelBudget x 7:=M.parallelBudget_mono N x 7 (fun _ => Nat.sub_le _ _) hstar
  obtain ⟨B,hBx,hBbal,hBsmall⟩:=N.exists_small_residue_colouring S x m (D-k) t ht
    (hS.trans hSc.symm) hNreg hdegree hcentre hcount
  have hroom : m+2*(300*t)+4*(m/300+1)+16≤2*(D-k):=by omega
  have hcentreRoom : 300*t+16*(m/300+1)<D-k:=by omega
  obtain ⟨J,hJ,hJreg,⟨CJ⟩,hcover⟩:=N.exists_sparse_internal_cover_eight S x m (D-k) (m/300+1) (300*t)
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
