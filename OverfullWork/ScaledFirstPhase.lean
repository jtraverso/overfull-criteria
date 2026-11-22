module

public import OverfullWork.ScaledCompletionInvariant
public import OverfullWork.ScaledMargins

@[expose] public section


/-! # Perturbation and termination with a variable remainder cutoff -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

/-- All local expansion premises follow from the global budget, including
using the sharper regularization centre control. -/
theorem scaled_invariant_find_five (P : M.PartialColouring k) (S : Finset V) (x : V) (m D t c : ℕ)
    (h : P.ScaledCompletionInvariant S x m t c) (ht : 0<t) (hcpos : 0<c) (hnum : OverfullWork.ScaledMargins.Budget c m D t k)
    (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7) (hcontrol : M.CentreControl x 7)
    (hk : k≤D/2+t)
    (i : Fin k) (u v : V) (hu : u∈S) (hv : v∈Sᶜ)
    (hmissU : (P.colouring.colourGraph i).degree u=0)
    (hmissV : (P.colouring.colourGraph i).degree v=0) :
    Nonempty (P.SafeFive S (P.scaledForbidden S x t c) i u v) := by
  let Z:=P.scaledForbidden S x t c
  let b:=4*t+2*Z.card
  have hz : c*Z.card≤4*m+c:=P.scaled_forbidden_card S x m t c h ht
  have hZ : Z.card≤4*m/c+1 := by
    rw [←Nat.add_div_right (4*m) hcpos]
    apply (Nat.le_div_iff_mul_le hcpos).mpr
    simpa only [Nat.mul_comm] using hz
  have hB : b≤OverfullWork.ScaledMargins.badBound c m t:=by
    dsimp [b,OverfullWork.ScaledMargins.badBound]
    omega
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
    have hbudget:=P.crossing_degree_budget S D (c*t) hreg h.remainder_degree u
    rw [if_pos hu] at hbudget
    have hcount:=P.available.degreeInto_le_scaled_neighbours Sᶜ x u 7 (by decide)
      (M.parallelBudget_mono P.available x 7 havail hstar)
      (M.centreControl_mono P.available x 7 havail hcontrol)
    have hh:=hnum.first
    omega
  have hOrd : ∀ z∈Sᶜ,OverfullWork.ScaledMargins.degreeBound c m≤(P.available.neighboursInto S z).card := by
    intro z hzS
    have hnot : z∉S:=mem_compl.mp hzS
    have hzx : z≠x:=fun he => hnot (he ▸ hx)
    have hbudget:=P.crossing_degree_budget S D (c*t) hreg h.remainder_degree z
    rw [if_neg hnot] at hbudget
    have hcount:=P.available.degreeInto_le_neighbours_add_budget S z x 7
      (M.parallelBudget_mono P.available x 7 havail hstar) hzx
    have hh:=hnum.ordinary
    omega
  have hroom : m+2*b<2*(OverfullWork.ScaledMargins.degreeBound c m) := by have hh:=hnum.overlap;omega
  exact P.exists_safe_five S Z i u v m (OverfullWork.ScaledMargins.degreeBound c m) b b hS hu hv hmissU hmissV hbA hbB
    hfirst (hOrd v hv) (fun z hz _ => hOrd z hz) hroom

/-- Termination of the perturbation process: every colour becomes a
perfect matching, while the exact small internal remainder is retained. -/
theorem scaled_exists_zero_deficit (S : Finset V) (x : V) (m D t c : ℕ)
    (ht : 0<t) (hcpos : 0<c) (hnum : OverfullWork.ScaledMargins.Budget c m D t k) (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7) (hcontrol : M.CentreControl x 7)
    (hk : k≤D/2+t)
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
      obtain ⟨f⟩:=P.scaled_invariant_find_five S x m D t c h ht hcpos hnum hS hbal hx hreg hmu hstar hcontrol hk
        i u v huS hvS hu0 hv0
      let Q:=P.perturb S (P.scaledForbidden S x t c) i u v f hu0 hv0
      have hQ : Q.ScaledCompletionInvariant S x m t c:=P.scaled_perturb_preserves S x m t c h i u v f hu0 hv0
      have hd : P.deficit S=Q.deficit S+1:=P.perturb_deficit_drop S _ i u v f hu0 hv0
      exact ih (Q.deficit S) (by omega) Q hQ rfl

theorem internalSeed_scaled_invariant (S : Finset V) (x : V) (m t c : ℕ) (hS : S.card=m)
    (C : (M.internalPart S).EdgeColoring k)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ)
    (hv : ∀ v,(C.missingPalette v).card≤t)
    (hc : ∀ i,(C.missingSet S i).card≤t) :
    (internalSeed S C).ScaledCompletionInvariant S x m t c := by
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
theorem exists_regular_partial_scaled (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t c k : ℕ) (ht : 0<t) (hcpos : 0<c) (hnum : OverfullWork.ScaledMargins.Budget c m D t k)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7) (hcontrol : M.CentreControl x 7)
    (hk : k≤D/2+t)
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
  obtain ⟨Q,hQ,hz⟩:=PartialColouring.scaled_exists_zero_deficit S x m D t c ht hcpos hnum hS (hS.trans hSc.symm) hx
    hreg hmu hstar hcontrol hk P hP
  have hfact:=Q.factorization_of_zero_deficit S (hS.trans hSc.symm) hQ.balance hz
  refine ⟨Q.graph,Q.le,Q.regular_of_factorization hfact,⟨Q.colouring⟩,hQ.remainder_degree,hQ.centre,?_⟩
  have hh:=hQ.potential
  change (Q.remainder S).edgeCount≤2*m*t
  omega


end SimpleGraph.MultiGraph
