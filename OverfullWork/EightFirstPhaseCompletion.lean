module

public import OverfullWork.FirstPhaseSeed

@[expose] public section


/-! # First-phase perturbation and termination for multiplicity eight -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

/-- All local expansion premises follow from the global budget, including
at the exceptional centre where parallel copies cost a factor eight. -/
theorem invariant_find_five_eight (P : M.PartialColouring k) (S : Finset V) (x : V) (m D t : ℕ)
    (h : P.CompletionInvariant S x m t) (ht : 0<t) (hsize : 10000*t≤m)
    (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7)
    (hdense : 4*m≤3*D) (hk : k≤D/2+t)
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
    have hcount:=P.available.degreeInto_le_mul_neighbours Sᶜ u 8 (fun w _ => (havail s(u,w)).trans (hmu s(u,w)))
    dsimp [b]
    omega
  have hOrd : ∀ z∈Sᶜ,3*m/5≤(P.available.neighboursInto S z).card := by
    intro z hzS
    have hnot : z∉S:=mem_compl.mp hzS
    have hzx : z≠x:=fun he => hnot (he ▸ hx)
    have hbudget:=P.crossing_degree_budget S D (100*t) hreg h.remainder_degree z
    rw [if_neg hnot] at hbudget
    have hcount:=P.available.degreeInto_le_neighbours_add_budget S z x 7
      (M.parallelBudget_mono P.available x 7 havail hstar) hzx
    omega
  have hroom : m+2*b<2*(3*m/5) := by dsimp [b]; omega
  exact P.exists_safe_five S Z i u v m (3*m/5) b b hS hu hv hmissU hmissV hbA hbB
    hfirst (hOrd v hv) (fun z hz _ => hOrd z hz) hroom

/-- Termination of the perturbation process: every colour becomes a
perfect matching, while the exact small internal remainder is retained. -/
theorem exists_zero_deficit_eight (S : Finset V) (x : V) (m D t : ℕ)
    (ht : 0<t) (hsize : 10000*t≤m) (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7)
    (hdense : 4*m≤3*D) (hk : k≤D/2+t)
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
      obtain ⟨f⟩:=P.invariant_find_five_eight S x m D t h ht hsize hS hbal hx hreg hmu hstar hdense hk
        i u v huS hvS hu0 hv0
      let Q:=P.perturb S (P.forbidden S x t) i u v f hu0 hv0
      have hQ : Q.CompletionInvariant S x m t:=P.perturb_preserves S x m t h i u v f hu0 hv0
      have hd : P.deficit S=Q.deficit S+1:=P.perturb_deficit_drop S _ i u v f hu0 hv0
      exact ih (Q.deficit S) (by omega) Q hQ rfl

end PartialColouring

/-- All initial colours are completed by bounded matching perturbations.
The uncovered internal copies form an explicitly bounded residue. -/
theorem exists_regular_partial_from_internal_eight (M : MultiGraph V) (S : Finset V) (x : V)
    (m D t k : ℕ) (ht : 0<t) (hsize : 10000*t≤m)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤8) (hstar : M.HasParallelBudget x 7)
    (hdense : 4*m≤3*D) (hk : k≤D/2+t)
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
  obtain ⟨Q,hQ,hz⟩:=PartialColouring.exists_zero_deficit_eight S x m D t ht hsize hS (hS.trans hSc.symm) hx
    hreg hmu hstar hdense hk P hP
  have hfact:=Q.factorization_of_zero_deficit S (hS.trans hSc.symm) hQ.balance hz
  refine ⟨Q.graph,Q.le,Q.regular_of_factorization hfact,⟨Q.colouring⟩,hQ.remainder_degree,hQ.centre,?_⟩
  have hh:=hQ.potential
  change (Q.remainder S).edgeCount≤2*m*t
  omega

end SimpleGraph.MultiGraph
