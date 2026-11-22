module

public import OverfullWork.CompensatedReduction
public import OverfullWork.AllBudgetCompletion

@[expose] public section


/-! # Additive completion after the exceptional point has been filled -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

theorem filled_centre_invariant_find_five (P : M.PartialColouring k) (S : Finset V) (x : V) (m D t c β d : ℕ)
    (h : P.ScaledCompletionInvariant S x m t c) (ht : 0<t) (hcpos : 0<c) (hnum : AdditiveFirstBudget β c m D t k d)
    (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hstar : M.HasParallelBudget x β)
    (hfilled : ∀ j,(P.colouring.colourGraph j).degree x=1)
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
  have hux : u≠x:=by
    intro he
    subst u
    have hh:=hfilled i
    omega
  have hfirst : b<(P.available.neighboursInto Sᶜ u).card := by
    have hbudget:=P.crossing_degree_budget S D (c*t) hreg h.remainder_degree u
    rw [if_pos hu] at hbudget
    have hcount:=P.available.degreeInto_le_neighbours_add_excess Sᶜ u
    have hexcess : P.available.parallelExcess u≤β:=
      (M.parallelExcess_mono P.available havail u).trans (hstar u hux)
    have hh:=hnum.first
    omega
  have hOrd : ∀ z∈Sᶜ,d≤(P.available.neighboursInto S z).card := by
    intro z hzS
    have hnot : z∉S:=mem_compl.mp hzS
    have hbudget:=P.crossing_degree_budget S D (c*t) hreg h.remainder_degree z
    rw [if_neg hnot] at hbudget
    have hcount:=P.available.degreeInto_le_neighbours_add_excess S z
    have hexcess : P.available.parallelExcess z≤β:=
      (M.parallelExcess_mono P.available havail z).trans (hstar z (fun he => hnot (he ▸ hx)))
    have hh:=hnum.ordinary
    omega
  have hroom : m+2*b<2*(d) := by have hh:=hnum.overlap;omega
  exact P.exists_safe_five S Z i u v m (d) b b hS hu hv hmissU hmissV hbA hbB
    hfirst (hOrd v hv) (fun z hz _ => hOrd z hz) hroom

theorem filled_centre_exists_zero_deficit (S : Finset V) (x : V) (m D t c β d : ℕ)
    (ht : 0<t) (hcpos : 0<c) (hnum : AdditiveFirstBudget β c m D t k d) (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hstar : M.HasParallelBudget x β) 
    (P : M.PartialColouring k) (h : P.ScaledCompletionInvariant S x m t c)
    (hfilled : ∀ j,(P.colouring.colourGraph j).degree x=1) :
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
      obtain ⟨f⟩:=P.filled_centre_invariant_find_five S x m D t c β d h ht hcpos hnum hS hbal hx hreg hstar hfilled
        i u v huS hvS hu0 hv0
      let Q:=P.perturb S (P.scaledForbidden S x t c) i u v f hu0 hv0
      have hQ : Q.ScaledCompletionInvariant S x m t c:=P.scaled_perturb_preserves S x m t c h i u v f hu0 hv0
      have hd : P.deficit S=Q.deficit S+1:=P.perturb_deficit_drop S _ i u v f hu0 hv0
      have hfilledQ : ∀ j,(Q.colouring.colourGraph j).degree x=1:=
        P.perturb_preserves_filled_point S (P.scaledForbidden S x t c) i u v x f hu0 hv0 hfilled
      exact ih (Q.deficit S) (by omega) Q hQ hfilledQ rfl

end PartialColouring
end SimpleGraph.MultiGraph
