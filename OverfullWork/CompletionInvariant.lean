module

public import OverfullWork.SafePerturbation
public import OverfullWork.ParallelBudget

@[expose] public section


namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

def remainder (P : M.PartialColouring k) (S : Finset V) := P.available.internalPart S

def deficit (P : M.PartialColouring k) (S : Finset V) : ℕ :=
  ∑ i,(P.colouring.missingSet S i).card

structure CompletionInvariant (P : M.PartialColouring k) (S : Finset V) (x : V) (m t : ℕ) : Prop where
  balance : ∀ i,(P.colouring.colourGraph i).edgesWithin S=(P.colouring.colourGraph i).edgesWithin Sᶜ
  remainder_degree : ∀ v,(P.remainder S).degree v≤100*t
  centre : (P.remainder S).degree x=0
  potential : (P.remainder S).edgeCount+2*P.deficit S≤2*m*t
  colour_budget : ∀ i,(P.colouring.colourGraph i).cutSize S+3*(P.colouring.missingSet S i).card≤3*t

noncomputable def forbidden (P : M.PartialColouring k) (S : Finset V) (x : V) (t : ℕ) : Finset V :=
  (univ.filter (fun v => 100*t≤(P.remainder S).degree v))∪{x}

theorem forbidden_card (P : M.PartialColouring k) (S : Finset V) (x : V) (m t : ℕ)
    (h : P.CompletionInvariant S x m t) (ht : 0<t) :
    25*(P.forbidden S x t).card≤m+25 := by
  have he : (P.remainder S).edgeCount≤2*m*t:=by have hp:=h.potential; omega
  have hb:=(P.remainder S).sparse_bad_vertices m t ht he
  have hc:=card_union_le (univ.filter (fun v => 100*t≤(P.remainder S).degree v)) {x}
  simp only [card_singleton] at hc
  change (P.forbidden S x t).card≤_ at hc
  omega

theorem forbidden_remainder_room (P : M.PartialColouring k) (S : Finset V) (x : V) (t : ℕ)
    (v : V) (hv : v∉P.forbidden S x t) : (P.remainder S).degree v<100*t ∧ v≠x := by
  simp only [forbidden,mem_union,mem_filter,mem_univ,true_and,mem_singleton,not_or] at hv
  exact ⟨by omega,hv.2⟩

/-- All local expansion premises follow from the global budget, including
at the exceptional centre where parallel copies cost a factor two. -/
theorem invariant_find_five (P : M.PartialColouring k) (S : Finset V) (x : V) (m D t : ℕ)
    (h : P.CompletionInvariant S x m t) (ht : 0<t) (hsize : 1000*t≤m)
    (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤2) (hstar : M.HasParallelBudget x 3)
    (hdense : 12*m≤7*D) (hk : k≤D/2+t)
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
    have hcount:=P.available.degreeInto_le_mul_neighbours Sᶜ u 2 (fun w _ => (havail s(u,w)).trans (hmu s(u,w)))
    dsimp [b]
    omega
  have hOrd : ∀ z∈Sᶜ,3*m/4≤(P.available.neighboursInto S z).card := by
    intro z hzS
    have hnot : z∉S:=mem_compl.mp hzS
    have hzx : z≠x:=fun he => hnot (he ▸ hx)
    have hbudget:=P.crossing_degree_budget S D (100*t) hreg h.remainder_degree z
    rw [if_neg hnot] at hbudget
    have hcount:=P.available.degreeInto_le_neighbours_add_budget S z x 3
      (M.parallelBudget_mono P.available x 3 havail hstar) hzx
    omega
  have hroom : m+2*b<2*(3*m/4) := by dsimp [b]; omega
  exact P.exists_safe_five S Z i u v m (3*m/4) b b hS hu hv hmissU hmissV hbA hbB
    hfirst (hOrd v hv) (fun z hz _ => hOrd z hz) hroom

end PartialColouring
end SimpleGraph.MultiGraph
