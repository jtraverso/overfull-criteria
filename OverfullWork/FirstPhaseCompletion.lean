module

public import OverfullWork.PerturbationInvariant

@[expose] public section


namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

/-- Termination of the perturbation process: every colour becomes a
perfect matching, while the exact small internal remainder is retained. -/
theorem exists_zero_deficit (S : Finset V) (x : V) (m D t : ℕ)
    (ht : 0<t) (hsize : 1000*t≤m) (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hmu : ∀ e,M.mult e≤2) (hstar : M.HasParallelBudget x 3)
    (hdense : 12*m≤7*D) (hk : k≤D/2+t)
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
      obtain ⟨f⟩:=P.invariant_find_five S x m D t h ht hsize hS hbal hx hreg hmu hstar hdense hk
        i u v huS hvS hu0 hv0
      let Q:=P.perturb S (P.forbidden S x t) i u v f hu0 hv0
      have hQ : Q.CompletionInvariant S x m t:=P.perturb_preserves S x m t h i u v f hu0 hv0
      have hd : P.deficit S=Q.deficit S+1:=P.perturb_deficit_drop S _ i u v f hu0 hv0
      exact ih (Q.deficit S) (by omega) Q hQ rfl

theorem factorization_of_zero_deficit (P : M.PartialColouring k) (S : Finset V)
    (hbal : S.card=Sᶜ.card)
    (hcol : ∀ i,(P.colouring.colourGraph i).edgesWithin S=(P.colouring.colourGraph i).edgesWithin Sᶜ)
    (hz : P.deficit S=0) : P.colouring.IsFactorization := by
  have hmA : ∀ i,(P.colouring.missingSet S i).card=0 := by
    intro i
    have hle : (P.colouring.missingSet S i).card≤P.deficit S :=
      single_le_sum (f:=fun j => (P.colouring.missingSet S j).card) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  have hmB : ∀ i,(P.colouring.missingSet Sᶜ i).card=0 := by
    intro i
    rw [←P.colouring.missing_balance_general S hbal hcol i,hmA i]
  intro v i
  have hc:=P.colouring.colourGraph_degree_le_one i v
  change (P.colouring.colourGraph i).degree v=1
  by_contra hn
  have hv0 : (P.colouring.colourGraph i).degree v=0:=by omega
  by_cases hv : v∈S
  · have hh : v∈P.colouring.missingSet S i:=mem_filter.mpr ⟨hv,hv0⟩
    have he:=card_eq_zero.mp (hmA i)
    rw [he] at hh
    exact notMem_empty v hh
  · have hh : v∈P.colouring.missingSet Sᶜ i:=mem_filter.mpr ⟨mem_compl.mpr hv,hv0⟩
    have he:=card_eq_zero.mp (hmB i)
    rw [he] at hh
    exact notMem_empty v hh

theorem regular_of_factorization (P : M.PartialColouring k) (h : P.colouring.IsFactorization) :
    P.graph.IsRegularOfDegree k := by
  intro v
  rw [←P.colouring.sum_colour_degree v]
  have he : ∀ i,(P.colouring.colourGraph i).degree v=1:=fun i => h v i
  simp only [he,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,Nat.mul_one]

end PartialColouring
end SimpleGraph.MultiGraph
