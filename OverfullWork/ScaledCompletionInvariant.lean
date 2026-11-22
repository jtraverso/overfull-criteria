module

public import OverfullWork.PerturbationInvariant

@[expose] public section


/-! # A scalable remainder threshold for the completion invariant -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

structure ScaledCompletionInvariant (P : M.PartialColouring k) (S : Finset V) (x : V) (m t c : ℕ) : Prop where
  balance : ∀ i,(P.colouring.colourGraph i).edgesWithin S=(P.colouring.colourGraph i).edgesWithin Sᶜ
  remainder_degree : ∀ v,(P.remainder S).degree v≤c*t
  centre : (P.remainder S).degree x=0
  potential : (P.remainder S).edgeCount+2*P.deficit S≤2*m*t
  colour_budget : ∀ i,(P.colouring.colourGraph i).cutSize S+3*(P.colouring.missingSet S i).card≤3*t

noncomputable def scaledForbidden (P : M.PartialColouring k) (S : Finset V) (x : V) (t c : ℕ) : Finset V :=
  (univ.filter (fun v => c*t≤(P.remainder S).degree v))∪{x}

theorem scaled_forbidden_card (P : M.PartialColouring k) (S : Finset V) (x : V) (m t c : ℕ)
    (h : P.ScaledCompletionInvariant S x m t c) (ht : 0<t) :
    c*(P.scaledForbidden S x t c).card≤4*m+c := by
  have he : (P.remainder S).edgeCount≤2*m*t:=by have hp:=h.potential;omega
  have hb:=(P.remainder S).high_degree_card_bound (c*t)
  have hprod : t*(c*(univ.filter (fun v => c*t≤(P.remainder S).degree v)).card)≤t*(4*m):=by
    nlinarith
  have hbound:=Nat.le_of_mul_le_mul_left hprod ht
  have hu:=card_union_le (univ.filter (fun v => c*t≤(P.remainder S).degree v)) {x}
  simp only [card_singleton] at hu
  have hh:=Nat.mul_le_mul_left c hu
  change c*(P.scaledForbidden S x t c).card≤_ at hh
  nlinarith

theorem scaled_forbidden_remainder_room (P : M.PartialColouring k) (S : Finset V) (x : V) (t c : ℕ)
    (v : V) (hv : v∉P.scaledForbidden S x t c) : (P.remainder S).degree v<c*t ∧ v≠x := by
  simp only [scaledForbidden,mem_union,mem_filter,mem_univ,true_and,mem_singleton,not_or] at hv
  exact ⟨by omega,hv.2⟩


/-- A local perturbation preserves all four global budgets, including
the small maximum degree of the exact internal remainder. -/
theorem scaled_perturb_preserves (P : M.PartialColouring k) (S : Finset V) (x : V) (m t c : ℕ)
    (h : P.ScaledCompletionInvariant S x m t c) (i : Fin k) (u v : V)
    (f : P.SafeFive S (P.scaledForbidden S x t c) i u v)
    (h0 : (P.colouring.colourGraph i).degree u=0) (h5 : (P.colouring.colourGraph i).degree v=0) :
    (P.perturb S (P.scaledForbidden S x t c) i u v f h0 h5).ScaledCompletionInvariant S x m t c := by
  let Q:=P.perturb S (P.scaledForbidden S x t c) i u v f h0 h5
  have hr : Q.remainder S=(P.remainder S).addCopies (fiveRemoved f.path):=
    P.perturb_remainder S _ i u v f h0 h5
  obtain ⟨hiA,hiB⟩:=P.perturb_internal_counts S _ i u v f h0 h5
  have hm:=P.perturb_missing_drop S _ i u v f h0 h5
  have hd:=P.perturb_deficit_drop S _ i u v f h0 h5
  have hcut:=P.perturb_cut S _ i u v f h0 h5
  have hother:=P.perturb_other S _ i u v f h0 h5
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    by_cases hj : j=i
    · subst j
      have hb:=h.balance i
      change (Q.colouring.colourGraph i).edgesWithin S+1=_ at hiA
      change (Q.colouring.colourGraph i).edgesWithin Sᶜ+1=_ at hiB
      dsimp only [Q] at *
      omega
    · change (Q.colouring.colourGraph j).edgesWithin S=(Q.colouring.colourGraph j).edgesWithin Sᶜ
      rw [hother j hj]
      exact h.balance j
  · intro z
    rw [hr,degree_addCopies]
    have hb:=h.remainder_degree z
    have hmatch : (fiveRemoved f.path).degree z≤1 := by rw [degree_fiveRemoved]; split_ifs <;> omega
    by_cases hz : 0<(fiveRemoved f.path).degree z
    · have hs:=P.scaled_forbidden_remainder_room S x t c z (f.safe z hz)
      dsimp only [Q] at *
      omega
    · omega
  · rw [hr,degree_addCopies,h.centre]
    have hzero : (fiveRemoved f.path).degree x=0 := by
      by_contra hn
      have hnot:=f.safe x (by omega)
      exact hnot (mem_union_right _ (mem_singleton_self x))
    dsimp only [Q] at *
    omega
  · rw [hr,edgeCount_addCopies,(five_edge_counts f.path).1]
    have hp:=h.potential
    change P.deficit S=Q.deficit S+1 at hd
    dsimp only [Q] at *
    omega
  · intro j
    by_cases hj : j=i
    · subst j
      have hb:=h.colour_budget i
      change (P.colouring.missingSet S i).card=(Q.colouring.missingSet S i).card+1 at hm
      change (Q.colouring.colourGraph i).cutSize S=(P.colouring.colourGraph i).cutSize S+3 at hcut
      dsimp only [Q] at *
      omega
    · change (Q.colouring.colourGraph j).cutSize S+3*(Q.colouring.missingSet S j).card≤3*t
      have hg:=hother j hj
      have hmiss : Q.colouring.missingSet S j=P.colouring.missingSet S j := by
        unfold EdgeColoring.missingSet
        rw [hg]
      rw [hg,hmiss]
      exact h.colour_budget j

end PartialColouring
end SimpleGraph.MultiGraph
