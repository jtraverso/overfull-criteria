module

public import OverfullWork.CompletionInvariant

@[expose] public section


namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem five_degree_change (p : Fin 6 ↪ V) (z : V) :
    (fiveAdded p).degree z=(fiveRemoved p).degree z+(if z=p 0 ∨ z=p 5 then 1 else 0) := by
  rw [degree_fiveRemoved,degree_fiveAdded]
  have hneq : ∀ a b : Fin 6,a≠b → p a≠p b:=fun _ _ h => p.injective.ne h
  by_cases hex : ∃ j : Fin 6,z=p j
  · obtain ⟨j,rfl⟩:=hex
    fin_cases j <;> simp [hneq]
  · have hn : ∀ j : Fin 6,z≠p j:=by simpa only [not_exists] using hex
    simp [hn,hex]

namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}
variable (P : M.PartialColouring k) (S Z : Finset V) (i : Fin k) (u v : V)
variable (f : P.SafeFive S Z i u v)
variable (h0 : (P.colouring.colourGraph i).degree u=0) (h5 : (P.colouring.colourGraph i).degree v=0)

theorem perturb_other (j : Fin k) (hj : j≠i) :
    ((P.perturb S Z i u v f h0 h5).colouring.colourGraph j)=P.colouring.colourGraph j :=
  P.exchange_colour_other i _ _ f.remove_le f.add_le (P.safe_five_proper S Z i u v f h0 h5) j hj

theorem perturb_selected :
    ((P.perturb S Z i u v f h0 h5).colouring.colourGraph i)=
      ((P.colouring.colourGraph i).subtractCopies (fiveRemoved f.path)).addCopies (fiveAdded f.path) :=
  P.exchange_colour_selected i _ _ f.remove_le f.add_le (P.safe_five_proper S Z i u v f h0 h5)

theorem perturb_selected_degree (z : V) :
    ((P.perturb S Z i u v f h0 h5).colouring.colourGraph i).degree z=
      (P.colouring.colourGraph i).degree z+(if z=u ∨ z=v then 1 else 0) := by
  rw [P.perturb_selected,degree_addCopies]
  have hd:=degree_subtract_add (P.colouring.colourGraph i) (fiveRemoved f.path) f.remove_le z
  have hc:=five_degree_change f.path z
  rw [f.first,f.last] at hc
  omega

theorem perturb_missing_drop :
    (P.colouring.missingSet S i).card=
      ((P.perturb S Z i u v f h0 h5).colouring.missingSet S i).card+1 := by
  apply P.colouring.missing_drop_of_degree_update
    (P.perturb S Z i u v f h0 h5).colouring S i u v
  · simpa only [f.first] using f.sided.1
  · simpa only [f.last] using f.sided.2.2.2.2.2
  · exact P.perturb_selected_degree S Z i u v f h0 h5

theorem perturb_deficit_drop : P.deficit S=(P.perturb S Z i u v f h0 h5).deficit S+1 := by
  exact P.colouring.total_missing_drop (P.perturb S Z i u v f h0 h5).colouring S i
    (P.perturb_missing_drop S Z i u v f h0 h5)
    (fun j hj => (P.perturb_other S Z i u v f h0 h5 j hj).symm)

theorem five_removed_cross_zero (a : V) (ha : a∈S) (b : V) (hb : b∈Sᶜ) :
    (fiveRemoved f.path).mult s(a,b)=0 := by
  exact cut_mult_eq_zero _ S (five_sided_counts S f.path f.sided).2.2.1 a ha b hb

theorem five_added_internal_zero (e : Sym2 V) (he : e.toFinset⊆S ∨ e.toFinset⊆Sᶜ) :
    (fiveAdded f.path).mult e=0 := by
  rcases he with he|he
  · exact mult_eq_zero_of_edgesWithin_zero _ S (five_sided_counts S f.path f.sided).2.2.2.1 e he
  · exact mult_eq_zero_of_edgesWithin_zero _ Sᶜ (five_sided_counts S f.path f.sided).2.2.2.2.1 e he

theorem perturb_remainder : (P.perturb S Z i u v f h0 h5).remainder S=
    (P.remainder S).addCopies (fiveRemoved f.path) := by
  apply remainder_internal_exchange M P.graph (fiveRemoved f.path) (fiveAdded f.path) S P.le
    (fun e => (f.remove_le e).trans (P.colouring.col_le_mult e i))
  · intro a b hab
    by_cases ha : a∈S
    · have hb : b∈Sᶜ:=mem_compl.mpr (fun hh => hab (by simp [ha,hh]))
      exact P.five_removed_cross_zero S Z i u v f a ha b hb
    · have hb : b∈S:=by by_contra hh; exact hab (by simp [ha,hh])
      rw [Sym2.eq_swap]
      exact P.five_removed_cross_zero S Z i u v f b hb a (mem_compl.mpr ha)
  · intro a b hab
    apply P.five_added_internal_zero S Z i u v f
    by_cases ha : a∈S
    · exact Or.inl (by simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff] using And.intro ha (hab.mp ha))
    · have hb : b∉S:=fun hh => ha (hab.mpr hh)
      exact Or.inr (by simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff] using And.intro (mem_compl.mpr ha) (mem_compl.mpr hb))

theorem perturb_internal_counts :
    ((P.perturb S Z i u v f h0 h5).colouring.colourGraph i).edgesWithin S+1=
      (P.colouring.colourGraph i).edgesWithin S ∧
    ((P.perturb S Z i u v f h0 h5).colouring.colourGraph i).edgesWithin Sᶜ+1=
      (P.colouring.colourGraph i).edgesWithin Sᶜ := by
  have hA:=edgesWithin_exchange (P.colouring.colourGraph i) (fiveRemoved f.path) (fiveAdded f.path) S
    f.remove_le (fun e he => P.five_added_internal_zero S Z i u v f e (Or.inl he))
  have hB:=edgesWithin_exchange (P.colouring.colourGraph i) (fiveRemoved f.path) (fiveAdded f.path) Sᶜ
    f.remove_le (fun e he => P.five_added_internal_zero S Z i u v f e (Or.inr he))
  have hc:=five_sided_counts S f.path f.sided
  rw [hc.1] at hA
  rw [hc.2.1] at hB
  rw [P.perturb_selected]
  exact ⟨hA,hB⟩

theorem perturb_cut : ((P.perturb S Z i u v f h0 h5).colouring.colourGraph i).cutSize S=
    (P.colouring.colourGraph i).cutSize S+3 := by
  rw [P.perturb_selected,cutSize_exchange _ _ _ S
    (P.five_removed_cross_zero S Z i u v f),(five_sided_counts S f.path f.sided).2.2.2.2.2]

end PartialColouring

namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

/-- A local perturbation preserves all four global budgets, including
the small maximum degree of the exact internal remainder. -/
theorem perturb_preserves (P : M.PartialColouring k) (S : Finset V) (x : V) (m t : ℕ)
    (h : P.CompletionInvariant S x m t) (i : Fin k) (u v : V)
    (f : P.SafeFive S (P.forbidden S x t) i u v)
    (h0 : (P.colouring.colourGraph i).degree u=0) (h5 : (P.colouring.colourGraph i).degree v=0) :
    (P.perturb S (P.forbidden S x t) i u v f h0 h5).CompletionInvariant S x m t := by
  let Q:=P.perturb S (P.forbidden S x t) i u v f h0 h5
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
    · have hs:=P.forbidden_remainder_room S x t z (f.safe z hz)
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
