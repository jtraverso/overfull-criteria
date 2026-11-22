module

public import OverfullWork.GeneralRegularization

@[expose] public section


/-! # Sharper information at a regularization centre

At a new point, multiplicity towards an old vertex cannot exceed that
vertex's original deficit. At an old centre a pointwise excess bound is
an alternative control. Both are stable when copies are removed.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def CentreControl (M : MultiGraph V) (x : V) (b : ℕ) : Prop :=
  (∀ v,M.mult s(x,v)≤b) ∨ M.parallelExcess x≤b

theorem parallelExcess_mono (M N : MultiGraph V) (hle : ∀ e,N.mult e≤M.mult e) (v : V) :
    N.parallelExcess v≤M.parallelExcess v := by
  apply sum_le_sum
  intro w _
  exact Nat.sub_le_sub_right (hle s(v,w)) 1

theorem centreControl_mono (M N : MultiGraph V) (x : V) (b : ℕ)
    (hle : ∀ e,N.mult e≤M.mult e) (h : M.CentreControl x b) : N.CentreControl x b := by
  rcases h with h|h
  · exact Or.inl (fun v => (hle s(x,v)).trans (h v))
  · exact Or.inr ((M.parallelExcess_mono N hle x).trans h)

theorem degreeInto_le_neighbours_add_excess (M : MultiGraph V) (S : Finset V) (v : V) :
    M.degreeInto S v≤(M.neighboursInto S v).card+M.parallelExcess v := by
  have hp : ∀ w∈S,M.mult s(v,w)≤
      (if 0<M.mult s(v,w) then 1 else 0)+(M.mult s(v,w)-1) := by
    intro w _
    split_ifs <;> omega
  have hs:=sum_le_sum hp
  rw [sum_add_distrib] at hs
  have hc : (∑ w∈S,if 0<M.mult s(v,w) then 1 else 0)=(M.neighboursInto S v).card:=by
    simp only [neighboursInto,card_eq_sum_ones,sum_filter]
  have he : (∑ w∈S,(M.mult s(v,w)-1))≤M.parallelExcess v:=
    sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  rw [hc] at hs
  exact hs.trans (Nat.add_le_add_left he _)

theorem degreeInto_le_scaled_neighbours (M : MultiGraph V) (S : Finset V) (x v : V)
    (b : ℕ) (hb : 1≤b) (hbudget : M.HasParallelBudget x b) (hcentre : M.CentreControl x b) :
    M.degreeInto S v≤b*(M.neighboursInto S v).card+b := by
  have hsmall (he : M.parallelExcess v≤b) : M.degreeInto S v≤b*(M.neighboursInto S v).card+b := by
    have hc : (M.neighboursInto S v).card≤b*(M.neighboursInto S v).card:=by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (M.neighboursInto S v).card hb
    exact (M.degreeInto_le_neighbours_add_excess S v).trans (Nat.add_le_add hc he)
  by_cases hv : v=x
  · subst v
    rcases hcentre with hcap|he
    · exact (M.degreeInto_le_mul_neighbours S x b (fun w _ => hcap w)).trans (Nat.le_add_right _ _)
    · exact hsmall he
  · exact hsmall (hbudget v hv)

end SimpleGraph.MultiGraph

namespace OverfullWork.GeneralRegularization
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- This holds for any regular extension containing G, not just the
particular realization chosen in the regularization construction. -/
theorem centre_mult_le_deficit (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : MultiGraph (Option V)) (D : ℕ) (hreg : M.IsRegularOfDegree D)
    (hcontains : ∀ u v,G.Adj u v → 1≤M.mult s(some u,some v)) (v : V) :
    M.mult s(none,some v)≤D-G.degree v := by
  have hsum : G.degree v≤∑ w : V,M.mult s(some v,some w) := by
    rw [←MultiGraph.degree_ofSimpleGraph,MultiGraph.degree_eq_sum_mult]
    apply sum_le_sum
    intro w _
    change (if s(v,w)∈G.edgeSet then 1 else 0)≤_
    simp only [mem_edgeSet]
    split_ifs with h
    · exact hcontains v w h
    · exact Nat.zero_le _
  have hh:=M.degree_eq_sum_mult (some v)
  rw [hreg (some v),Fintype.sum_option] at hh
  have he : M.mult s(none,some v)=M.mult s(some v,none):=by rw [Sym2.eq_swap]
  omega

end OverfullWork.GeneralRegularization
