module

public import OverfullWork.EligibleMatching
public import OverfullWork.PartialColouring

@[expose] public section


/-! # Available crossing neighbours, counting parallel copies correctly -/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def neighboursInto (M : MultiGraph V) (S : Finset V) (v : V) : Finset V :=
  S.filter (fun w => 0<M.mult s(v,w))

theorem degreeInto_le_mul_neighbours (M : MultiGraph V) (S : Finset V) (v : V) (K : ℕ)
    (hmu : ∀ w∈S,M.mult s(v,w)≤K) :
    M.degreeInto S v≤K*(M.neighboursInto S v).card := by
  simp only [degreeInto,neighboursInto,card_eq_sum_ones,sum_filter,mul_sum]
  apply sum_le_sum
  intro w hw
  by_cases h : 0<M.mult s(v,w)
  · simpa only [if_pos h,mul_one] using hmu w hw
  · simp only [if_neg h,mul_zero]
    omega

theorem degreeInto_le_neighbours_add_one (M : MultiGraph V) (S : Finset V) (v x : V)
    (hmu : ∀ w,M.mult s(v,w)≤2) (hsimple : ∀ w,w≠x → M.mult s(v,w)≤1) :
    M.degreeInto S v≤(M.neighboursInto S v).card+1 := by
  have hbound : ∀ w∈S,M.mult s(v,w)≤
      (if 0<M.mult s(v,w) then 1 else 0)+(if w=x then 1 else 0) := by
    intro w _
    by_cases hw : w=x
    · subst w
      have h:=hmu x
      simp only [ite_true]
      split_ifs <;> omega
    · have h:=hsimple w hw
      rw [if_neg hw]
      split_ifs <;> omega
  have h:=sum_le_sum hbound
  rw [sum_add_distrib] at h
  have hcard : (∑ w∈S,if 0<M.mult s(v,w) then 1 else 0)=(M.neighboursInto S v).card := by
    simp only [neighboursInto,card_eq_sum_ones,sum_filter]
  have hone : (∑ w∈S,if w=x then 1 else 0)≤1 := by
    simp only [sum_ite_eq']
    split_ifs <;> omega
  rw [hcard] at h
  exact h.trans (Nat.add_le_add_left hone _)

theorem EdgeColoring.degree_le_palette {M : MultiGraph V} {k : ℕ} (C : M.EdgeColoring k) (v : V) :
    M.degree v≤k := by
  rw [←C.sum_colour_degree v]
  have h:=sum_le_sum (s:=univ) (fun i _ => C.colourGraph_degree_le_one i v)
  simpa using h

namespace PartialColouring

variable {M : MultiGraph V} {k : ℕ}

/-- The uncoloured internal degree is the only loss, besides the palette,
in the available crossing degree. -/
theorem crossing_degree_budget (P : M.PartialColouring k) (S : Finset V) (D r : ℕ)
    (hreg : M.IsRegularOfDegree D)
    (hrem : ∀ v,(P.available.internalPart S).degree v≤r) (v : V) :
    D≤k+r+(if v∈S then P.available.degreeInto Sᶜ v else P.available.degreeInto S v) := by
  have hd:=P.available_degree v
  rw [hreg v] at hd
  have hc:=P.colouring.degree_le_palette v
  have hr:=hrem v
  rw [degree_internalPart] at hr
  have hsum:=P.available.degreeInto_add_compl S v
  by_cases hv : v∈S
  · simp only [if_pos hv] at hr ⊢
    omega
  · simp only [if_neg hv] at hr ⊢
    omega

end PartialColouring

end SimpleGraph.MultiGraph

namespace OverfullWork.ShortAugmentSearch

open Finset
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- Removing b ineligible vertices costs at most b neighbours. -/
theorem neighbours_lost (A E : Finset V) (_hE : E⊆A) (N : V → Prop) [DecidablePred N] :
    (A.filter N).card≤(E.filter N).card+(A\E).card := by
  classical
  have hs : A.filter N⊆E.filter N∪(A\E) := by
    intro v hv
    obtain ⟨ha,hn⟩:=mem_filter.mp hv
    by_cases he : v∈E
    · exact mem_union_left _ (mem_filter.mpr ⟨he,hn⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ha,he⟩)
  exact (card_le_card hs).trans (card_union_le _ _)

end OverfullWork.ShortAugmentSearch
