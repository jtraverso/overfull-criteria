module

public import OverfullWork.DirectedPackingPrefix

@[expose] public section


/-! Merge a completed batch with an earlier prefix. The batch is allowed
to use only the host arcs that survived the prefix. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset
open scoped Classical
variable {V I J : Type*} {D : Digraph V} {L : J → Layout V I} {S T : Finset J}

private theorem PackingPrefix.disjoint_of_residual (P : PackingPrefix D L S)
    (Q : PackingPrefix (D \ P.used) L T) (i : S) (j : T) :
    Disjoint (P.round i).used (Q.round j).used := by
  apply disjoint_iff_inf_le.mpr
  intro x y h
  have hP : P.used.Adj x y := le_iSup (fun a : S => (P.round a).used) i h.1
  exact ((Q.round j).used_le h.2).2 hP

/-- Retain the previous configurations and add every layout of a batch
simultaneously, retaining the previous realization at an index of the prefix. -/
noncomputable def PackingPrefix.merge (P : PackingPrefix D L S)
    (Q : PackingPrefix (D \ P.used) L T) : PackingPrefix D L (S ∪ T) where
  round i := if h : i.val ∈ S then P.round ⟨i.val,h⟩ else
    (Q.round ⟨i.val,(mem_union.mp i.prop).resolve_left h⟩).rehost sdiff_le
  disjoint := by
    intro i j hij
    by_cases hi : i.val ∈ S <;> by_cases hj : j.val ∈ S
    · simp only [dif_pos hi,dif_pos hj]
      exact P.disjoint (fun h => hij (Subtype.ext (congrArg (fun k : S => k.val) h)))
    · simp only [dif_pos hi,dif_neg hj]
      exact P.disjoint_of_residual Q ⟨i.val,hi⟩ ⟨j.val,(mem_union.mp j.prop).resolve_left hj⟩
    · simp only [dif_neg hi,dif_pos hj]
      exact (P.disjoint_of_residual Q ⟨j.val,hj⟩ ⟨i.val,(mem_union.mp i.prop).resolve_left hi⟩).symm
    · simp only [dif_neg hi,dif_neg hj]
      let i' : T := ⟨i.val,(mem_union.mp i.prop).resolve_left hi⟩
      let j' : T := ⟨j.val,(mem_union.mp j.prop).resolve_left hj⟩
      have h : i' ≠ j' := fun h => hij (Subtype.ext (congrArg (fun k : T => k.val) h))
      exact Q.disjoint h

theorem PackingPrefix.merge_round_left (P : PackingPrefix D L S)
    (Q : PackingPrefix (D \ P.used) L T) (i : S) :
    (P.merge Q).round ⟨i.val,mem_union_left _ i.prop⟩ = P.round i := by
  simp only [PackingPrefix.merge,dif_pos i.prop]

theorem PackingPrefix.merge_round_right (P : PackingPrefix D L S)
    (Q : PackingPrefix (D \ P.used) L T) (h : Disjoint S T) (i : T) :
    (P.merge Q).round ⟨i.val,mem_union_right _ i.prop⟩ = (Q.round i).rehost sdiff_le := by
  simp only [PackingPrefix.merge,dif_neg (fun hx => disjoint_left.mp h hx i.prop)]

/-- The merged used graph is the exact union, so every later batch can
use the ordinary graph difference to obtain its host. -/
theorem PackingPrefix.used_merge (P : PackingPrefix D L S)
    (Q : PackingPrefix (D \ P.used) L T) (h : Disjoint S T) :
    (P.merge Q).used = P.used ⊔ Q.used := by
  ext x y
  simp only [PackingPrefix.used,Digraph.iSup_adj,Digraph.sup_adj]
  constructor
  · rintro ⟨⟨i,hi⟩,hxy⟩
    rcases mem_union.mp hi with hl | hr
    · left
      exact ⟨⟨i,hl⟩,by simpa only [P.merge_round_left Q ⟨i,hl⟩] using hxy⟩
    · right
      refine ⟨⟨i,hr⟩,?_⟩
      rw [P.merge_round_right Q h ⟨i,hr⟩] at hxy
      exact hxy
  · rintro (⟨i,hi⟩ | ⟨i,hi⟩)
    · exact ⟨⟨i.val,mem_union_left _ i.prop⟩,by simpa only [P.merge_round_left Q i] using hi⟩
    · refine ⟨⟨i.val,mem_union_right _ i.prop⟩,?_⟩
      rw [P.merge_round_right Q h i]
      exact hi

end OverfullWork.DirectedSpanningConfiguration
