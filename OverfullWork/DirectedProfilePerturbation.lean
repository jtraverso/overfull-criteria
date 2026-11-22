module

public import OverfullWork.DirectedRobustExpansion

@[expose] public section


/-! Directed profiles after moving vertices between parts and deleting arcs. -/
namespace OverfullWork.InducedDigraphSampling

open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Changes to a neighborhood profile are paid by the vertices moved
out of or into the part and by the deleted neighbors. -/
theorem profile_count_perturbation (A B : Finset V) (P Q : V → Prop)
    (hQ : ∀ v, Q v → P v) (g : ℕ)
    (hLoss : ((univ : Finset V).filter (fun v => P v ∧ ¬Q v)).card ≤ g) :
    (A.filter P).card ≤ (B.filter Q).card+(A \ B).card+g ∧
    (B.filter Q).card ≤ (A.filter P).card+(B \ A).card := by
  let C := A.filter P
  let E := B.filter Q
  have hDiff : C \ E ⊆ (A \ B) ∪ univ.filter (fun v => P v ∧ ¬Q v) := by
    intro v hv
    obtain ⟨hc,he⟩ := mem_sdiff.mp hv
    obtain ⟨ha,hp⟩ := mem_filter.mp hc
    by_cases hb : v ∈ B
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hp,fun hq => he (mem_filter.mpr ⟨hb,hq⟩)⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨ha,hb⟩)
  have hRev : E \ C ⊆ B \ A := by
    intro v hv
    obtain ⟨he,hc⟩ := mem_sdiff.mp hv
    obtain ⟨hb,hq⟩ := mem_filter.mp he
    exact mem_sdiff.mpr ⟨hb,fun ha => hc (mem_filter.mpr ⟨ha,hQ v hq⟩)⟩
  have h₁ := card_le_card_sdiff_add_card (s := C) (t := E)
  have h₂ := card_le_card_sdiff_add_card (s := E) (t := C)
  have h₃ := (card_le_card hDiff).trans ((card_union_le _ _).trans (Nat.add_le_add_left hLoss _))
  have h₄ := card_le_card hRev
  change C.card ≤ E.card+(A \ B).card+g ∧ E.card ≤ C.card+(B \ A).card
  omega

/-- Bound the deleted semidegrees of a subgraph by those of a graph
containing all arcs used so far. -/
theorem semidegrees_deleted_le (D U : Digraph V) (v : V) :
    inDegree (D \ (D \ U)) v ≤ inDegree U v ∧
      outDegree (D \ (D \ U)) v ≤ outDegree U v := by
  have hLe : D \ (D \ U) ≤ U := by
    intro x y h
    exact Classical.byContradiction fun hu => h.2 ⟨h.1,hu⟩
  have aux (P Q : V → Prop) (h : ∀ x, P x → Q x) :
      ((univ : Finset V).filter P).card ≤ (univ.filter Q).card :=
    card_le_card fun _ hv => mem_filter.mpr ⟨mem_univ _,h _ (mem_filter.mp hv).2⟩
  exact ⟨aux _ _ (fun _ h => hLe h),aux _ _ (fun _ h => hLe h)⟩

end OverfullWork.InducedDigraphSampling
