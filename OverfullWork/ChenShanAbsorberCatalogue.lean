module

public import OverfullWork.ChenShanTripartiteCycles

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical BigOperators

variable {A B W : Type*}

abbrev TripartiteVertex (A B W : Type*) := A ⊕ (B ⊕ W)
abbrev TripartiteArcSet (A B W : Type*) := Finset (TripartiteVertex A B W × TripartiteVertex A B W)

section
variable [Fintype A] [Fintype B] [Fintype W]

@[simp] theorem mem_tripartiteArcs {E : A → B → Prop} {l : A → W → Prop} {r : B → W → Prop}
    {e : TripartiteVertex A B W × TripartiteVertex A B W} :
    e ∈ tripartiteArcs E l r ↔ tripartiteArc E l r e.1 e.2 := by
  simp [tripartiteArcs]

end

/-- One cycle in the vertex order used by the absorber. -/
structure LabeledTripartiteCycle (C : TripartiteArcSet A B W) where
  length : ℕ
  next : Equiv.Perm (Fin length)
  x : Fin length ↪ A
  y : Fin length ↪ B
  w : Fin length ↪ W
  positive : 0 < length
  card_eq : C.card = 3*length
  arcs : ∀ e, e ∈ C ↔
    (∃ i, e = (Sum.inl (x i), Sum.inr (Sum.inl (y i)))) ∨
    (∃ i, e = (Sum.inr (Sum.inl (y i)), Sum.inr (Sum.inr (w i)))) ∨
    (∃ i, e = (Sum.inr (Sum.inr (w i)), Sum.inl (x (next i))))

variable {C : TripartiteArcSet A B W}

theorem LabeledTripartiteCycle.vertices_mem (D : LabeledTripartiteCycle C)
    {U : Finset (TripartiteVertex A B W)} (hC : C ⊆ U ×ˢ U) (i : Fin D.length) :
    Sum.inl (D.x i) ∈ U ∧ Sum.inr (Sum.inl (D.y i)) ∈ U ∧ Sum.inr (Sum.inr (D.w i)) ∈ U := by
  have h₁ := mem_product.mp (hC ((D.arcs _).mpr (Or.inl ⟨i,rfl⟩)))
  have h₂ := mem_product.mp (hC ((D.arcs _).mpr (Or.inr (Or.inl ⟨i,rfl⟩))))
  exact ⟨h₁.1,h₁.2,h₂.2⟩

theorem LabeledTripartiteCycle.card_le_vertices (D : LabeledTripartiteCycle C)
    {U : Finset (TripartiteVertex A B W)} (hC : C ⊆ U ×ˢ U) : 3*D.length ≤ U.card := by
  let V := (univ.map D.x).disjSum ((univ.map D.y).disjSum (univ.map D.w))
  have hCard : V.card = 3*D.length := by
    simp [V,card_disjSum]
    omega
  rw [← hCard]
  apply card_le_card
  rintro (a | (b | w)) h
  · obtain ⟨i,_,rfl⟩ := mem_map.mp (inl_mem_disjSum.mp h)
    exact (D.vertices_mem hC i).1
  · obtain ⟨i,_,rfl⟩ := mem_map.mp (inl_mem_disjSum.mp (inr_mem_disjSum.mp h))
    exact (D.vertices_mem hC i).2.1
  · obtain ⟨i,_,rfl⟩ := mem_map.mp (inr_mem_disjSum.mp (inr_mem_disjSum.mp h))
    exact (D.vertices_mem hC i).2.2

/-- A balanced remainder admits a labeled partition in the form needed for
placing all absorber copies. The cardinality sum counts every edge once. -/
theorem exists_labeled_tripartite_cycle_partition [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {l : A → W → Prop} {r : B → W → Prop}
    (L : TripartiteArcSet A B W) (hSub : L ⊆ tripartiteArcs E l r) (hBal : ArcBalanced L) :
    ∃ C : List (TripartiteArcSet A B W),
      (∀ i j : Fin C.length, i ≠ j → Disjoint (C.get i) (C.get j)) ∧
      (∀ i : Fin C.length, Nonempty (LabeledTripartiteCycle (C.get i))) ∧
      (∀ e, e ∈ L ↔ ∃ i : Fin C.length, e ∈ C.get i) ∧
      (∑ i : Fin C.length, (C.get i).card) = L.card := by
  obtain ⟨C,hPair,hIsCycle,hCovers,hTotal⟩ := exists_directed_cycle_decomposition L hBal
  refine ⟨C,?_,?_,?_,?_⟩
  · intro i j h
    rcases lt_or_gt_of_ne h with hij | hji
    · exact List.pairwise_iff_get.mp hPair i j hij
    · exact (List.pairwise_iff_get.mp hPair j i hji).symm
  · intro i
    obtain ⟨n,f,hf⟩ := hIsCycle _ (C.get_mem i)
    have hF : cycleArcs n f ⊆ tripartiteArcs E l r := by
      intro e he
      exact hSub ((hCovers e).mpr ⟨C.get i,C.get_mem i,hf ▸ he⟩)
    obtain ⟨k,s,x,y,w,hk,hArcs⟩ := exists_tripartite_cycle_fin_labels n f hF
    have hc : (C.get i).card = 3*k := by rw [← hf,cycleArcs_card,hk]
    exact ⟨⟨k,s,x,y,w,by omega,hc,fun e => hf ▸ hArcs e⟩⟩
  · intro e
    rw [hCovers]
    constructor
    · rintro ⟨F,hF,he⟩
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hF
      exact ⟨i,he⟩
    · rintro ⟨i,hi⟩
      exact ⟨C.get i,C.get_mem i,hi⟩
  · have hMap : List.ofFn (fun i : Fin C.length => (C.get i).card) = C.map Finset.card := by
      change List.ofFn (Finset.card ∘ C.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    rw [← List.sum_ofFn,hMap,hTotal]

end OverfullWork.ChenShan
