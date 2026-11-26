module

public import OverfullWork.ChenShanAbsorberCatalogue

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {A B W : Type*}

abbrev OrientedTripartiteEdge (A B W : Type*) :=
  TripartiteVertex A B W × TripartiteVertex A B W

/-- A triangle as three vertices of the associated hypergraph. Each
vertex of that hypergraph represents one oriented graph edge. -/
noncomputable def triangleEdges (t : A × B × W) : Finset (OrientedTripartiteEdge A B W) :=
  {(.inl t.1,.inr (.inl t.2.1)),(.inr (.inl t.2.1),.inr (.inr t.2.2)),(.inr (.inr t.2.2),.inl t.1)}

theorem triangleEdges_card (t : A × B × W) : (triangleEdges t).card = 3 := by
  classical
  simp [triangleEdges,Finset.card_insert_of_notMem]

/-- Two distinct graph edges determine at most one tripartite triangle. -/
theorem triangle_eq_of_two_edges {t u : A × B × W}
    {e f : OrientedTripartiteEdge A B W} (hef : e ≠ f)
    (he : e ∈ triangleEdges t) (hf : f ∈ triangleEdges t)
    (he' : e ∈ triangleEdges u) (hf' : f ∈ triangleEdges u) : t = u := by
  classical
  rcases t with ⟨a,b,w⟩
  rcases u with ⟨a',b',w'⟩
  simp only [triangleEdges,mem_insert,mem_singleton] at he hf
  rcases he with rfl | rfl | rfl <;>
    rcases hf with rfl | rfl | rfl <;>
    simp_all [triangleEdges]

theorem triangleEdges_injective : Function.Injective (triangleEdges : A × B × W → _) := by
  intro t u h
  let e : OrientedTripartiteEdge A B W := (.inl t.1,.inr (.inl t.2.1))
  let f : OrientedTripartiteEdge A B W := (.inr (.inl t.2.1),.inr (.inr t.2.2))
  have hef : e ≠ f := by simp [e,f]
  have he : e ∈ triangleEdges t := by simp [e,triangleEdges]
  have hf : f ∈ triangleEdges t := by simp [f,triangleEdges]
  exact triangle_eq_of_two_edges hef he hf (h ▸ he) (h ▸ hf)

noncomputable def triangleHypergraph (T : Finset (A × B × W)) :
    Finset (Finset (OrientedTripartiteEdge A B W)) :=
  T.map ⟨triangleEdges,triangleEdges_injective⟩

theorem triangleHypergraph_uniform (T : Finset (A × B × W)) :
    ∀ t ∈ triangleHypergraph T, (t : Finset (OrientedTripartiteEdge A B W)).card = 3 := by
  intro t ht
  obtain ⟨u,_,rfl⟩ := mem_map.mp ht
  exact triangleEdges_card u

theorem triangleHypergraph_card (T : Finset (A × B × W)) : (triangleHypergraph T).card = T.card :=
  Finset.card_map _

theorem triangleHypergraph_codegree_le_one (T : Finset (A × B × W))
    (e f : OrientedTripartiteEdge A B W) (h : e ≠ f) :
    ((triangleHypergraph T).filter (fun t => e ∈ t ∧ f ∈ t)).card ≤ 1 := by
  apply card_le_one.mpr
  intro S hS U hU
  obtain ⟨hS,hS'⟩ := mem_filter.mp hS
  obtain ⟨hU,hU'⟩ := mem_filter.mp hU
  obtain ⟨s,_,rfl⟩ := mem_map.mp hS
  obtain ⟨u,_,rfl⟩ := mem_map.mp hU
  exact congrArg triangleEdges (triangle_eq_of_two_edges h hS'.1 hS'.2 hU'.1 hU'.2)

theorem triangleEdges_subset_tripartiteArcs [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}
    {t : A × B × W} (h : E t.1 t.2.1 ∧ L t.1 t.2.2 ∧ R t.2.1 t.2.2) :
    triangleEdges t ⊆ tripartiteArcs E L R := by
  intro e he
  simp only [triangleEdges,mem_insert,mem_singleton] at he
  rcases he with rfl | rfl | rfl <;>
    simp only [mem_tripartiteArcs,tripartiteArc] <;> tauto

theorem triangleHypergraph_degree_eq (T : Finset (A × B × W))
    (e : OrientedTripartiteEdge A B W) :
    ((triangleHypergraph T).filter (fun t => e ∈ t)).card =
      (T.filter (fun t => e ∈ triangleEdges t)).card := by
  rw [triangleHypergraph,filter_map,card_map]
  rfl

end OverfullWork.ChenShan
