module

public import OverfullWork.CMSOperation41CorePacking
public import OverfullWork.EdgeImageMultigraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

@[expose] public section


/-! Two-colour layers after projection of a cyclic configuration.
The physical vertices are embedded in the ambient graph, and degrees
are transported at the retained vertices and vanish elsewhere. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem map_degree_at_embedding (H : SimpleGraph W) [DecidableRel H.Adj] (w : W ↪ V) [dMap : DecidableRel (H.map w).Adj] (i : W) :
    (H.map w).degree (w i) = H.degree i := by
  rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
  have hN : (H.map w).neighborFinset (w i) = (H.neighborFinset i).image w := by
    ext z
    rw [mem_neighborFinset,map_adj,mem_image]
    constructor
    · rintro ⟨i',j,hAdj,hi,hj⟩
      have he := w.injective hi
      subst i'
      exact ⟨j,(mem_neighborFinset H i j).mpr hAdj,hj⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨i,j,(mem_neighborFinset H i j).mp hj,rfl,rfl⟩
  rw [hN,card_image_of_injective _ w.injective]

theorem map_degree_outside_embedding (H : SimpleGraph W) (w : W ↪ V) [dMap : DecidableRel (H.map w).Adj] (v : V)
    (hv : v ∉ Set.range w) : (H.map w).degree v = 0 := by
  rw [←card_neighborFinset_eq_degree]
  apply card_eq_zero.mpr (eq_empty_of_forall_notMem ?_)
  intro z hz
  obtain ⟨i,j,_,hi,_⟩ := (map_adj w H v z).mp ((mem_neighborFinset _ _ _).mp hz)
  exact hv ⟨i,hi⟩

theorem simple_colourable_of_copy_colouring (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (C : (MultiGraph.ofSimpleGraph G).EdgeColoring k) : G.EdgeColorable k := by
  have hLoop : ∀ x y,G.Adj x y → id x ≠ id y := fun _ _ h => h.ne
  have hG : EdgeImage.graph G id hLoop = MultiGraph.ofSimpleGraph G := by
    apply MultiGraph.ext_mult
    intro e
    change (EdgeImage.fibre G id e).card = if e ∈ G.edgeSet then 1 else 0
    by_cases he : e ∈ G.edgeSet
    · rw [if_pos he]
      have hh : EdgeImage.fibre G id e = {⟨e,he⟩} := by
        ext t
        simp [EdgeImage.fibre,Subtype.ext_iff]
      rw [hh,card_singleton]
    · rw [if_neg he]
      apply card_eq_zero.mpr
      apply eq_empty_of_forall_notMem
      intro t ht
      have hh := (mem_filter.mp ht).2
      have hz : t.val = e := by simpa using hh
      exact he (hz ▸ t.property)
  apply EdgeImage.colourable_of_image_colouring G id hLoop
  exact hG.symm ▸ C

theorem map_edge_colourable_two_of_bicolouring (H : SimpleGraph W) [DecidableRel H.Adj]
    (w : W ↪ V) (c : H.Coloring Bool) (hD : ∀ i,H.degree i ≤ 2) :
    (H.map w).EdgeColorable 2 := by
  let Q := H.map w
  let A := (univ.filter fun i => c i = true).image w
  have hQ (v : V) : Q.degree v ≤ 2 := by
    by_cases hv : v ∈ Set.range w
    · obtain ⟨i,rfl⟩ := hv
      rw [map_degree_at_embedding H w]
      exact hD i
    · change (H.map w).degree v ≤ 2
      exact (map_degree_outside_embedding H w v hv).le.trans (by decide)
  have hSide (i : W) : w i ∈ A ↔ c i = true := by
    simp [A,w.injective.eq_iff]
  have hB : (MultiGraph.ofSimpleGraph Q).IsBipartiteOn A := by
    intro u v hUV
    by_cases h : s(u,v) ∈ Q.edgeSet
    · obtain ⟨i,j,hij,hi,hj⟩ := (map_adj w H u v).mp ((mem_edgeSet Q).mp h)
      rw [←hi,←hj,hSide,hSide] at hUV
      have hSame : c i = c j := Bool.eq_iff_iff.mpr hUV
      exact (c.valid hij hSame).elim
    · change (if s(u,v) ∈ Q.edgeSet then 1 else 0) = 0
      rw [if_neg h]
  obtain ⟨C⟩ := MultiGraph.exists_edgeColoring_of_bipartite (MultiGraph.ofSimpleGraph Q) A 2
    hB (by intro v; rw [MultiGraph.degree_ofSimpleGraph]; exact hQ v)
  exact simple_colourable_of_copy_colouring Q C

/-- A projected even cycle or a cycle broken at the closing edge
produces a two-colour subgraph on its actual ambient vertices. -/
theorem projected_cycle_or_broken_cycle_layer (G : SimpleGraph V) {n : ℕ}
    (H : SimpleGraph (Fin (n+3))) [DecidableRel H.Adj] (w : Fin (n+3) ↪ V)
    (hEdges : ∀ i j,H.Adj i j → G.Adj (w i) (w j))
    (hCycle : H ≤ cycleGraph (n+3))
    (hParity : Even (n+3) ∨ H ≤ pathGraph (n+3)) :
    ∃ Q : SimpleGraph V, Q = H.map w ∧ Q ≤ G ∧ Q.EdgeColorable 2 ∧
      (∀ i,Q.degree (w i) = H.degree i) ∧
      (∀ v,v ∉ Set.range w → Q.degree v = 0) := by
  let Q := H.map w
  have hLe : Q ≤ G := by
    intro u v h
    obtain ⟨i,j,hij,rfl,rfl⟩ := (map_adj w H u v).mp h
    exact hEdges i j hij
  have hDegree (i : Fin (n+3)) : H.degree i ≤ 2 :=
    (degree_le_of_le hCycle (v := i)).trans (cycleGraph_degree_three_le (v := i)).le
  have hColour : Nonempty (H.Coloring Bool) := by
    rcases hParity with hEven|hPath
    · let C := cycleGraph.bicoloring_of_even (n+3) hEven
      exact ⟨Coloring.mk C (fun h => C.valid (hCycle h))⟩
    · let C := pathGraph.bicoloring (n+3)
      exact ⟨Coloring.mk C (fun h => C.valid (hPath h))⟩
  obtain ⟨c⟩ := hColour
  exact ⟨Q,rfl,hLe,map_edge_colourable_two_of_bicolouring H w c hDegree,
    map_degree_at_embedding H w (dMap := Classical.decRel _),
    map_degree_outside_embedding H w (dMap := Classical.decRel _)⟩

end OverfullWork.CMSTrimmingRound
