module

public import OverfullWork.ChenShanTriangleHypergraph
public import OverfullWork.ChenShanDirectedCycles
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V A B W : Type*}

/-- The undirected degree in a consistently oriented edge set. -/
noncomputable def incidentDegree (G : Finset (V × V)) (v : V) : ℕ :=
  (G.filter (fun e => e.1 = v ∨ e.2 = v)).card

theorem incidentDegree_mono {G C : Finset (V × V)} (hC : C ⊆ G) (v : V) :
    incidentDegree C v ≤ incidentDegree G v :=
  card_le_card (filter_subset_filter _ hC)

theorem incidentDegree_sdiff {G C : Finset (V × V)} (hC : C ⊆ G) (v : V) :
    incidentDegree (G \ C) v = incidentDegree G v - incidentDegree C v := by
  let p : V × V → Prop := fun e => e.1 = v ∨ e.2 = v
  have hFilter : (G \ C).filter p = G.filter p \ C.filter p := by
    ext e
    simp only [mem_filter,mem_sdiff]
    tauto
  simp only [incidentDegree]
  change ((G \ C).filter p).card = _
  rw [hFilter,card_sdiff_of_subset (filter_subset_filter p hC)]

theorem triangleEdges_balanced (t : A × B × W) : ArcBalanced (triangleEdges t) := by
  rcases t with ⟨a,b,w⟩
  intro v
  rcases v with x | (y | z)
  · by_cases hx : a = x <;> simp [triangleEdges,filter_insert,filter_singleton,hx]
  · by_cases hy : b = y <;> simp [triangleEdges,filter_insert,filter_singleton,hy]
  · by_cases hz : w = z <;> simp [triangleEdges,filter_insert,filter_singleton,hz]

theorem triangleEdges_incidentDegree_le_two (t : A × B × W) (v : A ⊕ B ⊕ W) :
    incidentDegree (triangleEdges t) v ≤ 2 := by
  rcases t with ⟨a,b,w⟩
  rcases v with x | (y | z)
  · by_cases hx : a = x <;> simp [incidentDegree,triangleEdges,filter_insert,filter_singleton,hx]
  · by_cases hy : b = y <;> simp [incidentDegree,triangleEdges,filter_insert,filter_singleton,hy]
  · by_cases hz : w = z <;> simp [incidentDegree,triangleEdges,filter_insert,filter_singleton,hz]

/-- Counting the incidences with v by hyperedges or by graph edges. -/
theorem sum_incidentDegree_eq_sum_hypergraphDegree
    (G : Finset (V × V)) (H : Finset (Finset (V × V))) (v : V)
    (hSub : ∀ S ∈ H, S ⊆ G) :
    (∑ S ∈ H, incidentDegree S v) =
      ∑ e ∈ G.filter (fun e => e.1 = v ∨ e.2 = v),
        (H.filter (fun S => e ∈ S)).card := by
  simp only [incidentDegree,card_filter]
  have hExtend (S : Finset (V × V)) (hS : S ∈ H) :
      (∑ e ∈ S, if e.1 = v ∨ e.2 = v then (1 : ℕ) else 0) =
        ∑ e ∈ G, if (e.1 = v ∨ e.2 = v) ∧ e ∈ S then 1 else 0 := by
    have hFilter : G.filter (fun e => (e.1 = v ∨ e.2 = v) ∧ e ∈ S) =
        S.filter (fun e => e.1 = v ∨ e.2 = v) := by
      ext e
      simp only [mem_filter]
      aesop
    simp only [← sum_filter]
    rw [hFilter]
  calc
    _ = ∑ S ∈ H, ∑ e ∈ G, if (e.1 = v ∨ e.2 = v) ∧ e ∈ S then (1 : ℕ) else 0 :=
      sum_congr rfl hExtend
    _ = _ := by
      rw [sum_comm,sum_filter]
      apply sum_congr rfl
      intro e _
      by_cases he : e.1 = v ∨ e.2 = v <;> simp [he]

theorem mul_incidentDegree_le_sum_incidentDegree
    (G : Finset (V × V)) (H : Finset (Finset (V × V))) (v : V) (a : ℝ)
    (hSub : ∀ S ∈ H, S ⊆ G) (hLower : ∀ e ∈ G, a ≤ ((H.filter (fun S => e ∈ S)).card : ℝ)) :
    a * incidentDegree G v ≤ ∑ S ∈ H, (incidentDegree S v : ℝ) := by
  rw [← Nat.cast_sum,sum_incidentDegree_eq_sum_hypergraphDegree G H v hSub,Nat.cast_sum]
  let F := G.filter (fun e => e.1 = v ∨ e.2 = v)
  calc
    _ = ∑ _e ∈ F, a := by simp [incidentDegree,F, nsmul_eq_mul, mul_comm]
    _ ≤ _ := sum_le_sum fun e he => hLower e (mem_filter.mp he).1

noncomputable def coveredEdges (M : Finset (Finset (V × V))) : Finset (V × V) :=
  M.biUnion id

noncomputable def packingLeave (G : Finset (V × V)) (M : Finset (Finset (V × V))) :
    Finset (V × V) :=
  G \ coveredEdges M

private theorem card_filter_coveredEdges (M : Finset (Finset (V × V)))
    (hM : ((↑M : Set (Finset (V × V)))).PairwiseDisjoint id)
    (p : V × V → Prop) [DecidablePred p] :
    ((coveredEdges M).filter p).card = ∑ S ∈ M, (S.filter p).card := by
  have hFilter : (coveredEdges M).filter p = M.biUnion (fun S => S.filter p) := by
    ext e
    simp only [coveredEdges,mem_filter,mem_biUnion,id_eq]
    constructor
    · rintro ⟨⟨S,hS,heS⟩,hep⟩
      exact ⟨S,hS,heS,hep⟩
    · rintro ⟨S,hS,heS,hep⟩
      exact ⟨⟨S,hS,heS⟩,hep⟩
  rw [hFilter]
  apply card_biUnion
  intro S hS U hU hNe
  exact (hM hS hU hNe).mono (filter_subset _ _) (filter_subset _ _)

theorem mem_coveredEdges {M : Finset (Finset (V × V))} {e : V × V} :
    e ∈ coveredEdges M ↔ ∃ S ∈ M, e ∈ S := by
  simp [coveredEdges]

theorem coveredEdges_subset {M : Finset (Finset (V × V))} {G : Finset (V × V)}
    (hM : ∀ S ∈ M, S ⊆ G) : coveredEdges M ⊆ G := by
  intro e he
  obtain ⟨S,hS,heS⟩ := mem_coveredEdges.mp he
  exact hM S hS heS

/-- The incidence weight of a matching counts the incident edges it covers. -/
theorem incidentDegree_coveredEdges_eq (M : Finset (Finset (V × V)))
    (hM : ((↑M : Set (Finset (V × V)))).PairwiseDisjoint id) (v : V) :
    incidentDegree (coveredEdges M) v = ∑ S ∈ M, incidentDegree S v := by
  unfold incidentDegree
  exact card_filter_coveredEdges M hM (fun e => e.1 = v ∨ e.2 = v)

/-- A union of edge-disjoint balanced sets is balanced. -/
theorem arcBalanced_coveredEdges (M : Finset (Finset (V × V)))
    (hM : ((↑M : Set (Finset (V × V)))).PairwiseDisjoint id)
    (hBal : ∀ S ∈ M, ArcBalanced S) : ArcBalanced (coveredEdges M) := by
  intro v
  rw [card_filter_coveredEdges M hM,card_filter_coveredEdges M hM]
  exact sum_congr rfl (fun S hS => hBal S hS v)

/-- Removing a packing from a locally balanced tripartite graph preserves local balance. -/
theorem trianglePacking_leave_balanced [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}
    (hb : TripartiteLocallyBalanced E L R) {T : Finset (A × B × W)}
    (hT : ∀ t ∈ T, E t.1 t.2.1 ∧ L t.1 t.2.2 ∧ R t.2.1 t.2.2)
    (hM : ((↑(triangleHypergraph T) : Set (Finset (OrientedTripartiteEdge A B W)))).PairwiseDisjoint id) :
    ArcBalanced (packingLeave (tripartiteArcs E L R) (triangleHypergraph T)) := by
  unfold packingLeave
  apply arcBalanced_sdiff _ (arcBalanced_of_tripartiteLocallyBalanced hb)
    (arcBalanced_coveredEdges _ hM ?_)
  · intro e he
    obtain ⟨S,hS,heS⟩ := mem_coveredEdges.mp he
    obtain ⟨t,ht,rfl⟩ := mem_map.mp hS
    exact triangleEdges_subset_tripartiteArcs (hT t ht) heS
  · intro S hS
    obtain ⟨t,_,rfl⟩ := mem_map.mp hS
    exact triangleEdges_balanced t

end OverfullWork.ChenShan
