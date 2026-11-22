module

public import OverfullWork.OddOrder

@[expose] public section


/-!
# Saturation of odd almost-regular graphs by a complementary matching

An odd-order almost-regular graph below the whole-graph overfull bound
can be completed to equality without changing its maximum degree.
The added edges are a matching on the original deficient vertices.
This completion theorem itself has no density hypothesis.
-/

namespace OverfullWork.Saturation

open SimpleGraph Finset
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem edges_ncard (G : SimpleGraph V) : G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]

theorem deficit_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.maxDegree - G.minDegree ≤ 1) :
    2 * G.edgeFinset.card + (OddOrder.deficit G).card = Fintype.card V * G.maxDegree := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  calc
    _ = ∑ v : V, (G.degree v + if v ∈ OddOrder.deficit G then 1 else 0) := by
      simp [sum_add_distrib]
    _ = ∑ _v : V, G.maxDegree :=
      sum_congr rfl (fun v _ => OddOrder.degree_add_deficit_indicator G hreg v)
    _ = _ := by simp

/-- Too many deficient vertices cannot form a clique. -/
theorem nonadjacent_deficient_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlarge : G.maxDegree < (OddOrder.deficit G).card) :
    ∃ u ∈ OddOrder.deficit G, ∃ v ∈ OddOrder.deficit G, u ≠ v ∧ ¬ G.Adj u v := by
  classical
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (OddOrder.deficit G).card by omega)
  have huD : G.degree u < G.maxDegree := (mem_filter.mp hu).2
  by_contra h
  have hall : ∀ v ∈ OddOrder.deficit G, u ≠ v → G.Adj u v := by
    intro v hv hne
    by_contra hno
    exact h ⟨u, hu, v, hv, hne, hno⟩
  have hsub : (OddOrder.deficit G).erase u ⊆ G.neighborFinset u := by
    intro v hv
    obtain ⟨hne, hv⟩ := mem_erase.mp hv
    rw [mem_neighborFinset]
    exact hall v hv hne.symm
  have hc := card_le_card hsub
  rw [card_erase_of_mem hu, card_neighborFinset_eq_degree] at hc
  omega

/-- Adding an edge changes each degree by at most its endpoint indicator. -/
theorem degree_sup_edge_le (G : SimpleGraph V) [DecidableRel G.Adj] (u v w : V) :
    (G ⊔ edge u v).degree w ≤ G.degree w + (if w = u ∨ w = v then 1 else 0) := by
  classical
  let T : Finset V := if w = u then {v} else if w = v then {u} else ∅
  have hT : T.card ≤ (if w = u ∨ w = v then 1 else 0) := by
    dsimp [T]
    split_ifs <;> simp_all
  have hsub : (G ⊔ edge u v).neighborFinset w ⊆ G.neighborFinset w ∪ T := by
    intro x hx
    rw [mem_neighborFinset, sup_adj, edge_adj] at hx
    rw [mem_union, mem_neighborFinset]
    rcases hx with hx | ⟨hx, _⟩
    · exact Or.inl hx
    · right
      rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [T]
  calc
    _ = ((G ⊔ edge u v).neighborFinset w).card := rfl
    _ ≤ (G.neighborFinset w ∪ T).card := card_le_card hsub
    _ ≤ (G.neighborFinset w).card + T.card := card_union_le _ _
    _ ≤ G.degree w + (if w = u ∨ w = v then 1 else 0) := Nat.add_le_add_left hT _

structure MatchingCompletion (G : SimpleGraph V) [DecidableRel G.Adj] where
  graph : SimpleGraph V
  [decidableAdjacency : DecidableRel graph.Adj]
  contains : G ≤ graph
  maxDegree_eq : graph.maxDegree = G.maxDegree
  almost_regular : graph.maxDegree - graph.minDegree ≤ 1
  saturated : 2 * graph.edgeFinset.card = G.maxDegree * (Fintype.card V - 1)
  matching : OneFactor.IsMatchingGraph (graph \ G)
  in_complement : graph \ G ≤ Gᶜ
  supported : ∀ u v, (graph \ G).Adj u v → u ∈ OddOrder.deficit G ∧ v ∈ OddOrder.deficit G
  edge_count : (graph \ G).edgeFinset.card + G.edgeFinset.card = graph.edgeFinset.card

attribute [instance] MatchingCompletion.decidableAdjacency

/-- Pure completion theorem: no 6/7 or other density assumption is needed. -/
theorem exists_matchingCompletion (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V)) (hreg : G.maxDegree - G.minDegree ≤ 1)
    (hno : 2 * G.edgeFinset.card ≤ G.maxDegree * (Fintype.card V - 1)) :
    Nonempty (MatchingCompletion G) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b => Classical.propDecidable (G.Adj a b)))
  obtain ⟨m, hm⟩ := hn
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let D := G.maxDegree
  let cap := D * m
  have htwocap : 2 * cap = D * (Fintype.card V - 1) := by
    dsimp [cap]
    rw [hm]
    have hsub : 2 * m + 1 - 1 = 2 * m := by omega
    rw [hsub]
    ring
  have hdegreeG (v : V) : D ≤ G.degree v + 1 := by
    have hmin := G.minDegree_le_degree v
    dsimp [D]
    omega
  have hGcap : G.edgeSet.ncard ≤ cap := by
    rw [edges_ncard]
    have hno' : 2 * G.edgeFinset.card ≤ 2 * cap := by rwa [htwocap]
    omega
  let candidates := (univ : Finset (SimpleGraph V)).filter fun H =>
    G ≤ H ∧ (∀ v, H.degree v ≤ D) ∧ H.edgeSet.ncard ≤ cap
  have hGmem : G ∈ candidates := by
    exact mem_filter.mpr ⟨mem_univ _, le_rfl, G.degree_le_maxDegree, hGcap⟩
  obtain ⟨H, hHmem, hmaximal⟩ := candidates.exists_max_image (fun H => H.edgeSet.ncard) ⟨G, hGmem⟩
  obtain ⟨_, hGH, hupper, hcap⟩ := mem_filter.mp hHmem
  rw [edges_ncard] at hcap
  have hmax : H.maxDegree = D :=
    le_antisymm (maxDegree_le_of_forall_degree_le H D hupper) (maxDegree_mono hGH)
  have hlower (v : V) : D ≤ H.degree v + 1 :=
    (hdegreeG v).trans (Nat.add_le_add_right (degree_le_of_le hGH) 1)
  have hregH : H.maxDegree - H.minDegree ≤ 1 := by
    obtain ⟨v, hv⟩ := H.exists_minimal_degree_vertex
    have h := hlower v
    rw [← hv, ← hmax] at h
    omega
  have hsat : H.edgeFinset.card = cap := by
    by_contra hne
    have hlt : H.edgeFinset.card < cap := by omega
    have hbudget := deficit_budget H hregH
    have hsplit : Fintype.card V * D = 2 * cap + D := by
      dsimp [cap]
      rw [hm]
      ring
    rw [hmax, hsplit] at hbudget
    have hlarge : H.maxDegree < (OddOrder.deficit H).card := by rw [hmax]; omega
    obtain ⟨u, hu, v, hv, huv, hnoadj⟩ := nonadjacent_deficient_pair H hlarge
    have huD : H.degree u < D := by simpa only [hmax] using (mem_filter.mp hu).2
    have hvD : H.degree v < D := by simpa only [hmax] using (mem_filter.mp hv).2
    have hnewupper (w : V) : (H ⊔ edge u v).degree w ≤ D := by
      have h := degree_sup_edge_le H u v w
      by_cases hw : w = u ∨ w = v
      · rw [if_pos hw] at h
        rcases hw with rfl | rfl <;> omega
      · rw [if_neg hw] at h
        have hwD := hupper w
        omega
    have hnewcard : (H ⊔ edge u v).edgeSet.ncard = H.edgeSet.ncard + 1 := by
      rw [edgeSet_sup, edgeSet_edge_of_ne huv, Set.union_singleton]
      exact Set.ncard_insert_of_notMem hnoadj
    have hlt' : H.edgeSet.ncard < cap := by rwa [edges_ncard]
    have hnewmem : H ⊔ edge u v ∈ candidates :=
      mem_filter.mpr ⟨mem_univ _, hGH.trans le_sup_left, hnewupper, by omega⟩
    have hbound := hmaximal (H ⊔ edge u v) hnewmem
    omega
  have hdiff (w : V) : (H \ G).degree w ≤ 1 := by
    have heq := Plantholt.degree_sdiff_add (G := H) hGH w
    have hup := hupper w
    have hlo := hdegreeG w
    omega
  refine ⟨{
    graph := H
    contains := hGH
    maxDegree_eq := hmax
    almost_regular := hregH
    saturated := by rw [hsat]; exact htwocap
    matching := ?_
    in_complement := ?_
    supported := ?_
    edge_count := ?_ }⟩
  · intro w a b ha hb
    have hc : ((H \ G).neighborFinset w).card ≤ 1 := hdiff w
    exact (card_le_one.mp hc) a (by rwa [mem_neighborFinset]) b (by rwa [mem_neighborFinset])
  · intro u v huv
    rw [compl_adj]
    exact ⟨(H \ G).ne_of_adj huv, ((sdiff_adj H G u v).mp huv).2⟩
  · intro u v huv
    have hposu : 0 < (H \ G).degree u := (degree_pos_iff_exists_adj _ _).mpr ⟨v, huv⟩
    have hposv : 0 < (H \ G).degree v := (degree_pos_iff_exists_adj _ _).mpr ⟨u, huv.symm⟩
    have heu := Plantholt.degree_sdiff_add (G := H) hGH u
    have hev := Plantholt.degree_sdiff_add (G := H) hGH v
    have hup := hupper u
    have hvp := hupper v
    constructor <;> apply mem_filter.mpr <;> refine ⟨mem_univ _, ?_⟩ <;> change _ < D <;> omega
  · rw [edgeFinset_sdiff]
    exact card_sdiff_add_card_eq_card (edgeFinset_mono hGH)

theorem MatchingCompletion.union_eq {G : SimpleGraph V} [DecidableRel G.Adj]
    (w : MatchingCompletion G) : G ⊔ (w.graph \ G) = w.graph := by
  ext u v
  simp only [sup_adj, sdiff_adj]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact w.contains h
    · exact h
  · intro h
    by_cases hG : G.Adj u v
    · exact Or.inl hG
    · exact Or.inr ⟨h, hG⟩

/-- The matching has exactly the required edge deficit (without integer division). -/
theorem MatchingCompletion.exact_deficit {G : SimpleGraph V} [DecidableRel G.Adj]
    (w : MatchingCompletion G) :
    2 * (w.graph \ G).edgeFinset.card + 2 * G.edgeFinset.card =
      G.maxDegree * (Fintype.card V - 1) := by
  have hcount := w.edge_count
  have hsat := w.saturated
  omega

/-- The saturation equality from the previous gate is replaced by an inequality. -/
theorem edgeColourable_of_dense_odd_almostRegular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V)) (hreg : G.maxDegree - G.minDegree ≤ 1)
    (hno : 2 * G.edgeFinset.card ≤ G.maxDegree * (Fintype.card V - 1))
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree) :
    G.EdgeColorable G.maxDegree := by
  classical
  obtain ⟨w⟩ := exists_matchingCompletion G hn hreg hno
  have hedges : 2 * w.graph.edgeFinset.card = w.graph.maxDegree * (Fintype.card V - 1) := by
    rw [w.maxDegree_eq]
    exact w.saturated
  have hdense' : 6 * (Fintype.card V + 1) ≤ 7 * w.graph.maxDegree := by
    rwa [w.maxDegree_eq]
  have hc := OddOrder.edgeColourable_of_dense_odd_almostRegular w.graph hn w.almost_regular hedges hdense'
  rw [w.maxDegree_eq] at hc
  exact Critical.colourable_of_copy (Copy.ofLE G w.graph w.contains) hc

/-- In this dense odd almost-regular range, the whole-graph edge bound is exact. -/
theorem dense_odd_almostRegular_criterion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V)) (hreg : G.maxDegree - G.minDegree ≤ 1)
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree) :
    G.EdgeColorable G.maxDegree ↔
      2 * G.edgeFinset.card ≤ G.maxDegree * (Fintype.card V - 1) := by
  constructor
  · intro hc
    classical
    cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
      (fun a b => Classical.propDecidable (G.Adj a b)))
    have h := Plantholt.two_mul_eIn_le_of_colorable (G := G) hc (S := univ) (by simpa using hn)
    simpa [Plantholt.eIn_univ] using h
  · exact fun hno => edgeColourable_of_dense_odd_almostRegular G hn hreg hno hdense

/-- In this family every class-two graph is itself overfull, not merely
a graph containing an overfull subgraph. Uses the registered overfull predicate. -/
theorem dense_odd_classTwo_iff_overfull
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Odd (Fintype.card V)) (hreg : G.maxDegree - G.minDegree ≤ 1)
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree) :
    ¬ G.EdgeColorable G.maxDegree ↔ Overfull.IsOverfull G := by
  rw [dense_odd_almostRegular_criterion G hn hreg hdense]
  unfold Overfull.IsOverfull
  obtain ⟨m, hm⟩ := hn
  have hhalf : Fintype.card V / 2 = m := by omega
  have hmul : G.maxDegree * (Fintype.card V - 1) = 2 * (G.maxDegree * m) := by
    rw [hm]
    have hsub : 2 * m + 1 - 1 = 2 * m := by omega
    rw [hsub]
    ring
  rw [hhalf, hmul]
  omega

namespace Example

/-- Remove a 27-cycle and a disjoint-endpoint 13-edge matching from K27.
Vertex 26 has degree 24; all the other vertices have degree 23. -/
def graph : SimpleGraph (Fin 27) where
  Adj u v := u ≠ v ∧ ¬ (
    (u.val + 1) % 27 = v.val ∨ (v.val + 1) % 27 = u.val ∨
    (u.val < 13 ∧ v.val = u.val + 13) ∨ (v.val < 13 ∧ u.val = v.val + 13))
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    intro h'
    apply h.2
    rcases h' with h' | h' | h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr h'))
    · exact Or.inr (Or.inr (Or.inl h'))⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel graph.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ¬ (
    (u.val + 1) % 27 = v.val ∨ (v.val + 1) % 27 = u.val ∨
    (u.val < 13 ∧ v.val = u.val + 13) ∨ (v.val < 13 ∧ u.val = v.val + 13))))

theorem degree_formula (v : Fin 27) : graph.degree v = if v = 26 then 24 else 23 := by
  have h : ∀ v : Fin 27, graph.degree v = if v = 26 then 24 else 23 := by decide
  exact h v

theorem max_degree : graph.maxDegree = 24 := by decide
theorem min_degree : graph.minDegree = 23 := by decide

theorem edge_count : graph.edgeFinset.card = 311 := by
  have hsum : (∑ v : Fin 27, graph.degree v) = 622 := by
    simp_rw [degree_formula]
    decide
  have hh := graph.sum_degrees_eq_twice_card_edges
  omega

/-- Strictly below saturation, but exactly at the 6/7 degree threshold. -/
theorem hypotheses : Odd (Fintype.card (Fin 27)) ∧
    graph.maxDegree - graph.minDegree ≤ 1 ∧
    2 * graph.edgeFinset.card < graph.maxDegree * (Fintype.card (Fin 27) - 1) ∧
    6 * (Fintype.card (Fin 27) + 1) = 7 * graph.maxDegree := by
  rw [max_degree, min_degree, edge_count]
  decide

theorem twentyFour_edgeColourable : graph.EdgeColorable 24 := by
  have h := hypotheses
  have hc := edgeColourable_of_dense_odd_almostRegular graph h.1 h.2.1 h.2.2.1.le h.2.2.2.le
  simpa only [max_degree] using hc

theorem one_edge_completion :
    ∃ w : MatchingCompletion graph, (w.graph \ graph).edgeFinset.card = 1 := by
  classical
  have h := hypotheses
  obtain ⟨w⟩ := exists_matchingCompletion graph h.1 h.2.1 h.2.2.1.le
  refine ⟨w, ?_⟩
  have hgap := w.exact_deficit
  rw [max_degree, edge_count] at hgap
  simp only [Fintype.card_fin] at hgap
  omega

end Example

#print axioms deficit_budget
#print axioms nonadjacent_deficient_pair
#print axioms exists_matchingCompletion
#print axioms MatchingCompletion.union_eq
#print axioms MatchingCompletion.exact_deficit
#print axioms edgeColourable_of_dense_odd_almostRegular
#print axioms dense_odd_almostRegular_criterion
#print axioms dense_odd_classTwo_iff_overfull
#print axioms Example.twentyFour_edgeColourable
#print axioms Example.one_edge_completion

end OverfullWork.Saturation
