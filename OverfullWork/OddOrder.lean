module

public import OverfullWork.Critical
public import OneFactor.Main67
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section


/-!
# An unconditional dense odd-order special case

If `n` is odd, `Delta - delta <= 1`, `2|E| = Delta(n-1)`, and
`6(n+1) <= 7 Delta`, then the graph is Delta-edge-colourable.

The point-extension construction and deficiency argument are adapted from
`smwangz6r/m6/PointExtension.lean` in the uploaded ZIP. Unlike its final
conditional reduction, this theorem calls the registered 6/7 factorization
proof itself. It has no abstract even-order criterion or predicate `P`.
-/

namespace OverfullWork.OddOrder

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Add one vertex, adjacent precisely to the chosen set. -/
def pointExtend (S : Finset V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | some u, some v => G.Adj u v
    | none, some v => v ∈ S
    | some u, none => u ∈ S
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact G.symm.symm _ _ h⟩
  loopless := ⟨by
    intro a
    cases a
    · exact id
    · exact G.loopless.irrefl _⟩

instance (S : Finset V) : DecidableRel (pointExtend G S).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp only [pointExtend] <;> infer_instance

theorem neighbours_none (S : Finset V) :
    (pointExtend G S).neighborFinset none = S.image some := by
  ext w
  simp only [mem_neighborFinset]
  cases w <;> simp [pointExtend]

theorem neighbours_some (S : Finset V) (v : V) :
    (pointExtend G S).neighborFinset (some v) =
      (G.neighborFinset v).image some ∪ (if v ∈ S then {none} else ∅) := by
  ext w
  simp only [mem_neighborFinset]
  cases w <;> by_cases hv : v ∈ S <;> simp [pointExtend, hv]

theorem degree_none (S : Finset V) : (pointExtend G S).degree none = S.card := by
  rw [degree, neighbours_none]
  exact card_image_of_injective S (Option.some_injective V)

theorem degree_some (S : Finset V) (v : V) :
    (pointExtend G S).degree (some v) = G.degree v + (if v ∈ S then 1 else 0) := by
  rw [degree, neighbours_some]
  have hd : Disjoint ((G.neighborFinset v).image some) (if v ∈ S then {none} else ∅) := by
    by_cases hv : v ∈ S
    · rw [if_pos hv]
      exact Finset.disjoint_singleton_right.mpr (by simp)
    · rw [if_neg hv]
      simp
  rw [card_union_of_disjoint hd, card_image_of_injective _ (Option.some_injective V), degree]
  by_cases hv : v ∈ S <;> simp [hv]

/-- The deficient vertices; every such vertex lacks exactly one edge in
the almost-regular case considered below. -/
def deficit : Finset V := univ.filter (fun v => G.degree v < G.maxDegree)

theorem degree_add_deficit_indicator
    (hreg : G.maxDegree - G.minDegree ≤ 1) (v : V) :
    G.degree v + (if v ∈ deficit G then 1 else 0) = G.maxDegree := by
  have hmax := G.degree_le_maxDegree v
  have hmin := G.minDegree_le_degree v
  by_cases hv : v ∈ deficit G
  · have hlt : G.degree v < G.maxDegree := (mem_filter.mp hv).2
    rw [if_pos hv]
    omega
  · have hge : ¬ G.degree v < G.maxDegree := fun h => hv (mem_filter.mpr ⟨mem_univ _, h⟩)
    rw [if_neg hv]
    omega

/-- Saturation of the odd-set edge bound forces exactly Delta deficient vertices. -/
theorem card_deficit_of_saturated (hn : 1 ≤ Fintype.card V)
    (hreg : G.maxDegree - G.minDegree ≤ 1)
    (hedges : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1)) :
    (deficit G).card = G.maxDegree := by
  have hsum : (∑ v : V, G.degree v) + (deficit G).card =
      Fintype.card V * G.maxDegree := by
    calc
      _ = ∑ v : V, (G.degree v + if v ∈ deficit G then 1 else 0) := by
        simp [sum_add_distrib]
      _ = ∑ _v : V, G.maxDegree :=
        sum_congr rfl (fun v _ => degree_add_deficit_indicator G hreg v)
      _ = _ := by simp
  rw [G.sum_degrees_eq_twice_card_edges, hedges] at hsum
  have hsplit : G.maxDegree * (Fintype.card V - 1) + G.maxDegree =
      Fintype.card V * G.maxDegree := by
    have hn' : Fintype.card V - 1 + 1 = Fintype.card V := by omega
    calc
      _ = G.maxDegree * (Fintype.card V - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [hn', Nat.mul_comm]
  omega

theorem regular_extension (hn : 1 ≤ Fintype.card V)
    (hreg : G.maxDegree - G.minDegree ≤ 1)
    (hedges : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1)) :
    (pointExtend G (deficit G)).IsRegularOfDegree G.maxDegree := by
  intro w
  cases w with
  | none => exact (degree_none G _).trans (card_deficit_of_saturated G hn hreg hedges)
  | some v => exact (degree_some G _ v).trans (degree_add_deficit_indicator G hreg v)

/-- The original graph is a copy of its one-vertex extension. -/
def intoExtension (S : Finset V) : Copy G (pointExtend G S) :=
  ⟨⟨Option.some, fun h => h⟩, Option.some_injective V⟩

/-- Unconditional closure of the saturated almost-regular odd-order case.
The only assumptions are the four displayed elementary hypotheses. -/
theorem edgeColourable_of_dense_odd_almostRegular
    (hn : Odd (Fintype.card V))
    (hreg : G.maxDegree - G.minDegree ≤ 1)
    (hedges : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1))
    (hdense : 6 * (Fintype.card V + 1) ≤ 7 * G.maxDegree) :
    G.EdgeColorable G.maxDegree := by
  classical
  obtain ⟨m, hm⟩ := hn
  have hnpos : 1 ≤ Fintype.card V := by omega
  have hcard : Fintype.card (Option V) = 2 * (m + 1) := by
    rw [Fintype.card_option]
    omega
  have hd : 12 * (m + 1) ≤ 7 * G.maxDegree := by omega
  have hregular := regular_extension G hnpos hreg hedges
  have hc : (pointExtend G (deficit G)).lineGraph.Colorable G.maxDegree :=
    OneFactor.colorable_of_regular67 hcard (fun v => by convert hregular v) hd
  exact Critical.colourable_of_copy (intoExtension G (deficit G)) hc

namespace Example

/-- K13 with six independent edges removed: (0,1), (2,3), ..., (10,11). -/
def graph : SimpleGraph (Fin 13) where
  Adj u v := u ≠ v ∧ ¬ (u.val < 12 ∧ v.val < 12 ∧ u.val / 2 = v.val / 2)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 ⟨h'.2.1, h'.1, h'.2.2.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel graph.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ¬ (u.val < 12 ∧ v.val < 12 ∧ u.val / 2 = v.val / 2)))

theorem max_degree : graph.maxDegree = 12 := by decide
theorem min_degree : graph.minDegree = 11 := by decide
theorem edge_count : graph.edgeFinset.card = 72 := by decide

/-- This nonempty example reaches equality in the 6/7 threshold after extension. -/
theorem hypotheses : Odd (Fintype.card (Fin 13)) ∧
    graph.maxDegree - graph.minDegree ≤ 1 ∧
    2 * graph.edgeFinset.card = graph.maxDegree * (Fintype.card (Fin 13) - 1) ∧
    6 * (Fintype.card (Fin 13) + 1) = 7 * graph.maxDegree := by
  rw [max_degree, min_degree, edge_count]
  decide

theorem twelve_edgeColourable : graph.EdgeColorable 12 := by
  have h := hypotheses
  have hc := edgeColourable_of_dense_odd_almostRegular graph h.1 h.2.1 h.2.2.1 h.2.2.2.le
  simpa only [max_degree] using hc

end Example

#print axioms regular_extension
#print axioms edgeColourable_of_dense_odd_almostRegular
#print axioms Example.twelve_edgeColourable

end OverfullWork.OddOrder
