module

public import OverfullWork.OddCutDeficit
public import OverfullWork.RobustExpansionFinite

@[expose] public section


/-! # Packing disjoint odd sets of maximum-degree vertices

No-overfull gives a full Delta units of boundary at every odd all-maximum
set. If all those boundaries lead into U, their disjointness pays for
each such set using one vertex of U. This is a counting input to Tutte,
not a colouring or a matching-preserving-no-overfull assertion.
-/
namespace OverfullWork.MaximumOddCutPacking
open SimpleGraph Finset PrunedCore
open scoped Classical
variable {V I : Type*} [Fintype V] [DecidableEq V]

theorem maximum_set_cut_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hno : ¬G.HasOverfullSubgraph) (S : Finset V) (hodd : Odd S.card)
    (hmax : ∀v∈S,G.degree v=G.maxDegree) :
    G.maxDegree≤OddCutDeficit.cutEdges G S := by
  have h := (OddCutDeficit.no_overfull_iff_odd_cut_deficit G).mp hno S hodd
  have hz : OddCutDeficit.deficitMass G G.maxDegree S=0 := by
    apply sum_eq_zero
    intro v hv
    rw [hmax v hv,Nat.sub_self]
  simpa only [hz,Nat.add_zero] using h

theorem cut_eq_sum_neighboursIn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S U : Finset V) (hdis : Disjoint S U)
    (hboundary : ∀x∈S,∀y,G.Adj x y → y∈S ∨ y∈U) :
    OddCutDeficit.cutEdges G S=∑v∈U,neighboursIn G S v := by
  have hp : OddCutDeficit.crossingEdges G S=(S×ˢU).filter (fun p => G.Adj p.1 p.2) := by
    ext p
    simp only [OddCutDeficit.crossingEdges,mem_filter,mem_product,mem_compl]
    constructor
    · rintro ⟨⟨hx,hy⟩,hxy⟩
      exact ⟨⟨hx,(hboundary p.1 hx p.2 hxy).resolve_left hy⟩,hxy⟩
    · rintro ⟨⟨hx,hy⟩,hxy⟩
      exact ⟨⟨hx,fun hh => Finset.disjoint_left.mp hdis hh hy⟩,hxy⟩
  rw [OddCutDeficit.cutEdges,hp,card_filter,sum_product,sum_comm]
  apply sum_congr rfl
  intro v _
  rw [RobustExpansion.neighboursIn_eq_filter_card,card_filter]
  apply sum_congr rfl
  intro x _
  simp only [G.adj_comm]

theorem sum_neighboursIn_disjoint_le_degree [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : I → Finset V)
    (hdis : ∀i j,i≠j → Disjoint (S i) (S j)) (v : V) :
    (∑i : I,neighboursIn G (S i) v)≤G.degree v := by
  let C : I → Finset V := fun i => (G.neighborFinset v).filter (fun x => x∈S i)
  have hC : (↑(univ : Finset I) : Set I).PairwiseDisjoint C := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    exact Finset.disjoint_left.mp (hdis i j hij) (mem_filter.mp hxi).2 (mem_filter.mp hxj).2
  have hsub : (univ : Finset I).biUnion C⊆G.neighborFinset v := by
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hi).1
  have hc := card_le_card hsub
  rw [card_biUnion hC,card_neighborFinset_eq_degree] at hc
  exact hc

/-- Disjoint odd maximum sets with all boundary edges entering U number
at most |U|. There is no density or criticality hypothesis. -/
theorem card_le_boundary [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hD : 0<G.maxDegree)
    (hno : ¬G.HasOverfullSubgraph) (S : I → Finset V) (U : Finset V)
    (hodd : ∀i,Odd (S i).card) (hmax : ∀i,∀v∈S i,G.degree v=G.maxDegree)
    (hdis : ∀i j,i≠j → Disjoint (S i) (S j))
    (hU : ∀i,Disjoint (S i) U)
    (hboundary : ∀i,∀x∈S i,∀y,G.Adj x y → y∈S i ∨ y∈U) :
    Fintype.card I≤U.card := by
  have hcut : G.maxDegree*Fintype.card I≤∑i : I,OddCutDeficit.cutEdges G (S i) := by
    calc
      _ = ∑_i : I,G.maxDegree := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum (fun i _ => maximum_set_cut_lower G hno (S i) (hodd i) (hmax i))
  have htotal : (∑i : I,OddCutDeficit.cutEdges G (S i))≤G.maxDegree*U.card := by
    calc
      _ = ∑i : I,∑v∈U,neighboursIn G (S i) v := by
        apply sum_congr rfl
        intro i _
        exact cut_eq_sum_neighboursIn G (S i) U (hU i) (hboundary i)
      _ = ∑v∈U,∑i : I,neighboursIn G (S i) v := sum_comm
      _ ≤ ∑v∈U,G.degree v := sum_le_sum (fun v _ => sum_neighboursIn_disjoint_le_degree G S hdis v)
      _ ≤ ∑_v∈U,G.maxDegree := sum_le_sum (fun v _ => G.degree_le_maxDegree v)
      _ = _ := by simp [Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left (hcut.trans htotal) hD

end OverfullWork.MaximumOddCutPacking
