module

public import OverfullWork.MultigraphCuts
public import OverfullWork.SimpleColouringBridge

@[expose] public section


/-! # Exact odd-cut budgets with arbitrary degree deficits

An unordered crossing edge has a unique orientation from S to its complement.
The cut budget is this crossing count plus the degree deficit inside S.
-/
namespace OverfullWork.OddCutDeficit
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def internalEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset⊆S).card

def crossingEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (V×V) := (S×ˢSᶜ).filter fun p => G.Adj p.1 p.2

def cutEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (crossingEdges G S).card

def deficitMass (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (S : Finset V) : ℕ :=
  ∑ v∈S,(D-G.degree v)

def oddCutSlack (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (S : Finset V) : ℤ :=
  (cutEdges G S:ℤ)+(deficitMass G D S:ℤ)-(D:ℤ)

theorem internalEdges_eq_multigraph (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    internalEdges G S=(MultiGraph.ofSimpleGraph G).edgesWithin S := by
  simp only [internalEdges,MultiGraph.edgesWithin,MultiGraph.edgeCount,
    MultiGraph.restrict,MultiGraph.ofSimpleGraph,Finset.card_eq_sum_ones,Finset.sum_filter]
  have hEF : G.edgeFinset=univ.filter (fun e => e∈G.edgeSet) := by
    ext e
    simp only [mem_edgeFinset,mem_filter,mem_univ,true_and]
  rw [hEF,Finset.sum_filter]
  apply sum_congr rfl
  intro e he
  split_ifs <;> simp_all

theorem cutEdges_eq_multigraph (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutEdges G S=(MultiGraph.ofSimpleGraph G).cutSize S := by
  simp only [cutEdges,crossingEdges,Finset.card_eq_sum_ones,Finset.sum_filter,
    Finset.sum_product,MultiGraph.cutSize,MultiGraph.ofSimpleGraph,mem_edgeSet]

theorem internal_cut_identity (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    2*internalEdges G S+cutEdges G S=∑v∈S,G.degree v := by
  have h:=(MultiGraph.ofSimpleGraph G).sum_degree_eq_internal_add_cut S
  simp_rw [MultiGraph.degree_ofSimpleGraph] at h
  rw [MultiGraph.twiceInternal_eq,←internalEdges_eq_multigraph,←cutEdges_eq_multigraph] at h
  exact h.symm

theorem internal_cut_deficit_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀v,G.degree v≤D) (S : Finset V) :
    2*internalEdges G S+cutEdges G S+deficitMass G D S=D*S.card := by
  rw [internal_cut_identity,deficitMass,←sum_add_distrib]
  calc
    _ = ∑_v∈S,D := sum_congr rfl (fun v _ => Nat.add_sub_of_le (hD v))
    _ = _ := by simp [Nat.mul_comm]

theorem odd_internal_bound_iff_cut_deficit (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀v,G.degree v≤D) (S : Finset V) (hodd : Odd S.card) :
    internalEdges G S≤D*(S.card/2) ↔ D≤cutEdges G S+deficitMass G D S := by
  have hid:=internal_cut_deficit_identity G D hD S
  obtain ⟨m,hm⟩:=hodd
  have hh : S.card/2=m := by omega
  have he : D*S.card=2*(D*m)+D := by rw [hm];ring
  rw [hh]
  rw [he] at hid
  omega

theorem even_internal_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀v,G.degree v≤D) (S : Finset V) (heven : Even S.card) :
    internalEdges G S≤D*(S.card/2) := by
  have hid:=internal_cut_deficit_identity G D hD S
  obtain ⟨m,hm⟩:=heven
  have hh : S.card/2=m := by omega
  have he : D*S.card=2*(D*m) := by rw [hm];ring
  rw [he] at hid
  rw [hh]
  omega

theorem no_overfull_iff_odd_cut_deficit (G : SimpleGraph V) [DecidableRel G.Adj] :
    (¬G.HasOverfullSubgraph) ↔
      ∀S : Finset V,Odd S.card → G.maxDegree≤cutEdges G S+deficitMass G G.maxDegree S := by
  constructor
  · intro hno S hodd
    apply (odd_internal_bound_iff_cut_deficit G G.maxDegree G.degree_le_maxDegree S hodd).mp
    by_contra hn
    exact hno ⟨S,Nat.lt_of_not_ge hn⟩
  · intro hbudget
    rintro ⟨S,hS⟩
    by_cases hodd : Odd S.card
    · have hb:=(odd_internal_bound_iff_cut_deficit G G.maxDegree G.degree_le_maxDegree S hodd).mpr
        (hbudget S hodd)
      exact (not_lt_of_ge hb) hS
    · have hb:=even_internal_bound G G.maxDegree G.degree_le_maxDegree S
        (Nat.not_odd_iff_even.mp hodd)
      exact (not_lt_of_ge hb) hS

theorem no_overfull_iff_nonnegative_odd_slack (G : SimpleGraph V) [DecidableRel G.Adj] :
    (¬G.HasOverfullSubgraph) ↔ ∀S : Finset V,Odd S.card → 0≤oddCutSlack G G.maxDegree S := by
  rw [no_overfull_iff_odd_cut_deficit]
  constructor
  · intro h S hodd
    have hh:=h S hodd
    unfold oddCutSlack
    omega
  · intro h S hodd
    have hh:=h S hodd
    unfold oddCutSlack at hh
    omega

end OverfullWork.OddCutDeficit
