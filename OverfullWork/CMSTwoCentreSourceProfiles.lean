module

public import OverfullWork.CMSTwoCentreRobustTransfer

@[expose] public section


/-! Numerical source profiles for the actual two-group quotient. -/
namespace OverfullWork.TwoIndependentIdentifications

open Finset SimpleGraph TwoCentreOrdinaryCore
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem support_degree_loss_at_ordinary (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hInd : G.IsIndepSet (Z : Set V)) (x : Outside Z) :
    G.degree x.val ≤ (graph G Z A hA hInd).supportGraph.degree (Sum.inr x)+Z.card := by
  let M := graph G Z A hA hInd
  have hLoss := ordinary_degree_loss G Z A hA hInd x
  have hMono : (ordinary M).degree x ≤ M.supportGraph.degree (Sum.inr x) := by
    rw [MultiGraph.degree_eq_sum_mult,←MultiGraph.degree_ofSimpleGraph,MultiGraph.degree_eq_sum_mult]
    let H := MultiGraph.ofSimpleGraph M.supportGraph
    have hSub : (∑ y : Outside Z, H.mult s(Sum.inr x,Sum.inr y)) ≤
        ∑ y : Vertices Z, H.mult s(Sum.inr x,y) := by
      rw [Fintype.sum_sum_type]
      exact Nat.le_add_left _ _
    refine (sum_le_sum (fun y _ => ?_)).trans hSub
    rw [ordinary_mult]
    by_cases hxy : 0 < M.mult s(Sum.inr x,Sum.inr y)
    · have hAdj : M.supportGraph.Adj (Sum.inr x) (Sum.inr y) := hxy
      change M.mult s(Sum.inr x,Sum.inr y) ≤ if s(Sum.inr x,Sum.inr y) ∈ M.supportGraph.edgeSet then 1 else 0
      rw [if_pos (M.supportGraph.mem_edgeSet.mpr hAdj)]
      exact mult_inr_le G Z A hA hInd x y
    · exact (Nat.eq_zero_of_not_pos hxy).trans_le (Nat.zero_le _)
  exact hLoss.trans (Nat.add_le_add_right hMono _)

theorem maxDegree_lt_quotient_order_of_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hInd : G.IsIndepSet (Z : Set V)) :
    let M := graph G Z A hA hInd
    let d := G.maxDegree
    (∑ x : Outside Z, (d-G.degree x.val))+M.degree (Sum.inl false)+M.degree (Sum.inl true) <
      Fintype.card (Outside Z) →
    d < Fintype.card (Vertices Z) := by
  intro M d hBudget
  have hRows (i : Bool) :
      (∑ x : Outside Z, M.mult s(Sum.inl i,Sum.inr x)) ≤ M.degree (Sum.inl i) := by
    rw [MultiGraph.degree_eq_sum_mult,Fintype.sum_sum_type]
    exact Nat.le_add_left _ _
  have hV : ∃ x : Outside Z, d-G.degree x.val+
      M.mult s(Sum.inl false,Sum.inr x)+M.mult s(Sum.inl true,Sum.inr x) = 0 := by
    by_contra hn
    push Not at hn
    have hh : Fintype.card (Outside Z) ≤
        (∑ x : Outside Z,(d-G.degree x.val))+M.degree (Sum.inl false)+M.degree (Sum.inl true) := by
      calc
        _ = ∑ _x : Outside Z, (1:ℕ) := by simp
        _ ≤ ∑ x : Outside Z, (d-G.degree x.val+
          M.mult s(Sum.inl false,Sum.inr x)+M.mult s(Sum.inl true,Sum.inr x)) :=
          sum_le_sum (fun x _ => Nat.pos_of_ne_zero (hn x))
        _ ≤ _ := by
          rw [sum_add_distrib,sum_add_distrib]
          exact Nat.add_le_add (Nat.add_le_add_left (hRows false) _) (hRows true)
    omega
  obtain ⟨x,hx⟩ := hV
  have hMax := G.degree_le_maxDegree x.val
  have hRow := M.degree_eq_sum_mult (Sum.inr x)
  have hOrig : M.degree (Sum.inr x) = G.degree x.val := degree_inr G Z A hA hInd x
  rw [hOrig,Fintype.sum_sum_type,Fintype.sum_bool] at hRow
  have hL : M.mult s(Sum.inl false,Sum.inr x) = 0 := by omega
  have hR : M.mult s(Sum.inl true,Sum.inr x) = 0 := by omega
  have hSwap (i : Bool) : M.mult s(Sum.inr x,Sum.inl i) = M.mult s(Sum.inl i,Sum.inr x) :=
    congrArg M.mult Sym2.eq_swap
  rw [hSwap true,hSwap false,hL,hR,zero_add,zero_add] at hRow
  have hSimple : (∑ y : Outside Z,M.mult s(Sum.inr x,Sum.inr y)) ≤ Fintype.card (Outside Z) := by
    calc
      _ ≤ ∑ _y : Outside Z,(1:ℕ) := sum_le_sum (fun y _ => mult_inr_le G Z A hA hInd x y)
      _ = _ := by simp
  rw [Fintype.card_sum,Fintype.card_bool]
  omega

end OverfullWork.TwoIndependentIdentifications
