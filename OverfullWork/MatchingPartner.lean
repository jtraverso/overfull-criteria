module

public import OverfullWork.DoubleLayers
public import OneFactor.Label67

@[expose] public section


/-! # Partner permutations for a single colour, with exact copy counts -/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mult_pair_le_degree (M : MultiGraph V) (u v : V) :
    M.mult s(u,v)≤M.degree u := by
  rw [degree_eq_sum_mult]
  exact single_le_sum (f:=fun w : V => M.mult s(u,w)) (fun _ _ => Nat.zero_le _) (mem_univ v)

theorem mult_le_one_of_degrees (M : MultiGraph V) (hdeg : ∀ v,M.degree v≤1) :
    ∀ e,M.mult e≤1 := by
  intro e
  induction e using Sym2.inductionOn with
  | hf u v => exact (M.mult_pair_le_degree u v).trans (hdeg u)

theorem supportGraph_degree_of_matching (M : MultiGraph V) (hdeg : ∀ v,M.degree v≤1) (v : V) :
    M.supportGraph.degree v=M.degree v := by
  rw [←degree_ofSimpleGraph,of_supportGraph M (M.mult_le_one_of_degrees hdeg)]

theorem supportGraph_isMatching (M : MultiGraph V) (hdeg : ∀ v,M.degree v≤1) :
    OneFactor.IsMatchingGraph M.supportGraph := by
  apply OneFactor.isMatchingGraph_of_degree
  intro v
  rw [M.supportGraph_degree_of_matching hdeg]
  exact hdeg v

theorem partner_not_covered {G : SimpleGraph V} (v : V) (hv : v∉OneFactor.cover G) :
    OneFactor.partner G v=v := by
  have hn : ¬∃ u,G.Adj v u:=fun h => hv (OneFactor.mem_cover.mpr h)
  simp only [OneFactor.partner,dif_neg hn]

theorem partner_involutive_of_matching (M : MultiGraph V) (hdeg : ∀ v,M.degree v≤1) :
    Function.Involutive (OneFactor.partner M.supportGraph) := by
  intro v
  by_cases hv : v∈OneFactor.cover M.supportGraph
  · exact OneFactor.partner_partner (M.supportGraph_isMatching hdeg) hv
  · rw [partner_not_covered v hv,partner_not_covered v hv]

noncomputable def matchingPartner (M : MultiGraph V) (hdeg : ∀ v,M.degree v≤1) : Equiv.Perm V :=
  (M.partner_involutive_of_matching hdeg).toPerm _

theorem matchingPartner_apply_apply (M : MultiGraph V) (hdeg : ∀ v,M.degree v≤1) (v : V) :
    M.matchingPartner hdeg (M.matchingPartner hdeg v)=v := M.partner_involutive_of_matching hdeg v

theorem matchingPartner_adj (M : MultiGraph V) (hdeg : ∀ v,M.degree v≤1) (v : V)
    (hv : M.degree v=1) : M.mult s(v,M.matchingPartner hdeg v)=1 := by
  have hv' : v∈OneFactor.cover M.supportGraph := by
    by_contra hn
    have hz:=OneFactor.degree_eq_zero_of_not_cover hn
    rw [M.supportGraph_degree_of_matching hdeg,hv] at hz
    omega
  have hadj:=OneFactor.adj_partner hv'
  change 0<M.mult s(v,M.matchingPartner hdeg v) at hadj
  have hu:=M.mult_pair_le_degree v (M.matchingPartner hdeg v)
  omega

theorem matchingPartner_ne (M : MultiGraph V) (hdeg : ∀ v,M.degree v≤1) (v : V)
    (hv : M.degree v=1) : M.matchingPartner hdeg v≠v := by
  intro he
  have h:=M.matchingPartner_adj hdeg v hv
  rw [he,M.loopless s(v,v) (by simp)] at h
  omega

theorem matchingPartner_fixed_of_zero (M : MultiGraph V) (hdeg : ∀ v,M.degree v≤1) (v : V)
    (hv : M.degree v=0) : M.matchingPartner hdeg v=v := by
  apply partner_not_covered
  intro hc
  have h:=OneFactor.degree_eq_one_of_matching (M.supportGraph_isMatching hdeg) hc
  rw [M.supportGraph_degree_of_matching hdeg,hv] at h
  omega

end SimpleGraph.MultiGraph
