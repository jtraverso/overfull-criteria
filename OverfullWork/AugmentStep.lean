module

public import OverfullWork.ShortAugmentSearch
public import OverfullWork.AvailableNeighbours

@[expose] public section


/-! # A proved augmentation step from explicit expansion inequalities -/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fiveRemoved_le_of_edges (Q : MultiGraph V) (p : Fin 6 ↪ V)
    (h12 : 1≤Q.mult s(p 1,p 2)) (h34 : 1≤Q.mult s(p 3,p 4)) :
    ∀ e,(fiveRemoved p).mult e≤Q.mult e := by
  have hb : ∀ e,(fiveRemoved p).mult e≤1 := by
    apply mult_le_one_of_degrees
    intro v
    rw [degree_fiveRemoved]
    split_ifs <;> omega
  intro e
  by_cases he1 : e=s(p 1,p 2)
  · exact (hb e).trans (he1 ▸ h12)
  by_cases he2 : e=s(p 3,p 4)
  · exact (hb e).trans (he2 ▸ h34)
  have hz : (fiveRemoved p).mult e=0 := by
    simp only [fiveRemoved,addCopies,unitEdge,if_neg he1,if_neg he2,Nat.zero_add]
  rw [hz]
  exact Nat.zero_le _

theorem fiveAdded_le_of_edges (Q : MultiGraph V) (p : Fin 6 ↪ V)
    (h01 : 1≤Q.mult s(p 0,p 1)) (h23 : 1≤Q.mult s(p 2,p 3))
    (h45 : 1≤Q.mult s(p 4,p 5)) :
    ∀ e,(fiveAdded p).mult e≤Q.mult e := by
  have hb : ∀ e,(fiveAdded p).mult e≤1 := by
    apply mult_le_one_of_degrees
    intro v
    rw [degree_fiveAdded]
    split_ifs <;> omega
  intro e
  by_cases he1 : e=s(p 0,p 1)
  · exact (hb e).trans (he1 ▸ h01)
  by_cases he2 : e=s(p 2,p 3)
  · exact (hb e).trans (he2 ▸ h23)
  by_cases he3 : e=s(p 4,p 5)
  · exact (hb e).trans (he3 ▸ h45)
  have hz : (fiveAdded p).mult e=0 := by
    simp only [fiveAdded,addCopies,unitEdge,if_neg he1,if_neg he2,if_neg he3,Nat.zero_add]
  rw [hz]
  exact Nat.zero_le _

namespace PartialColouring

variable {M : MultiGraph V} {k : ℕ}

/-- The local augmentation theorem: the path and new proper partial
colouring are both constructed from neighbourhood inequalities. No
completion or alternating-path existence is supplied as a hypothesis. -/
theorem exists_augmentation (P : M.PartialColouring k) (S Z : Finset V)
    (i : Fin k) (u v : V) (m d bA bB : ℕ)
    (hS : S.card=m) (hu : u∈S) (hv : v∈Sᶜ)
    (hmissU : (P.colouring.colourGraph i).degree u=0)
    (hmissV : (P.colouring.colourGraph i).degree v=0)
    (hbadA : (S\(P.colouring.colourGraph i).eligibleVertices
      (P.colouring.colourGraph_degree_le_one i) S Z).card≤bA)
    (hbadB : (Sᶜ\(P.colouring.colourGraph i).eligibleVertices
      (P.colouring.colourGraph_degree_le_one i) Sᶜ Z).card≤bB)
    (hfirst : bB<(P.available.neighboursInto Sᶜ u).card)
    (hNv : d≤(P.available.neighboursInto S v).card)
    (hNold : ∀ z∈Sᶜ,z∉Z → d≤(P.available.neighboursInto S z).card)
    (hroom : m+2*bA<2*d) :
    ∃ Q : M.PartialColouring k,
      Q.graph.edgeCount=P.graph.edgeCount+1 ∧
      (∀ z,Q.graph.degree z=P.graph.degree z+(if z=u ∨ z=v then 1 else 0)) ∧
      (∀ j,j≠i → Q.colouring.colourGraph j=P.colouring.colourGraph j) ∧
      ∀ z,(Q.colouring.colourGraph i).degree z=
        (P.colouring.colourGraph i).degree z+(if z=u ∨ z=v then 1 else 0) := by
  classical
  let C:=P.colouring.colourGraph i
  let hc:=P.colouring.colourGraph_degree_le_one i
  let EA:=C.eligibleVertices hc S Z
  let EB:=C.eligibleVertices hc Sᶜ Z
  let τ:=C.matchingPartner hc
  let N : V → V → Prop:=fun a b => 0<P.available.mult s(a,b)
  have hEA : EA⊆S:=C.eligibleVertices_subset hc S Z
  have hEB : EB⊆Sᶜ:=C.eligibleVertices_subset hc Sᶜ Z
  change (S\EA).card≤bA at hbadA
  change (Sᶜ\EB).card≤bB at hbadB
  have hfirst' : (EB.filter (N u)).Nonempty := by
    have h:=OverfullWork.ShortAugmentSearch.neighbours_lost Sᶜ EB hEB (N u)
    have hn : (Sᶜ.filter (N u)).card=(P.available.neighboursInto Sᶜ u).card:=rfl
    rw [hn] at h
    have he : 0<(EB.filter (N u)).card := by omega
    exact card_pos.mp he
  have hlarge : ∀ z∈EB,EA.card<(EA.filter (N v)).card+(EA.filter (N z)).card := by
    intro z hz
    have hZ : z∉Z:=(mem_filter.mp hz).2.2.2.1
    have hn:=hNold z (hEB hz) hZ
    have h₁:=OverfullWork.ShortAugmentSearch.neighbours_lost S EA hEA (N v)
    have h₂:=OverfullWork.ShortAugmentSearch.neighbours_lost S EA hEA (N z)
    have hE:=card_le_card hEA
    change (S.filter (N z)).card≥d at hn
    change (S.filter (N v)).card≥d at hNv
    omega
  have huE : u∉EA := by
    intro h
    have h1:=(mem_filter.mp h).2.1
    change (P.colouring.colourGraph i).degree u=1 at h1
    omega
  have hvE : v∉EB := by
    intro h
    have h1:=(mem_filter.mp h).2.1
    change (P.colouring.colourGraph i).degree v=1 at h1
    omega
  obtain ⟨p,hp0,hp5,hp1,hp2,hp3,hp4,h01,h23,h54⟩ :=
    OverfullWork.ShortAugmentSearch.exists_five_pattern S Sᶜ EA EB u v τ
      (C.matchingPartner_apply_apply hc) disjoint_compl_right hEA hEB hu hv huE hvE
      (C.eligibleVertices_closed hc S Z) (C.eligibleVertices_closed hc Sᶜ Z)
      (C.eligibleVertices_ne hc S Z) (C.eligibleVertices_ne hc Sᶜ Z) N hfirst' hlarge
  have h12 : 1≤C.mult s(p 1,p 2) := by
    rw [hp2]
    exact (C.matchingPartner_adj hc (p 1) (mem_filter.mp hp1).2.1).ge
  have h34 : 1≤C.mult s(p 3,p 4) := by
    rw [hp4]
    exact (C.matchingPartner_adj hc (p 3) (mem_filter.mp hp3).2.1).ge
  have hR : ∀ e,(fiveRemoved p).mult e≤P.colouring.col e i:=fiveRemoved_le_of_edges C p h12 h34
  have hA : ∀ e,(fiveAdded p).mult e≤P.available.mult e :=
    fiveAdded_le_of_edges P.available p h01 h23 (by
      change 0<P.available.mult s(p 5,p 4) at h54
      have h : 0<P.available.mult s(p 4,p 5) := by simpa only [Sym2.eq_swap] using h54
      omega)
  obtain ⟨Q,he,hd,ho,hi⟩:=P.five_exchange_exists i p hR hA
    (by simpa only [hp0] using hmissU) (by simpa only [hp5] using hmissV)
  refine ⟨Q,he,?_,ho,?_⟩
  · simpa only [hp0,hp5] using hd
  · simpa only [hp0,hp5] using hi

end PartialColouring
end SimpleGraph.MultiGraph
