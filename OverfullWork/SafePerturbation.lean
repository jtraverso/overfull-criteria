module

public import OverfullWork.PerturbationAccounting

@[expose] public section


namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

/-- The path witness is retained so that local perturbations can be
iterated with exact remainder and cut identities. -/
structure SafeFive (P : M.PartialColouring k) (S Z : Finset V) (i : Fin k) (u v : V) where
  path : Fin 6 ↪ V
  first : path 0=u
  last : path 5=v
  sided : FiveSided S path
  safe : ∀ z,0<(fiveRemoved path).degree z → z∉Z
  remove_le : ∀ e,(fiveRemoved path).mult e≤P.colouring.col e i
  add_le : ∀ e,(fiveAdded path).mult e≤P.available.mult e

theorem exists_safe_five (P : M.PartialColouring k) (S Z : Finset V)
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
    (hroom : m+2*bA<2*d) : Nonempty (P.SafeFive S Z i u v) := by
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
    change (P.available.neighboursInto Sᶜ u).card≤(EB.filter (N u)).card+(Sᶜ\EB).card at h
    exact card_pos.mp (by omega)
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
  have hp2mem : p 2∈EB := by rw [hp2]; exact C.eligibleVertices_closed hc Sᶜ Z (p 1) hp1
  have hp4mem : p 4∈EA := by rw [hp4]; exact C.eligibleVertices_closed hc S Z (p 3) hp3
  have h12 : 1≤C.mult s(p 1,p 2) := by
    rw [hp2]
    exact (C.matchingPartner_adj hc (p 1) (mem_filter.mp hp1).2.1).ge
  have h34 : 1≤C.mult s(p 3,p 4) := by
    rw [hp4]
    exact (C.matchingPartner_adj hc (p 3) (mem_filter.mp hp3).2.1).ge
  refine ⟨{path:=p,first:=hp0,last:=hp5,sided:=?_,safe:=?_,remove_le:=?_,add_le:=?_}⟩
  · exact ⟨hp0 ▸ hu,mem_compl.mp (hEB hp1),mem_compl.mp (hEB hp2mem),hEA hp3,hEA hp4mem,
      hp5 ▸ mem_compl.mp hv⟩
  · intro z hz
    rw [degree_fiveRemoved] at hz
    have he : z=p 1 ∨ z=p 2 ∨ z=p 3 ∨ z=p 4 := by split_ifs at hz <;> simp_all
    rcases he with rfl|rfl|rfl|rfl
    · exact (mem_filter.mp hp1).2.2.2.1
    · exact (mem_filter.mp hp2mem).2.2.2.1
    · exact (mem_filter.mp hp3).2.2.2.1
    · exact (mem_filter.mp hp4mem).2.2.2.1
  · exact fiveRemoved_le_of_edges C p h12 h34
  · exact fiveAdded_le_of_edges P.available p h01 h23 (by
      change 0<P.available.mult s(p 5,p 4) at h54
      have h : 0<P.available.mult s(p 4,p 5) := by simpa only [Sym2.eq_swap] using h54
      omega)

theorem safe_five_proper (P : M.PartialColouring k) (S Z : Finset V) (i : Fin k) (u v : V)
    (f : P.SafeFive S Z i u v)
    (h0 : (P.colouring.colourGraph i).degree u=0)
    (h5 : (P.colouring.colourGraph i).degree v=0) (z : V) :
    ((P.colouring.colourGraph i).subtractCopies (fiveRemoved f.path)).degree z+
      (fiveAdded f.path).degree z≤1 := by
  have hd:=degree_subtract_add (P.colouring.colourGraph i) (fiveRemoved f.path) f.remove_le z
  have hc:=P.colouring.colourGraph_degree_le_one i z
  have hr:=degree_fiveRemoved f.path z
  have ha:=degree_fiveAdded f.path z
  have h0' : (P.colouring.colourGraph i).degree (f.path 0)=0 := by simpa only [f.first] using h0
  have h5' : (P.colouring.colourGraph i).degree (f.path 5)=0 := by simpa only [f.last] using h5
  by_cases hex : ∃ j : Fin 6,z=f.path j
  · obtain ⟨j,rfl⟩:=hex
    fin_cases j <;> simp_all <;> omega
  · have hn : ∀ j : Fin 6,z≠f.path j := by simpa only [not_exists] using hex
    simp only [hn,or_self,if_false] at hr
    rw [if_neg hex] at ha
    omega

def perturb (P : M.PartialColouring k) (S Z : Finset V) (i : Fin k) (u v : V)
    (f : P.SafeFive S Z i u v) (h0 : (P.colouring.colourGraph i).degree u=0)
    (h5 : (P.colouring.colourGraph i).degree v=0) : M.PartialColouring k :=
  P.exchange i (fiveRemoved f.path) (fiveAdded f.path) f.remove_le f.add_le
    (P.safe_five_proper S Z i u v f h0 h5)

end PartialColouring
end SimpleGraph.MultiGraph
