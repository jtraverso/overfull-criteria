module

public import OverfullWork.PartialColouring

@[expose] public section


/-! # The exact five-edge exchange used in matching completion

For six distinct vertices, remove the two inner matching edges and add
three alternate edges. This file proves properness and capacity for
all parallel copies in the ambient multigraph.
-/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def unitEdge (u v : V) (hne : u≠v) : MultiGraph V where
  mult e := if e=s(u,v) then 1 else 0
  loopless e he := by
    have hn : e≠s(u,v) := by
      intro h
      subst e
      exact hne (Sym2.mk_isDiag_iff.mp he)
    simp only [if_neg hn]

theorem degree_unitEdge (u v : V) (hne : u≠v) (z : V) :
    (unitEdge u v hne).degree z=if z=u ∨ z=v then 1 else 0 := by
  rw [degree_eq_sum_ite]
  simp only [unitEdge]
  rw [sum_eq_single s(u,v)]
  · simp only [ite_true,Sym2.mem_iff]
  · intro e _ he
    rw [if_neg he]
    simp
  · simp

theorem edgeCount_unitEdge (u v : V) (hne : u≠v) :
    (unitEdge u v hne).edgeCount=1 := by
  simp only [edgeCount,unitEdge]
  simp

def fiveRemoved (p : Fin 6 ↪ V) : MultiGraph V :=
  (unitEdge (p 1) (p 2) (p.injective.ne (by decide))).addCopies
    (unitEdge (p 3) (p 4) (p.injective.ne (by decide)))

def fiveAdded (p : Fin 6 ↪ V) : MultiGraph V :=
  ((unitEdge (p 0) (p 1) (p.injective.ne (by decide))).addCopies
    (unitEdge (p 2) (p 3) (p.injective.ne (by decide)))).addCopies
    (unitEdge (p 4) (p 5) (p.injective.ne (by decide)))

theorem degree_fiveRemoved (p : Fin 6 ↪ V) (v : V) :
    (fiveRemoved p).degree v=if v=p 1 ∨ v=p 2 ∨ v=p 3 ∨ v=p 4 then 1 else 0 := by
  simp only [fiveRemoved,degree_addCopies,degree_unitEdge]
  have hneq : ∀ i j : Fin 6,i≠j → p i≠p j := fun _ _ h => p.injective.ne h
  by_cases h1 : v=p 1
  · subst v; simp [hneq]
  by_cases h2 : v=p 2
  · subst v; simp [hneq,h1]
  by_cases h3 : v=p 3
  · subst v; simp [hneq,h1,h2]
  by_cases h4 : v=p 4
  · subst v; simp [hneq,h1,h2,h3]
  simp [h1,h2,h3,h4]

theorem degree_fiveAdded (p : Fin 6 ↪ V) (v : V) :
    (fiveAdded p).degree v=if ∃ i : Fin 6,v=p i then 1 else 0 := by
  simp only [fiveAdded,degree_addCopies,degree_unitEdge]
  have hneq : ∀ i j : Fin 6,i≠j → p i≠p j := fun _ _ h => p.injective.ne h
  by_cases hex : ∃ i : Fin 6,v=p i
  · obtain ⟨i,rfl⟩:=hex
    fin_cases i <;> simp [hneq]
  · have hn : ∀ i : Fin 6,v≠p i := by simpa only [not_exists] using hex
    simp [hn,hex]

theorem edgeCount_addCopies (M N : MultiGraph V) :
    (M.addCopies N).edgeCount=M.edgeCount+N.edgeCount := by
  simp only [edgeCount,addCopies,sum_add_distrib]

theorem five_edge_counts (p : Fin 6 ↪ V) :
    (fiveRemoved p).edgeCount=2 ∧ (fiveAdded p).edgeCount=3 := by
  simp only [fiveRemoved,fiveAdded,edgeCount_addCopies,edgeCount_unitEdge]
  norm_num

namespace PartialColouring

variable {M : MultiGraph V} {k : ℕ}

/-- A five-edge exchange is a legal update when its two old edges have
the selected colour and its three new copies are available. -/
theorem five_exchange_exists (P : M.PartialColouring k) (i : Fin k) (p : Fin 6 ↪ V)
    (hR : ∀ e,(fiveRemoved p).mult e≤P.colouring.col e i)
    (hA : ∀ e,(fiveAdded p).mult e≤P.available.mult e)
    (h0 : (P.colouring.colourGraph i).degree (p 0)=0)
    (h5 : (P.colouring.colourGraph i).degree (p 5)=0) :
    ∃ Q : M.PartialColouring k,
      Q.graph.edgeCount=P.graph.edgeCount+1 ∧
      (∀ v,Q.graph.degree v=P.graph.degree v+(if v=p 0 ∨ v=p 5 then 1 else 0)) ∧
      (∀ j,j≠i → Q.colouring.colourGraph j=P.colouring.colourGraph j) ∧
      ∀ v,(Q.colouring.colourGraph i).degree v=
        (P.colouring.colourGraph i).degree v+(if v=p 0 ∨ v=p 5 then 1 else 0) := by
  have hdeg (v : V) := degree_subtract_add (P.colouring.colourGraph i) (fiveRemoved p) hR v
  have hp (v : V) : ((P.colouring.colourGraph i).subtractCopies (fiveRemoved p)).degree v+
      (fiveAdded p).degree v≤1 := by
    have hc:=P.colouring.colourGraph_degree_le_one i v
    have hr:=degree_fiveRemoved p v
    have ha:=degree_fiveAdded p v
    have hd:=hdeg v
    by_cases hex : ∃ j : Fin 6,v=p j
    · obtain ⟨j,rfl⟩:=hex
      fin_cases j <;> simp_all
    · have hn : ∀ j : Fin 6,v≠p j := by simpa only [not_exists] using hex
      simp only [hn,or_self,if_false] at hr
      rw [if_neg hex] at ha
      omega
  let Q:=P.exchange i (fiveRemoved p) (fiveAdded p) hR hA hp
  have hchange (v : V) : (fiveAdded p).degree v=
      (fiveRemoved p).degree v+(if v=p 0 ∨ v=p 5 then 1 else 0) := by
    rw [degree_fiveRemoved,degree_fiveAdded]
    have hneq : ∀ a b : Fin 6,a≠b → p a≠p b := fun _ _ h => p.injective.ne h
    by_cases hex : ∃ j : Fin 6,v=p j
    · obtain ⟨j,rfl⟩:=hex
      fin_cases j <;> simp [hneq]
    · have hn : ∀ j : Fin 6,v≠p j := by simpa only [not_exists] using hex
      simp [hn,hex]
  refine ⟨Q,?_,?_,?_,?_⟩
  · have h:=P.exchange_edgeCount_identity i (fiveRemoved p) (fiveAdded p) hR hA hp
    obtain ⟨hr,ha⟩:=five_edge_counts p
    dsimp only [Q]
    omega
  · intro v
    have h:=P.exchange_degree_identity i (fiveRemoved p) (fiveAdded p) hR hA hp v
    have hc:=hchange v
    change Q.graph.degree v+_= _ at h
    omega
  · intro j hj
    exact P.exchange_colour_other i (fiveRemoved p) (fiveAdded p) hR hA hp j hj
  · intro v
    dsimp only [Q]
    rw [P.exchange_colour_selected,degree_addCopies]
    have h:=hdeg v
    have hc:=hchange v
    omega

end PartialColouring
end SimpleGraph.MultiGraph
