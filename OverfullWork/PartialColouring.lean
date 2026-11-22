module

public import OverfullWork.MissingPairs

@[expose] public section


/-! # Capacity-preserving updates of partial multigraph edge colourings -/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A proper colouring of a submultigraph, with explicit ambient capacities. -/
structure PartialColouring (M : MultiGraph V) (k : ℕ) where
  graph : MultiGraph V
  colouring : graph.EdgeColoring k
  le : ∀ e,graph.mult e≤M.mult e

namespace PartialColouring

variable {M : MultiGraph V} {k : ℕ}

def available (P : M.PartialColouring k) : MultiGraph V := M.subtractCopies P.graph

theorem available_degree (P : M.PartialColouring k) (v : V) :
    P.available.degree v+P.graph.degree v=M.degree v :=
  degree_subtract_add M P.graph P.le v

/-- Replace part of a single colour by available copies. The degree
inequality is the exact local matching obligation for this update. -/
def exchange (P : M.PartialColouring k) (i : Fin k) (R A : MultiGraph V)
    (hR : ∀ e,R.mult e≤P.colouring.col e i)
    (hA : ∀ e,A.mult e≤P.available.mult e)
    (hproper : ∀ v, ((P.colouring.colourGraph i).subtractCopies R).degree v+A.degree v≤1) :
    M.PartialColouring k where
  graph := (P.graph.subtractCopies R).addCopies A
  le e := by
    have hr:=hR e
    have hc:=P.colouring.col_le_mult e i
    have ha:=hA e
    have hp:=P.le e
    change P.graph.mult e-R.mult e+A.mult e≤M.mult e
    change A.mult e≤M.mult e-P.graph.mult e at ha
    omega
  colouring := {
    col e j := if j=i then P.colouring.col e i-R.mult e+A.mult e else P.colouring.col e j
    sum_col e := by
      rw [←sum_erase_add _ _ (mem_univ i)]
      simp only [ite_true]
      have ho : (∑ j∈univ.erase i,
          if j=i then P.colouring.col e i-R.mult e+A.mult e else P.colouring.col e j)=
          ∑ j∈univ.erase i,P.colouring.col e j := by
        apply sum_congr rfl
        intro j hj
        rw [if_neg (mem_erase.mp hj).1]
      rw [ho]
      have hs:=P.colouring.sum_col e
      rw [←sum_erase_add _ _ (mem_univ i)] at hs
      have hr:=hR e
      change _=P.graph.mult e-R.mult e+A.mult e
      omega
    proper v j := by
      by_cases hj : j=i
      · subst j
        simp only [ite_true,sum_add_distrib]
        exact hproper v
      · simpa only [if_neg hj] using P.colouring.proper v j }

theorem exchange_colour_other (P : M.PartialColouring k) (i : Fin k) (R A : MultiGraph V)
    (hR : ∀ e,R.mult e≤P.colouring.col e i)
    (hA : ∀ e,A.mult e≤P.available.mult e)
    (hp : ∀ v, ((P.colouring.colourGraph i).subtractCopies R).degree v+A.degree v≤1)
    (j : Fin k) (hj : j≠i) :
    ((P.exchange i R A hR hA hp).colouring.colourGraph j)=P.colouring.colourGraph j := by
  apply ext_mult
  intro e
  exact if_neg hj

theorem exchange_colour_selected (P : M.PartialColouring k) (i : Fin k) (R A : MultiGraph V)
    (hR : ∀ e,R.mult e≤P.colouring.col e i)
    (hA : ∀ e,A.mult e≤P.available.mult e)
    (hp : ∀ v, ((P.colouring.colourGraph i).subtractCopies R).degree v+A.degree v≤1) :
    ((P.exchange i R A hR hA hp).colouring.colourGraph i)=
      ((P.colouring.colourGraph i).subtractCopies R).addCopies A := by
  apply ext_mult
  intro e
  exact if_pos rfl

theorem exchange_degree_identity (P : M.PartialColouring k) (i : Fin k) (R A : MultiGraph V)
    (hR : ∀ e,R.mult e≤P.colouring.col e i)
    (hA : ∀ e,A.mult e≤P.available.mult e)
    (hp : ∀ v, ((P.colouring.colourGraph i).subtractCopies R).degree v+A.degree v≤1) (v : V) :
    (P.exchange i R A hR hA hp).graph.degree v+R.degree v=P.graph.degree v+A.degree v := by
  change ((P.graph.subtractCopies R).addCopies A).degree v+R.degree v=_
  rw [degree_addCopies]
  have hr : ∀ e,R.mult e≤P.graph.mult e := fun e => (hR e).trans (P.colouring.col_le_mult e i)
  have h:=degree_subtract_add P.graph R hr v
  omega

theorem exchange_edgeCount_identity (P : M.PartialColouring k) (i : Fin k) (R A : MultiGraph V)
    (hR : ∀ e,R.mult e≤P.colouring.col e i)
    (hA : ∀ e,A.mult e≤P.available.mult e)
    (hp : ∀ v, ((P.colouring.colourGraph i).subtractCopies R).degree v+A.degree v≤1) :
    (P.exchange i R A hR hA hp).graph.edgeCount+R.edgeCount=P.graph.edgeCount+A.edgeCount := by
  unfold edgeCount
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  have hr:=(hR e).trans (P.colouring.col_le_mult e i)
  change P.graph.mult e-R.mult e+A.mult e+R.mult e=P.graph.mult e+A.mult e
  omega

end PartialColouring
end SimpleGraph.MultiGraph
