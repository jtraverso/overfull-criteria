module

public import OverfullWork.FreeColourMatching

@[expose] public section


namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

def addMatching (P : M.PartialColouring k) (i : Fin k) (J : MultiGraph V)
    (hJ : ∀ e,J.mult e≤P.available.mult e)
    (hp : ∀ v,(P.colouring.colourGraph i).degree v+J.degree v≤1) : M.PartialColouring k where
  graph:=P.graph.addCopies J
  le e:=by
    have hc:=P.le e
    have hj:=hJ e
    change P.graph.mult e+J.mult e≤M.mult e
    change J.mult e≤M.mult e-P.graph.mult e at hj
    omega
  colouring:={
    col e j:=P.colouring.col e j+(if j=i then J.mult e else 0)
    sum_col e:=by
      rw [sum_add_distrib,P.colouring.sum_col,sum_ite_eq']
      simp only [mem_univ,if_true]
      rfl
    proper v j:=by
      by_cases hj : j=i
      · subst j
        simp only [ite_true,sum_add_distrib]
        exact hp v
      · simpa only [if_neg hj,Nat.add_zero] using P.colouring.proper v j }

theorem addMatching_other (P : M.PartialColouring k) (i : Fin k) (J : MultiGraph V)
    (hJ : ∀ e,J.mult e≤P.available.mult e)
    (hp : ∀ v,(P.colouring.colourGraph i).degree v+J.degree v≤1) (j : Fin k) (hj : j≠i) :
    ((P.addMatching i J hJ hp).colouring.colourGraph j)=P.colouring.colourGraph j := by
  apply ext_mult
  intro e
  change P.colouring.col e j+(if j=i then J.mult e else 0)=P.colouring.col e j
  simp only [if_neg hj,Nat.add_zero]

theorem addMatching_selected (P : M.PartialColouring k) (i : Fin k) (J : MultiGraph V)
    (hJ : ∀ e,J.mult e≤P.available.mult e)
    (hp : ∀ v,(P.colouring.colourGraph i).degree v+J.degree v≤1) :
    ((P.addMatching i J hJ hp).colouring.colourGraph i)=(P.colouring.colourGraph i).addCopies J := by
  apply ext_mult
  intro e
  exact congrArg (fun n => P.colouring.col e i+n) (if_pos rfl)

end PartialColouring
end SimpleGraph.MultiGraph
