module

public import OverfullWork.DirectedListRoutes

@[expose] public section


/-! Concatenation at one shared endpoint, preserving the exact list
of vertices. Used to preserve all prescribed visits during induction. -/
namespace OverfullWork.DirectedListRoutes
variable {V : Type*}

theorem join_chain (D : Digraph V) {x y : V} {l s : List V}
    (h : Route D x y l) (hs : (y :: s).IsChain D.Adj) :
    (x :: (l++s)).IsChain D.Adj := by
  change ((x :: l)++s).IsChain D.Adj
  apply h.1.append hs.tail
  intro u hu v hv
  have he : y=u := by simpa only [h.2,Option.mem_some_iff] using hu
  subst u
  exact hs.rel_head? hv

theorem join_last {x y : V} {l s : List V}
    (h : (x :: l).getLast?=some y) :
    (x :: (l++s)).getLast?=(y :: s).getLast? := by
  cases s with
  | nil => simpa using h
  | cons v vs =>
    change ((x :: l)++(v :: vs)).getLast?=(y :: v :: vs).getLast?
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),List.getLast?_cons_cons]

end OverfullWork.DirectedListRoutes
