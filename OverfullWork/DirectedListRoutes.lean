module

public import OverfullWork.DirectedRobustExpansion
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup

@[expose] public section


/-! Directed routes on actual digraphs, represented by vertex lists.
Loop erasure preserves endpoints and only deletes vertices. -/
namespace OverfullWork.DirectedListRoutes
variable {V : Type*}
open scoped Classical
set_option maxHeartbeats 4000000

def Route (D : Digraph V) (x y : V) (tail : List V) : Prop :=
  (x :: tail).IsChain D.Adj ∧ (x :: tail).getLast?=some y

theorem nil_route (D : Digraph V) (x : V) : Route D x x [] := by
  exact ⟨.singleton _,rfl⟩

theorem snoc_route (D : Digraph V) {x y z : V} {tail : List V}
    (h : Route D x y tail) (hyz : D.Adj y z) : Route D x z (tail ++ [z]) := by
  constructor
  · change ((x :: tail) ++ [z]).IsChain D.Adj
    apply h.1.append (.singleton _)
    intro u hu v hv
    have hu' : u=y := by
      have hh : y=u := by simpa only [h.2,Option.mem_some_iff] using hu
      exact hh.symm
    have hv' : v=z := by
      have hh : z=v := by simpa using hv
      exact hh.symm
    subst u;subst v;exact hyz
  · change ((x :: tail) ++ [z]).getLast?=some z
    exact (List.getLast?_append_of_ne_nil (x :: tail) (by simp)).trans rfl

/-- Every actual directed route admits a simple route with the same
ends, no greater length, and no new vertices. -/
theorem erase_loops (D : Digraph V) (x y : V) (tail : List V)
    (h : Route D x y tail) :
    ∃ s,Route D x y s ∧ (x :: s).Nodup ∧ s.length≤tail.length ∧
      ∀ v∈x :: s,v∈x :: tail := by
  have main : ∀ n : ℕ,∀ (l : List V),l.length=n → ∀ x : V,
      Route D x y l → ∃ s,Route D x y s ∧ (x :: s).Nodup ∧ s.length≤l.length ∧
        ∀ v∈x :: s,v∈x :: l := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hn x hR
      cases l with
      | nil => exact ⟨[],hR,by simp,le_rfl,fun _ hh => hh⟩
      | cons z zs =>
        by_cases hx : x∈z :: zs
        · obtain ⟨pre,post,hSplit⟩ := List.append_of_mem hx
          have hChain : ((x :: pre) ++ (x :: post)).IsChain D.Adj := by
            simpa only [List.cons_append,←hSplit] using hR.1
          have hLast : (x :: post).getLast?=some y := by
            have hh := hR.2
            change (x :: z :: zs).getLast?=some y at hh
            rw [hSplit] at hh
            change ((x :: pre) ++ (x :: post)).getLast?=some y at hh
            simpa only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] using hh
          have hLength : post.length<n := by
            have hh := congrArg List.length hSplit
            simp only [List.length_cons,List.length_append] at hn hh
            omega
          obtain ⟨s,hs,hSimple,hLen,hSub⟩ := ih post.length hLength post rfl x
            ⟨hChain.right_of_append,hLast⟩
          refine ⟨s,hs,hSimple,by simp only [List.length_cons] at hn ⊢;omega,?_⟩
          intro v hv
          have hh := hSub v hv
          rw [hSplit]
          simp only [List.mem_cons,List.mem_append] at ⊢ hh
          tauto
        · have hTail : Route D z y zs :=
            ⟨hR.1.tail,by simpa only [List.getLast?_cons_cons] using hR.2⟩
          obtain ⟨s,hs,hSimple,hLen,hSub⟩ := ih zs.length (by simp only [List.length_cons] at hn;omega) zs rfl z hTail
          refine ⟨z :: s,⟨List.IsChain.cons_cons hR.1.rel hs.1,?_⟩,?_,by simpa using hLen,?_⟩
          · simpa only [List.getLast?_cons_cons] using hs.2
          · apply List.nodup_cons.mpr
            exact ⟨fun hv => hx (hSub x hv),hSimple⟩
          · intro v hv
            rcases List.mem_cons.mp hv with rfl|hv
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hSub v hv)
  exact main tail.length tail rfl x h

end OverfullWork.DirectedListRoutes
