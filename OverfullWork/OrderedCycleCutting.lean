module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.OfFn

@[expose] public section


/-! Cutting a directed cycle presented by its marked vertices and the
lists between consecutive marks. These lemmas transform an actual edge
chain; they assert no Hamiltonian existence. -/
namespace OverfullWork.OrderedCycleCutting
variable {I X : Type*}

def block (body : I → List X) (i : I) : List (X ⊕ I) :=
  (body i).map Sum.inl ++ [Sum.inr i]

def word (body : I → List X) (order : List I) : List (X ⊕ I) :=
  order.flatMap (block body)

theorem cut_chain (R : (X ⊕ I) → (X ⊕ I) → Prop) (body : I → List X)
    (order : List I) (start : I)
    (h : (Sum.inr start :: word body order).IsChain R) :
    (start :: order).IsChain (fun j i =>
      (Sum.inr j :: block body i).IsChain R) := by
  induction order generalizing start with
  | nil => exact .singleton _
  | cons i rest ih =>
    have hh : ((Sum.inr start :: (body i).map Sum.inl) ++
        Sum.inr i :: word body rest).IsChain R := by
      simpa [word,block,List.flatMap_cons,List.append_assoc] using h
    obtain ⟨hFirst,hRest⟩ := List.isChain_split.mp hh
    apply List.IsChain.cons_cons
    · simpa [block,List.cons_append] using hFirst
    · exact ih i hRest

theorem prescribed_steps (next : I ≃ I) (Q : I → I → Prop)
    (order : List I) (start : I)
    (hOrder : (start :: order).IsChain (fun j i => next j=i))
    (hQ : (start :: order).IsChain Q) :
    ∀ i ∈ order,Q (next.symm i) i := by
  induction order generalizing start with
  | nil => simp
  | cons i rest ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · have he := hOrder.rel
      have he' : next.symm k=start := by rw [←he,next.symm_apply_apply]
      rw [he']
      exact hQ.rel
    · exact ih i hOrder.tail hQ.tail k hk

end OverfullWork.OrderedCycleCutting
