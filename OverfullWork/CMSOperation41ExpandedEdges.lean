module

public import OverfullWork.CMSOperation41MarkedCycle

@[expose] public section


/-! Exact edge support of the expanded cyclic word. This keeps track of
the original host edges and of all edges in replacement segments. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset
open scoped Classical

variable {V : Type*}

/-- The cyclic sequence with its starting vertex repeated at the end. -/
def expandedCycleWord {n : ℕ} (w : Fin (n+1) → V) (body : Fin (n+1) → List V) : List V :=
  openCycleWord w body ++ [w 0]

private theorem chain_of_consecutive_pairs : ∀ l : List V, l.IsChain (wordGraph l).Adj
  | [] => .nil
  | [v] => .singleton v
  | u :: v :: l => by
    apply List.isChain_cons_cons.mpr
    constructor
    · exact ⟨[],l,rfl⟩
    · apply (chain_of_consecutive_pairs (v :: l)).imp
      intro x y h
      obtain ⟨p,q,hq⟩ := h
      exact ⟨u::p,q,by simpa only [List.cons_append] using congrArg (List.cons u) hq⟩

theorem replacement_word_infix_expanded_cycle {n : ℕ} (w : Fin (n+1) → V)
    (body : Fin (n+1) → List V) (i : Fin (n+1)) :
    List.IsInfix (w i :: body i ++ [w (finRotate (n+1) i)]) (expandedCycleWord w body) := by
  let order := List.ofFn (id : Fin (n+1) → Fin (n+1))
  let P (j : Fin (n+1)) := w j :: body j
  have hi : i ∈ order := List.mem_ofFn.mpr ⟨i,rfl⟩
  obtain ⟨before,after,hOrder,_⟩ := List.eq_append_cons_of_mem hi
  have hRotate : (order ++ [0]).IsChain (fun j k => finRotate (n+1) j = k) :=
    DirectedRungCycle.rotate_order (fun _ => rfl)
  rw [hOrder,List.append_assoc,List.cons_append] at hRotate
  have hHead := hRotate.right_of_append
  have hAfter : ∃ t, after.flatMap P ++ [w 0] = w (finRotate (n+1) i) :: t := by
    cases after with
    | nil =>
      have h := hHead.rel
      exact ⟨[],by simpa [h]⟩
    | cons j after =>
      have h := hHead.rel
      exact ⟨body j ++ after.flatMap P ++ [w 0],by
        rw [List.flatMap_cons,h]
        simp [P,List.cons_append,List.append_assoc]⟩
  obtain ⟨t,ht⟩ := hAfter
  refine ⟨before.flatMap P,t,?_⟩
  change _ = order.flatMap P ++ [w 0]
  rw [hOrder,List.flatMap_append,List.flatMap_cons]
  simp only [List.append_assoc]
  rw [ht]
  simp only [P,List.cons_append,List.nil_append]

/-- No edges other than consecutive pairs of the replacement words
appear in the expanded cycle, including its closing edge. -/
theorem expanded_cycle_wordGraph {n : ℕ} (w : Fin (n+1) → V)
    (body : Fin (n+1) → List V) :
    wordGraph (expandedCycleWord w body) =
      ⨆ i, wordGraph (w i :: body i ++ [w (finRotate (n+1) i)]) := by
  let A (i : Fin (n+1)) := w i :: body i
  let last (i : Fin (n+1)) := (A i).getLast (by simp [A])
  let X := ⨆ i, wordGraph (w i :: body i ++ [w (finRotate (n+1) i)])
  have hPart (i : Fin (n+1)) :
      (A i ++ [w (finRotate (n+1) i)]).IsChain X.Adj :=
    (chain_of_consecutive_pairs _).imp (fun u v h => Digraph.iSup_adj.mpr ⟨i,h⟩)
  have hNext (i : Fin (n+1)) : X.Adj (last i) (w (finRotate (n+1) i)) :=
    (hPart i).rel_getLast_head_of_append (by simp) (by simp)
  have hChain : (expandedCycleWord w body).IsChain X.Adj :=
    DirectedReserveStitching.chain_of_blocks X A w last (fun _ => rfl)
      (fun _ => List.getLast?_eq_getLast_of_ne_nil (by simp [A]))
      (fun i => (hPart i).left_of_append) 0 _
      (DirectedRungCycle.rotate_order hNext)
  apply le_antisymm (wordGraph_le hChain)
  apply iSup_le
  intro i x y h
  exact h.trans (replacement_word_infix_expanded_cycle w body i)

end OverfullWork.DirectedSpanningConfiguration
