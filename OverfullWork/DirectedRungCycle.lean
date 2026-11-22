module

public import OverfullWork.DirectedRouteJoining
public import Mathlib.Data.List.Perm.Basic

@[expose] public section


/-! A directed cycle presented as rungs and the paths joining consecutive rungs.
The order of the rungs can be any cyclic order. -/
namespace OverfullWork.DirectedRungCycle

open DirectedListRoutes
variable {V I : Type*}

def block (a b : I → V) (link body : I → List V) (i : I) : List V :=
  [a i] ++ body i ++ (b i :: link i)

def word (a b : I → V) (link body : I → List V) (order : List I) : List V :=
  order.flatMap (block a b link body)

private theorem chain_word (D : Digraph V) (a b : I → V) (link body : I → List V)
    (hRung : ∀ i, Route D (a i) (b i) (body i ++ [b i]))
    (z : I) (order : List I)
    (hOrder : (order ++ [z]).IsChain (fun i j => Route D (b i) (a j) (link i ++ [a j]))) :
    (word a b link body order ++ [a z]).IsChain D.Adj := by
  induction order with
  | nil => exact .singleton _
  | cons i rest ih =>
    have hRest := ih hOrder.tail
    have hConnection : (b i :: (link i ++ (word a b link body rest ++ [a z]))).IsChain D.Adj := by
      cases rest with
      | nil => simpa [word] using hOrder.rel.1
      | cons j rest =>
        have hLink : Route D (b i) (a j) (link i ++ [a j]) := hOrder.rel
        let T := body j ++ (b j :: link j) ++ word a b link body rest ++ [a z]
        have hTail : (a j :: T).IsChain D.Adj := by
          simpa only [word, block, List.flatMap_cons, List.singleton_append, List.cons_append,
            List.append_assoc, List.nil_append, T] using hRest
        simpa only [T, word, block, List.flatMap_cons, List.singleton_append, List.cons_append,
          List.append_assoc] using join_chain D hLink hTail
    have hR := hRung i
    have hGlue := join_chain D hR hConnection
    simpa only [word, block, List.flatMap_cons, List.singleton_append, List.cons_append,
      List.append_assoc, List.nil_append] using hGlue

/-- The unchanged connectors between rungs yield an actual closed edge chain. -/
theorem closed_word (D : Digraph V) (a b : I → V) (link body : I → List V)
    (first : I) (rest : List I)
    (hRung : ∀ i, Route D (a i) (b i) (body i ++ [b i]))
    (hOrder : ((first :: rest) ++ [first]).IsChain
      (fun i j => Route D (b i) (a j) (link i ++ [a j]))) :
    (word a b link body (first :: rest)).head? = some (a first) ∧
      (word a b link body (first :: rest) ++ [a first]).IsChain D.Adj := by
  exact ⟨by simp [word, block], chain_word D a b link body hRung first _ hOrder⟩

private theorem perm_collect (a b : I → V) (link body : I → List V) (order : List I) :
    (word a b link body order).Perm
      ((word a b link (fun _ => []) order) ++ order.flatMap body) := by
  unfold word
  have hBlock : ∀ i, (block a b link body i).Perm
      (block a b link (fun _ => []) i ++ body i) := by
    intro i
    simpa [block, List.append_assoc] using
      (List.perm_append_comm (l₁ := body i) (l₂ := b i :: link i)).cons (a i)
  exact (List.Perm.flatMap_left _ (fun i _ => hBlock i)).trans (List.flatMap_append_perm _ _ _).symm

private theorem flatMap_at [DecidableEq I] (k : I) (fresh : List V) (order : List I)
    (hSimple : order.Nodup) :
    order.flatMap (fun i => if i = k then fresh else []) =
      if k ∈ order then fresh else [] := by
  induction order with
  | nil => simp
  | cons i rest ih =>
    rw [List.flatMap_cons, ih hSimple.of_cons]
    by_cases hi : i = k
    · subst i
      have hOut := (List.nodup_cons.mp hSimple).1
      simp [hOut]
    · simp [hi, Ne.symm hi]

/-- Permuting the middle lists of rungs and inserting a fresh list into
one slot preserves every old vertex, with exactly the new list added. -/
theorem perm_word_replace [DecidableEq I] (a b : I → V) (link body : I → List V)
    (order : List I) (hOrder : order.Nodup)
    (e : Equiv.Perm I) (hPreserves : ∀ i, i ∈ order ↔ e i ∈ order)
    (k : I) (hk : k ∈ order) (fresh : List V) :
    (word a b link (fun i => body (e i) ++ if i = k then fresh else []) order).Perm
      (word a b link body order ++ fresh) := by
  have hMap : (order.map e).Perm order := by
    apply (List.perm_ext_iff_of_nodup (hOrder.map e.injective) hOrder).mpr
    intro j
    rw [List.mem_map]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (hPreserves i).mp hi
    · intro hj
      exact ⟨e.symm j, (hPreserves _).mpr (by simpa using hj), e.apply_symm_apply j⟩
  have hBody : (order.flatMap (fun i => body (e i))).Perm (order.flatMap body) := by
    simpa only [List.flatMap_map, Function.comp_apply] using hMap.flatMap_right body
  have hInsert := List.flatMap_append_perm order (fun i => body (e i))
    (fun i => if i = k then fresh else [])
  rw [flatMap_at k fresh order hOrder, if_pos hk] at hInsert
  have h := (perm_collect a b link _ order).trans
    ((hInsert.symm.trans (hBody.append_right fresh)).append_left _)
  rw [← List.append_assoc] at h
  exact h.trans ((perm_collect a b link body order).symm.append_right fresh)

end OverfullWork.DirectedRungCycle
