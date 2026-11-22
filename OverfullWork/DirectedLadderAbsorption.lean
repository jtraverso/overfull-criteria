module

public import OverfullWork.DirectedLadderRungs
public import OverfullWork.DirectedRungCycle
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Equiv.Set

@[expose] public section


/-! Absorbing a path into a cycle of rungs and connectors, as in
Lo–Patel Lemma 4.4. The local changes move the middle of each rung
to the next rung of that ladder, in ladder order. The cycle's
order of slots and every connector stay fixed. -/
namespace OverfullWork.DirectedAbsorbingLadder

open DirectedListRoutes DirectedRungCycle
open scoped Classical
variable {V I : Type*} {D : Digraph V} {u v : V} {q : ℕ}

def Ladder.middle (A : Ladder D u v q) : Fin (q+1) → List V :=
  Fin.snoc (fun i => A.spine (left i) :: A.tail i) []

theorem Ladder.ordinary_middle_route (A : Ladder D u v q) (i : Fin (q+1)) :
    Route D (A.spine (evenLeft i)) (A.spine (evenRight i))
      (A.middle i ++ [A.spine (evenRight i)]) := by
  induction i using Fin.lastCases with
  | last =>
    have h := snoc_route D (nil_route D (A.spine (evenLeft (Fin.last q)))) A.central_rung
    simpa [Ladder.middle] using h
  | cast i => simpa [Ladder.middle] using (A.ordinary_rung i).1

private theorem rotate_castSucc (i : Fin q) : finRotate (q+1) i.castSucc = i.succ := by
  exact finRotate_of_lt i.isLt

private theorem Ladder.rotated_middle_route (A : Ladder D u v q) (fresh : List V)
    (hFresh : Route D u v (fresh ++ [v])) (i : Fin (q+1)) :
    Route D (A.spine (evenLeft i)) (A.spine (evenRight i))
      ((A.middle ((finRotate (q+1)).symm i) ++ (if i = 0 then fresh else [])) ++
        [A.spine (evenRight i)]) := by
  induction i using Fin.cases with
  | zero =>
    have hLeft : evenLeft (0 : Fin (q+1)) = 0 := Fin.ext (by simp [evenLeft])
    have hRight : evenRight (0 : Fin (q+1)) = Fin.last (4*q+1) :=
      Fin.ext (by simp [evenRight])
    have hRotate : (finRotate (q+1)).symm 0 = Fin.last q :=
      (finRotate _).symm_apply_eq.mpr finRotate_last.symm
    simpa [hRotate, hLeft, hRight, A.source, A.target, Ladder.middle] using hFresh
  | succ i =>
    have hRotate : (finRotate (q+1)).symm i.succ = i.castSucc :=
      (finRotate _).symm_apply_eq.mpr (rotate_castSucc i).symm
    simpa [hRotate, Ladder.middle, Fin.succ_ne_zero] using (A.alternative_rung i).1

/-- Replace the ordinary rungs of one embedded ladder by its shifted
rungs and a fresh path with the same outside endpoints. The other
rungs and all connectors keep their original paths. The resulting
closed chain is simple and has exactly the old and inserted vertices. -/
theorem Ladder.absorb_into_rung_cycle (A : Ladder D u v q) (index : Fin (q+1) ↪ I)
    (a b : I → V) (link body : I → List V) (first : I) (rest : List I)
    (hDistinct : (first :: rest).Nodup) (hAll : ∀ i : I, i ∈ first :: rest)
    (hOrder : ((first :: rest) ++ [first]).IsChain
      (fun i j => Route D (b i) (a j) (link i ++ [a j])))
    (hOldRoutes : ∀ i, Route D (a i) (b i) (body i ++ [b i]))
    (hOldSimple : (word a b link body (first :: rest)).Nodup)
    (hA : ∀ i, a (index i) = A.spine (evenLeft i))
    (hB : ∀ i, b (index i) = A.spine (evenRight i))
    (hBody : ∀ i, body (index i) = A.middle i)
    (fresh : List V) (hFresh : Route D u v (fresh ++ [v])) (hFreshSimple : fresh.Nodup)
    (hDisjoint : List.Disjoint (word a b link body (first :: rest)) fresh) :
    ∃ newBody : I → List V,
      (∀ i, Route D (a i) (b i) (newBody i ++ [b i])) ∧
      (∀ j, j ∉ Set.range index → newBody j = body j) ∧
      newBody (index 0) = fresh ∧
      (word a b link newBody (first :: rest)).Perm (word a b link body (first :: rest) ++ fresh) ∧
      (word a b link newBody (first :: rest)).Nodup ∧
      (word a b link newBody (first :: rest)).head? = some (a first) ∧
      (word a b link newBody (first :: rest) ++ [a first]).IsChain D.Adj := by
  classical
  let f := Equiv.ofInjective index index.injective
  let e := Equiv.Perm.extendDomain (finRotate (q+1)).symm f
  have hApply : ∀ i, e (index i) = index ((finRotate (q+1)).symm i) := by
    intro i
    exact Equiv.Perm.extendDomain_apply_image _ f i
  let newBody := fun j => body (e j) ++ (if j = index 0 then fresh else [])
  have hSame : ∀ j, j ∉ Set.range index → newBody j = body j := by
    intro j hj
    have he : e j = j := Equiv.Perm.extendDomain_apply_not_subtype _ _ hj
    have hn : j ≠ index 0 := fun h => hj ⟨0, h.symm⟩
    simp [newBody, he, hn]
  have hLocal : ∀ i, newBody (index i) =
      A.middle ((finRotate (q+1)).symm i) ++ (if i = 0 then fresh else []) := by
    intro i
    simp only [newBody, hApply, hBody, index.injective.eq_iff]
  have hAtZero : newBody (index 0) = fresh := by
    have hRotate : (finRotate (q+1)).symm 0 = Fin.last q :=
      (finRotate _).symm_apply_eq.mpr finRotate_last.symm
    simp [hLocal, hRotate, Ladder.middle]
  have hNewRoutes : ∀ j, Route D (a j) (b j) (newBody j ++ [b j]) := by
    intro j
    by_cases hj : j ∈ Set.range index
    · obtain ⟨i, rfl⟩ := hj
      rw [hA, hB, hLocal]
      exact A.rotated_middle_route fresh hFresh i
    · simpa only [hSame j hj] using hOldRoutes j
  have hPerm := perm_word_replace a b link body (first :: rest) hDistinct e
    (fun j => iff_of_true (hAll j) (hAll (e j))) (index 0) (hAll _) fresh
  have hNodup := hPerm.nodup_iff.mpr (List.nodup_append.mpr
    ⟨hOldSimple, hFreshSimple, fun x hx y hy he => hDisjoint hx (he ▸ hy)⟩)
  exact ⟨newBody, hNewRoutes, hSame, hAtZero, hPerm, hNodup,
    closed_word D a b link newBody first rest hNewRoutes hOrder⟩

end OverfullWork.DirectedAbsorbingLadder
