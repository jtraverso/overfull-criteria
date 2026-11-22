module

public import OverfullWork.CMSOperation41LowSide

@[expose] public section


/-! Physical arms of the even matching skeleton in CMS Case S2.1.
The optional representative edge is kept as an actual original edge. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PaperLowSkeleton LowSkeletonPreparation
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1800000 in
theorem low_skeleton_arms {G M : SimpleGraph V} [DecidableRel M.Adj]
    {W U Z : Finset V} (hWU : W ⊆ U)
    (hM : IsSkeleton G M W)
    (P : LowSkeletonProjection.Projection G (outerLeaves M W) U Z) :
    ∃ (low : outerLeaves M W → V) (arm : outerLeaves M W → List V),
      (∀ a,low a ∈ W ∧ M.Adj (low a) a.val) ∧
      (∀ a,(arm a).Nodup ∧ (arm a).IsChain G.Adj ∧
        (arm a).head? = some (low a) ∧ (arm a).getLast? = some (P.representative a).val) ∧
      (∀ a v,v ∈ arm a → (v ∉ U ↔ v = (P.representative a).val)) ∧
      (∀ a b,a ≠ b → ∀ v,v ∈ arm a → v ∈ arm b → v = low a ∧ v = low b) ∧
      (∀ a,a.val ∉ U → arm a = [low a,a.val]) ∧
      (∀ a,arm a = low a :: a.val :: (if a.val ∈ U then [(P.representative a).val] else [])) ∧
      (∀ a v,v ∈ arm a → v ∈ U → v ∉ W → v = a.val) := by
  let A := outerLeaves M W
  have hLow (a : A) : ∃ v ∈ W,M.Adj v a.val := by
    have hD := (mem_filter.mp a.property).2
    obtain ⟨u,hu⟩ := (M.degree_pos_iff_exists_adj a.val).mp (by omega)
    have ha := mem_compl.mp (mem_filter.mp a.property).1
    rcases hM.crosses a.val u hu with he|he
    · exact False.elim (ha he.1)
    · exact ⟨u,he.1,hu.symm⟩
  choose l hl hAdj using hLow
  let rep (a : A) : V := (P.representative a).val
  have hRep (a : A) : rep a ∉ U := mem_compl.mp (P.representative a).property
  have hLowU (a : A) : l a ∈ U := hWU (hl a)
  have hAway (a : A) : a.val ∉ W := mem_compl.mp (mem_filter.mp a.property).1
  let arm (a : A) : List V :=
    if a.val ∈ U then [l a,a.val,rep a] else [l a,rep a]
  have hArm (a : A) : (arm a).Nodup ∧ (arm a).IsChain G.Adj ∧
      (arm a).head? = some (l a) ∧ (arm a).getLast? = some (rep a) := by
    have h₁ : l a ≠ a.val := (hAdj a).ne
    have h₂ : l a ≠ rep a := fun h => hRep a (h ▸ hLowU a)
    by_cases hU : a.val ∈ U
    · have h₃ : a.val ≠ rep a := fun h => hRep a (h ▸ hU)
      have hEdge : G.Adj a.val (rep a) := P.neighbour a hU
      have hFirst : G.Adj (l a) a.val := hM.le_graph (hAdj a)
      simp [arm,hU,h₁,h₂,h₃,List.isChain_cons_cons,hEdge,hFirst]
    · have hEdge : G.Adj (l a) (rep a) := by
        rw [show rep a = a.val from P.fixed a hU]
        exact hM.le_graph (hAdj a)
      simp [arm,hU,h₂,List.isChain_cons_cons,hEdge]
  have hMem (a : A) (v : V) :
      v ∈ arm a ↔ v = l a ∨ v = rep a ∨ (a.val ∈ U ∧ v = a.val) := by
    by_cases h : a.val ∈ U <;> simp [arm,h,or_left_comm,or_comm]
  have hOutside (a : A) (v : V) (hv : v ∈ arm a) : v ∉ U ↔ v = rep a := by
    constructor
    · intro h
      rcases (hMem a v).mp hv with he|he|⟨hu,he⟩
      · exact False.elim (h (he.symm ▸ hLowU a))
      · exact he
      · exact False.elim (h (he.symm ▸ hu))
    · rintro rfl
      exact hRep a
  refine ⟨l,arm,fun a => ⟨hl a,hAdj a⟩,hArm,hOutside,?_,
    fun a ha => by simp [arm,ha,rep,P.fixed a ha],?_,?_⟩
  case refine_2 =>
    intro a
    by_cases ha : a.val ∈ U
    · simp [arm,ha,rep]
    · simp [arm,ha,rep,P.fixed a ha]
  case refine_3 =>
    intro a v hv hu hw
    rcases (hMem a v).mp hv with h | h | ⟨_,h⟩
    · exact (hw (h.symm ▸ hl a)).elim
    · exact (hRep a (h ▸ hu)).elim
    · exact h
  intro a b hab v hva hvb
  by_cases hv : v ∉ U
  · have he : rep a = rep b := ((hOutside a v hva).mp hv).symm.trans ((hOutside b v hvb).mp hv)
    exact (hab (P.injective (Subtype.ext he))).elim
  · by_cases hW : v ∈ W
    · have hOnly (c : A) (hc : v ∈ arm c) : v = l c := by
        rcases (hMem c v).mp hc with h|h|⟨_,h⟩
        · exact h
        · exact False.elim (hv (h.symm ▸ hRep c))
        · exact False.elim (hAway c (h ▸ hW))
      exact ⟨hOnly a hva,hOnly b hvb⟩
    · have hOnly (c : A) (hc : v ∈ arm c) : v = c.val := by
        rcases (hMem c v).mp hc with h|h|⟨_,h⟩
        · exact False.elim (hW (h.symm ▸ hl c))
        · exact False.elim (hv (h.symm ▸ hRep c))
        · exact h
      exact (hab (Subtype.ext ((hOnly a hva).symm.trans (hOnly b hvb)))).elim

set_option maxHeartbeats 1800000 in
theorem matching_skeleton_arms {G M : SimpleGraph V} [DecidableRel M.Adj]
    {W U Z : Finset V} (hWU : W ⊆ U)
    (hM : IsSkeleton G M W) (hMatch : OneFactor.IsMatchingGraph M)
    (P : LowSkeletonProjection.Projection G (outerLeaves M W) U Z) :
    ∃ (low : outerLeaves M W ↪ V) (arm : outerLeaves M W → List V),
      (∀ a,low a ∈ W ∧ M.Adj (low a) a.val) ∧
      (∀ a,(arm a).Nodup ∧ (arm a).IsChain G.Adj ∧
        (arm a).head? = some (low a) ∧ (arm a).getLast? = some (P.representative a).val) ∧
      (∀ a v,v ∈ arm a → (v ∉ U ↔ v = (P.representative a).val)) ∧
      (∀ a b,a ≠ b → List.Disjoint (arm a) (arm b)) ∧
      (∀ a,a.val ∉ U → arm a = [low a,a.val]) ∧
      (∀ a,arm a = low a :: a.val :: (if a.val ∈ U then [(P.representative a).val] else [])) ∧
      (∀ a v,v ∈ arm a → v ∈ U → v ∉ W → v = a.val) := by
  obtain ⟨l,arm,hLow,hArm,hOutside,hInter,hFixed,hShape,hLeaf⟩ := low_skeleton_arms hWU hM P
  have hInj : Function.Injective l := by
    intro a b he
    apply Subtype.ext
    exact hMatch (l a) a.val b.val (hLow a).2 (he.symm ▸ (hLow b).2)
  refine ⟨⟨l,hInj⟩,arm,hLow,hArm,hOutside,?_,hFixed,hShape,hLeaf⟩
  intro a b hab v hva hvb
  obtain ⟨ha,hb⟩ := hInter a b hab v hva hvb
  exact hab (hInj (ha.symm.trans hb))

/-- Pair two disjoint arms at their low endpoints. All consecutive
pairs are physical except for the designated join between the leaves. -/
theorem join_projected_arms (G : SimpleGraph V) (A B : List V) (x y : V)
    (hAHead : A.head? = some x) (hBHead : B.head? = some y)
    (hASimple : A.Nodup) (hBSimple : B.Nodup) (hDis : List.Disjoint A B)
    (hA : A.IsChain G.Adj) (hB : B.IsChain G.Adj) :
    let T := A.reverse ++ B
    T.Nodup ∧ T.head? = A.getLast? ∧ T.getLast? = B.getLast? ∧
      T.IsChain (fun u v => G.Adj u v ∨ (u=x ∧ v=y)) ∧
      List.IsInfix [x,y] T := by
  intro T
  have hAB : A.reverse ≠ [] := by
    intro h
    have he : A = [] := List.reverse_eq_nil_iff.mp h
    simp [he] at hAHead
  have hBN : B ≠ [] := by intro h; simp [h] at hBHead
  have hN : T.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.nodup_reverse.mpr hASimple,hBSimple,?_⟩
    intro u hu v hv he
    subst v
    exact hDis (List.mem_reverse.mp hu) hv
  have hHead : T.head? = A.getLast? := by
    change (A.reverse ++ B).head? = _
    rw [List.head?_append_of_ne_nil _ hAB,List.head?_reverse]
  have hLast : T.getLast? = B.getLast? := List.getLast?_append_of_ne_nil _ hBN
  have hChain : T.IsChain (fun u v => G.Adj u v ∨ (u=x ∧ v=y)) := by
    apply List.IsChain.append
    · have hReverse : A.reverse.IsChain G.Adj := List.isChain_reverse.mpr (hA.imp (fun _ _ he => he.symm))
      exact hReverse.imp (fun _ _ he => Or.inl he)
    · exact hB.imp (fun _ _ he => Or.inl he)
    · intro u hu v hv
      rw [List.getLast?_reverse,hAHead] at hu
      rw [hBHead] at hv
      exact Or.inr ⟨(Option.mem_some_iff.mp hu).symm,(Option.mem_some_iff.mp hv).symm⟩
  refine ⟨hN,hHead,hLast,hChain,?_⟩
  subst T
  cases A with
  | nil => simp at hAHead
  | cons a A =>
    cases B with
    | nil => simp at hBHead
    | cons b B =>
      have ha : a=x := Option.some.inj hAHead
      have hb : b=y := Option.some.inj hBHead
      subst a
      subst b
      exact ⟨A.reverse,B,by simp [List.reverse_cons,List.append_assoc]⟩


end OverfullWork.CMSTrimmingRound
