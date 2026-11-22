module

public import OverfullWork.DirectedLadderAbsorption

@[expose] public section


/-! The ordinary rungs of an absorbing ladder are a disjoint family of paths. -/
namespace OverfullWork.DirectedAbsorbingLadder

open Finset DirectedListRoutes
open scoped Classical
variable {V : Type*} {D : Digraph V} {u v : V} {q : ℕ}

def Ladder.ordinaryVertices (A : Ladder D u v q) (i : Fin (q+1)) : List V :=
  A.spine (evenLeft i) :: (A.middle i ++ [A.spine (evenRight i)])

theorem Ladder.ordinaryVertices_nodup (A : Ladder D u v q) (i : Fin (q+1)) :
    (A.ordinaryVertices i).Nodup := by
  induction i using Fin.lastCases with
  | last =>
    simp [Ladder.ordinaryVertices, Ladder.middle]
    intro he
    have h := congrArg Fin.val he
    simp only [evenLeft, evenRight, Fin.val_last] at h
    omega
  | cast i => simpa [Ladder.ordinaryVertices, Ladder.middle] using (A.ordinary_rung i).2

private theorem Ladder.middle_disjoint (A : Ladder D u v q) (i j : Fin (q+1)) (h : i ≠ j) :
    List.Disjoint (A.middle i) (A.middle j) := by
  induction i using Fin.lastCases with
  | last => simp [Ladder.middle]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Ladder.middle]
    | cast j =>
      have hij : i ≠ j := fun he => h (congrArg Fin.castSucc he)
      simpa [Ladder.middle] using A.disjoint i j hij

private theorem Ladder.even_not_middle (A : Ladder D u v q) (i j : Fin (q+1)) :
    A.spine (evenLeft i) ∉ A.middle j ∧ A.spine (evenRight i) ∉ A.middle j := by
  induction j using Fin.lastCases with
  | last => simp [Ladder.middle]
  | cast j =>
    simp only [Ladder.middle, Fin.snoc_castSucc]
    have hi := i.isLt
    have hj := j.isLt
    constructor <;> intro h
    · rcases A.meets_spine j _ h ⟨_, rfl⟩ with he|he
      · have hv := congrArg Fin.val (A.spine.injective he)
        simp only [evenLeft, left] at hv
        omega
      · have hv := congrArg Fin.val (A.spine.injective he)
        simp only [evenLeft, right] at hv
        omega
    · rcases A.meets_spine j _ h ⟨_, rfl⟩ with he|he
      · have hv := congrArg Fin.val (A.spine.injective he)
        simp only [evenRight, left] at hv
        omega
      · have hv := congrArg Fin.val (A.spine.injective he)
        simp only [evenRight, right] at hv
        omega

/-- Two distinct ordinary rungs of a ladder have no common vertices. -/
theorem Ladder.ordinaryVertices_disjoint (A : Ladder D u v q) (i j : Fin (q+1))
    (h : i ≠ j) : List.Disjoint (A.ordinaryVertices i) (A.ordinaryVertices j) := by
  intro w hi hj
  simp only [Ladder.ordinaryVertices, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi hj
  have hLeft : A.spine (evenLeft i) ≠ A.spine (evenLeft j) := by
    intro he
    apply h
    apply Fin.ext
    have hv := congrArg Fin.val (A.spine.injective he)
    simp only [evenLeft] at hv
    omega
  have hRight : A.spine (evenRight i) ≠ A.spine (evenRight j) := by
    intro he
    apply h
    apply Fin.ext
    have h₁ := i.isLt
    have h₂ := j.isLt
    have hv := congrArg Fin.val (A.spine.injective he)
    simp only [evenRight] at hv
    omega
  have hApart : ∀ a b, A.spine (evenLeft a) ≠ A.spine (evenRight b) := by
    intro a b he
    have hb := b.isLt
    have hv := congrArg Fin.val (A.spine.injective he)
    simp only [evenLeft, evenRight] at hv
    omega
  have hOut := A.even_not_middle i j
  have hOut' := A.even_not_middle j i
  have hMiddle := A.middle_disjoint i j h
  rcases hi with rfl|hi|rfl
  · exact hj.elim hLeft (fun hm => hm.elim hOut.1 (hApart i j))
  · rcases hj with rfl|hj|rfl
    · exact hOut'.1 hi
    · exact hMiddle hi hj
    · exact hOut'.2 hi
  · exact hj.elim (fun he => hApart j i he.symm) (fun hm => hm.elim hOut.2 hRight)

/-- Each ordinary rung is contained in the support of the ladder. -/
theorem Ladder.ordinaryVertices_mem (A : Ladder D u v q) (i : Fin (q+1)) {w : V}
    (hw : w ∈ A.ordinaryVertices i) : w ∈ A.vertices := by
  simp only [Ladder.ordinaryVertices, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|hw|rfl
  · exact mem_union_left _ (mem_image_of_mem _ (mem_univ (evenLeft i)))
  · induction i using Fin.lastCases with
    | last => simp [Ladder.middle] at hw
    | cast i =>
      exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _,
        List.mem_toFinset.mpr (by simpa [Ladder.middle] using hw)⟩)
  · exact mem_union_left _ (mem_image_of_mem _ (mem_univ (evenRight i)))

end OverfullWork.DirectedAbsorbingLadder
