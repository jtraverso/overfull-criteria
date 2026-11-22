module

public import OverfullWork.DirectedAbsorbingLadder

@[expose] public section


/-! The two directed rung families in Lo–Patel Definition 4.3. -/
namespace OverfullWork.DirectedAbsorbingLadder
open DirectedRobustExpansion DirectedAlternatingPaths DirectedListRoutes
variable {V : Type*} {D : Digraph V} {u v : V} {q : ℕ}

def evenLeft (i : Fin (q+1)) : Fin (4*q+2) := ⟨2*i.val, by have := i.isLt; omega⟩
def evenRight (i : Fin (q+1)) : Fin (4*q+2) := ⟨4*q+1-2*i.val, by omega⟩

private theorem Ladder.forward (A : Ladder D u v q) {a b : Fin (4*q+2)}
    (h : a.val+1 = b.val) (he : a.val % 2 = 0) : D.Adj (A.spine a) (A.spine b) := by
  let i : Fin (4*q+1) := ⟨a.val, by have := b.isLt; omega⟩
  have hi : i.castSucc = a := rfl
  have hj : i.succ = b := Fin.ext h
  have hArc := A.arcs i
  simpa only [step, show i.val % 2 = 0 from he, if_true, hi, hj] using hArc

private theorem Ladder.backward (A : Ladder D u v q) {a b : Fin (4*q+2)}
    (h : a.val+1 = b.val) (ho : a.val % 2 ≠ 0) : D.Adj (A.spine b) (A.spine a) := by
  let i : Fin (4*q+1) := ⟨a.val, by have := b.isLt; omega⟩
  have hi : i.castSucc = a := rfl
  have hj : i.succ = b := Fin.ext h
  have hArc := A.arcs i
  rw [step, if_neg (show i.val % 2 ≠ 0 from ho), hi, hj] at hArc
  exact hArc

private theorem Ladder.extend_crossing (A : Ladder D u v q) (i : Fin q)
    (p b : Fin (4*q+2)) (hpb : p ≠ b)
    (hpL : p ≠ left i) (hpR : p ≠ right i) (hbL : b ≠ left i) (hbR : b ≠ right i)
    (h₁ : D.Adj (A.spine p) (A.spine (left i)))
    (h₂ : D.Adj (A.spine (right i)) (A.spine b)) :
    Route D (A.spine p) (A.spine b) ((A.spine (left i) :: A.tail i) ++ [A.spine b]) ∧
      ((A.spine p :: A.spine (left i) :: A.tail i) ++ [A.spine b]).Nodup := by
  have hRoute : Route D (A.spine p) (A.spine (right i)) (A.spine (left i) :: A.tail i) :=
    ⟨.cons_cons h₁ (A.routes i).1, by simpa only [List.getLast?_cons_cons] using (A.routes i).2⟩
  refine ⟨snoc_route D hRoute h₂, ?_⟩
  have hFresh : ∀ a : Fin (4*q+2), a ≠ left i → a ≠ right i →
      A.spine a ∉ A.spine (left i) :: A.tail i := by
    intro a haL haR ha
    rcases A.meets_spine i _ ha ⟨a, rfl⟩ with h|h
    · exact haL (A.spine.injective h)
    · exact haR (A.spine.injective h)
  exact List.nodup_append.mpr
    ⟨List.nodup_cons.mpr ⟨hFresh p hpL hpR, A.simple i⟩, by simp,
      fun a ha w hw haw => by
        obtain rfl := List.mem_singleton.mp hw
        subst a
        rcases List.mem_cons.mp ha with he|he
        · exact hpb (A.spine.injective he.symm)
        · exact hFresh b hbL hbR he⟩

/-- The ordinary directed rung through the crossing path at odd position `2i+1`. -/
theorem Ladder.ordinary_rung (A : Ladder D u v q) (i : Fin q) :
    Route D (A.spine (evenLeft i.castSucc)) (A.spine (evenRight i.castSucc))
      ((A.spine (left i) :: A.tail i) ++ [A.spine (evenRight i.castSucc)]) ∧
    ((A.spine (evenLeft i.castSucc) :: A.spine (left i) :: A.tail i) ++
      [A.spine (evenRight i.castSucc)]).Nodup := by
  have hi := i.isLt
  apply A.extend_crossing i
  · intro h
    have hv := congrArg Fin.val h
    simp only [evenLeft, evenRight, Fin.val_castSucc] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [evenLeft, left, Fin.val_castSucc] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [evenLeft, right, Fin.val_castSucc] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [evenRight, left, Fin.val_castSucc] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [evenRight, right, Fin.val_castSucc] at hv
    omega
  · exact A.forward (by rfl) (by simp [evenLeft])
  · apply A.forward <;> simp only [right, evenRight, Fin.val_castSucc] <;> omega

/-- The alternative directed rung through the same crossing path. -/
theorem Ladder.alternative_rung (A : Ladder D u v q) (i : Fin q) :
    Route D (A.spine (evenLeft i.succ)) (A.spine (evenRight i.succ))
      ((A.spine (left i) :: A.tail i) ++ [A.spine (evenRight i.succ)]) ∧
    ((A.spine (evenLeft i.succ) :: A.spine (left i) :: A.tail i) ++
      [A.spine (evenRight i.succ)]).Nodup := by
  have hi := i.isLt
  apply A.extend_crossing i
  · intro h
    have hv := congrArg Fin.val h
    simp only [evenLeft, evenRight, Fin.val_succ] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [evenLeft, left, Fin.val_succ] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [evenLeft, right, Fin.val_succ] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [evenRight, left, Fin.val_succ] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [evenRight, right, Fin.val_succ] at hv
    omega
  · apply A.backward <;> simp only [evenLeft, left, Fin.val_succ] <;> omega
  · apply A.backward <;> simp only [right, evenRight, Fin.val_succ] <;> omega

/-- The central arc forms the final ordinary rung. -/
theorem Ladder.central_rung (A : Ladder D u v q) :
    D.Adj (A.spine (evenLeft (Fin.last q))) (A.spine (evenRight (Fin.last q))) := by
  apply A.forward <;> simp only [evenLeft, evenRight, Fin.val_last] <;> omega

end OverfullWork.DirectedAbsorbingLadder
