module

public import OverfullWork.KuhnOsthusClosedCycleReserve
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section


/-! Check (CyA3) on the physical reserve. Its two cycles preserve
the rows, and successive marked edges are exactly the prescribed
switches in column order. -/
namespace OverfullWork.DirectedRobustExpansion

open Function Finset
open scoped Classical
variable {V : Type*}

structure CycleAbsorberMarkedRows (σ : Equiv.Perm V) (m : ℕ) where
  mark : Bool × Fin (2*m+1) ↪ V
  order : MarkedCycleSegments σ mark (Equiv.prodCongr (Equiv.refl Bool) (finRotate (2*m+1)))
  bicycle : MarkedBicycle σ (mark (false,Fin.last (2*m))) (mark (true,Fin.last (2*m)))

theorem CycleAbsorberMarkedRows.orderedReserve {σ : Equiv.Perm V} {m : ℕ}
    (R : CycleAbsorberMarkedRows σ m) :
    OrderedReserve σ R.mark (finRotate (2*m+1)) :=
  ⟨_,⟨R.order⟩,fun _ => rfl⟩

variable [Fintype V]

/-- The two origins used by the final repair belong to different
cycles. Both cycles contain their entire rows of marks. -/
theorem OrderedClusterPaths.exists_marked_rows {G : Digraph V} {A : ℕ → Finset V} {m : ℕ}
    (S : OrderedClusterPaths G A (Fin m × Fin 2) 3 12) (hm : 0 < m)
    (σ : Equiv.Perm V)
    (H : MarkedCycleSegments σ
      ((S.orderAt 3 le_rfl (by decide)).toEmbedding.trans (Embedding.subtype (· ∈ A 3)))
      (cycleAbsorberReturn m))
    (hSpan : ∀ j, 8 < H.span j)
    (hTrace : ∀ j i, i ≤ 9 →
      (σ : V → V)^[i] (S.vertex 3 j) = S.vertex (3+i) j) :
    ∃ R : CycleAbsorberMarkedRows σ m,
      (∀ i b, R.mark (b,cycleAbsorberColumn i 0) = S.vertex 3 (i,cycleAbsorberLane b) ∧
        σ (R.mark (b,cycleAbsorberColumn i 0)) = S.vertex 4 (i,cycleAbsorberLane b)) ∧
      (∀ i b, R.mark (b,cycleAbsorberColumn i 1) = S.vertex 7 (i,cycleAbsorberLane b) ∧
        σ (R.mark (b,cycleAbsorberColumn i 1)) = S.vertex 8 (i,cycleAbsorberLane b)) ∧
      ∀ b, R.mark (b,Fin.last (2*m)) = S.vertex 11 (cycleAbsorberLastCopy m hm,cycleAbsorberLane b) ∧
        σ (R.mark (b,Fin.last (2*m))) = S.vertex 12 (cycleAbsorberLastCopy m hm,cycleAbsorberLane b) := by
  let D := cycleAbsorberMarkSubdivision hm H hSpan
  let M := D.mark
  let τ : Equiv.Perm (Bool × Fin (2*m+1)) :=
    Equiv.prodCongr (Equiv.refl Bool) (finRotate (2*m+1))
  have hM (b : Bool) (j : Fin (2*m+1)) :
      M (b,j) = (σ : V → V)^[(cycleAbsorberColumnCoordinates hm j).2]
        (S.vertex 3 ((cycleAbsorberColumnCoordinates hm j).1,cycleAbsorberLane b)) := rfl
  have hNext (b : Bool) (j : Fin (2*m+1)) :
      σ (M (b,j)) = (σ : V → V)^[(cycleAbsorberColumnCoordinates hm j).2+1]
        (S.vertex 3 ((cycleAbsorberColumnCoordinates hm j).1,cycleAbsorberLane b)) := by
    rw [hM,iterate_succ_apply']
  have hApart : ¬ τ.SameCycle (false,Fin.last (2*m)) (true,Fin.last (2*m)) := by
    intro h
    obtain ⟨i,hi⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow] at hi
    have hPreserves (k : ℕ) :
        (((τ : Bool × Fin (2*m+1) → Bool × Fin (2*m+1))^[k]) (false,Fin.last (2*m))).1 = false := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        exact ih
    have hbad := hPreserves i
    rw [hi] at hbad
    cases hbad
  have hCyclic (c : Fin (2*m+1)) : (finRotate (2*m+1)).SameCycle c (Fin.last (2*m)) := by
    have hN : 2 ≤ 2*m+1 := by omega
    exact (isCycle_finRotate_of_le hN).sameCycle
      (finRotate_interval_ne_self hN c) (finRotate_interval_ne_self hN _)
  have hO : OrderedReserve σ M (finRotate (2*m+1)) := ⟨τ,⟨D.segments⟩,fun _ => rfl⟩
  have hB : MarkedBicycle σ (M (false,Fin.last (2*m))) (M (true,Fin.last (2*m))) :=
    ⟨fun h => hApart ((D.segments.sameCycle _ _).mp h),hO.cycle_meets_column _ hCyclic⟩
  refine ⟨⟨M,D.segments,hB⟩,?_,?_,?_⟩
  · intro i b
    change M (b,cycleAbsorberColumn i 0) = _ ∧ σ (M (b,cycleAbsorberColumn i 0)) = _
    constructor
    · rw [hM,cycleAbsorberColumnCoordinates_column]
      rfl
    · rw [hNext,cycleAbsorberColumnCoordinates_column]
      exact hTrace _ 1 (by decide)
  · intro i b
    change M (b,cycleAbsorberColumn i 1) = _ ∧ σ (M (b,cycleAbsorberColumn i 1)) = _
    constructor
    · rw [hM,cycleAbsorberColumnCoordinates_column]
      exact hTrace _ 4 (by decide)
    · rw [hNext,cycleAbsorberColumnCoordinates_column]
      exact hTrace _ 5 (by decide)
  · intro b
    change M (b,Fin.last (2*m)) = _ ∧ σ (M (b,Fin.last (2*m))) = _
    constructor
    · rw [hM,cycleAbsorberColumnCoordinates_last]
      exact hTrace _ 8 (by decide)
    · rw [hNext,cycleAbsorberColumnCoordinates_last]
      exact hTrace _ 9 (by decide)

end OverfullWork.DirectedRobustExpansion
