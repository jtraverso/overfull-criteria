module

public import OverfullWork.KuhnOsthusMarkedTours

@[expose] public section


/-! The order condition (PCA6) of Kühn–Osthus. The three columns
carry the first repair, the second repair, and the triple switch. -/
namespace OverfullWork.DirectedRobustExpansion

open Function
open scoped Classical
variable {V : Type*} [Fintype V]

private def parityMarkNext : Equiv.Perm (Bool × Fin 3) :=
  Equiv.prodCongr (Equiv.refl Bool) (finRotate 3)

private noncomputable def parityMarkDoubleSwitch : Equiv.Perm (Bool × Fin 3) :=
  switchSuccessors (switchSuccessors parityMarkNext (false,0) (true,0)) (false,1) (true,1)

private def parityMarkLane (a : Bool × Fin 3) : Bool :=
  xor a.1 (a.2 == 1)

private theorem parity_mark_lane_invariant (a : Bool × Fin 3) :
    parityMarkLane (parityMarkDoubleSwitch a) = parityMarkLane a := by
  obtain ⟨lane,c⟩ := a
  cases lane <;> fin_cases c <;>
    simp [parityMarkLane,parityMarkDoubleSwitch,switchSuccessors,parityMarkNext,
      Equiv.swap_apply_def,finRotate_apply]

private theorem parity_marks_apart :
    ¬ parityMarkDoubleSwitch.SameCycle (false,2) (true,2) := by
  intro h
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hk
  have hTrace (n : ℕ) :
      parityMarkLane ((parityMarkDoubleSwitch : Bool × Fin 3 → Bool × Fin 3)^[n] (false,2)) =
        parityMarkLane (false,2) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [iterate_succ_apply',parity_mark_lane_invariant,ih]
  have he := hTrace k
  rw [hk] at he
  revert he
  decide

private theorem parity_column_reaches (i : Fin 3) : (finRotate 3).SameCycle i 2 := by
  fin_cases i
  · exact successor_sameCycle_iterate (finRotate 3) 0 2
  · exact successor_sameCycle_iterate (finRotate 3) 1 1
  · exact Equiv.Perm.SameCycle.refl _ _


/-- After both pair exchanges the reserve is again a bicycle. The
third-column marks for the triple exchange lie on distinct cycles. -/
theorem pca6_double_exchange_markedBicycle (B : Equiv.Perm V) (mark : Bool × Fin 3 ↪ V)
    (H : MarkedCycleSegments B mark (Equiv.prodCongr (Equiv.refl Bool) (finRotate 3))) :
    MarkedBicycle
      (switchSuccessors (switchSuccessors B (mark (false,0)) (mark (true,0)))
        (mark (false,1)) (mark (true,1)))
      (mark (false,2)) (mark (true,2)) := by
  let B' := switchSuccessors (switchSuccessors B (mark (false,0)) (mark (true,0)))
    (mark (false,1)) (mark (true,1))
  have H' : MarkedCycleSegments B' mark parityMarkDoubleSwitch :=
    (H.switch (false,0) (true,0)).switch (false,1) (true,1)
  have hApart : ¬ B'.SameCycle (mark (false,2)) (mark (true,2)) :=
    fun h => parity_marks_apart ((H'.sameCycle (false,2) (true,2)).mp h)
  have hOrder : OrderedReserve B mark (finRotate 3) := ⟨_,⟨H⟩,fun _ => rfl⟩
  exact ⟨hApart, ((hOrder.switch 0).switch 1).cycle_meets_column 2 parity_column_reaches⟩

private theorem parity_mark_next_preserves_lane (a : Bool × Fin 3) :
    (parityMarkNext a).1 = a.1 := rfl

private theorem parity_mark_next_apart (c : Fin 3) :
    ¬ parityMarkNext.SameCycle (false,c) (true,c) := by
  intro h
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hk
  have hTrace (n : ℕ) :
      ((parityMarkNext : Bool × Fin 3 → Bool × Fin 3)^[n] (false,c)).1 = false := by
    induction n with
    | zero => rfl
    | succ n ih => rw [iterate_succ_apply',parity_mark_next_preserves_lane,ih]
  have he := hTrace k
  rw [hk] at he
  cases he

/-- The initial third reserve is a marked bicycle at each of its
three switch columns. -/
theorem pca6_initial_markedBicycle (B : Equiv.Perm V) (mark : Bool × Fin 3 ↪ V)
    (H : MarkedCycleSegments B mark (Equiv.prodCongr (Equiv.refl Bool) (finRotate 3))) (c : Fin 3) :
    MarkedBicycle B (mark (false,c)) (mark (true,c)) := by
  have hReach (a : Fin 3) : (finRotate 3).SameCycle a c :=
    (parity_column_reaches a).trans (parity_column_reaches c).symm
  have hOrder : OrderedReserve B mark (finRotate 3) := ⟨_,⟨H⟩,fun _ => rfl⟩
  exact ⟨fun h => parity_mark_next_apart c ((H.sameCycle (false,c) (true,c)).mp h),
    hOrder.cycle_meets_column c hReach⟩

end OverfullWork.DirectedRobustExpansion
