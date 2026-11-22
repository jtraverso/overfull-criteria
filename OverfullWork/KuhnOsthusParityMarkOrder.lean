module

public import OverfullWork.KuhnOsthusCycleAbsorberMarkOrder
public import OverfullWork.KuhnOsthusParityReserveOrder

@[expose] public section


/-! Read the three marked arcs per lane of B₁ from the two orbits
of its prescribed return. The six marks then have precisely the
first-return permutation required by (PCA6). -/
namespace OverfullWork.DirectedRobustExpansion

open Function
open scoped Classical
variable {V : Type*} [Fintype V]

theorem cycleAbsorberReturn_sameCycle {m : ℕ} (x y : Fin m × Fin 2) :
    (cycleAbsorberReturn m).SameCycle x y ↔ x.2 = y.2 := by
  let ρ := cycleAbsorberReturn m
  have hTrace (i : ℕ) : (ρ : Fin m × Fin 2 → Fin m × Fin 2)^[i] x =
      ((finRotate m : Fin m → Fin m)^[i] x.1,x.2) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [iterate_succ_apply',iterate_succ_apply',ih]
      rfl
  constructor
  · intro h
    obtain ⟨i,hi⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow,hTrace] at hi
    have he := congrArg (fun p : Fin m × Fin 2 => p.2) hi
    exact he
  · intro h
    have hc : (finRotate m).SameCycle x.1 y.1 := by
      by_cases hm : 2 ≤ m
      · exact (isCycle_finRotate_of_le hm).sameCycle (finRotate_interval_ne_self hm _)
          (finRotate_interval_ne_self hm _)
      · have hx := x.1.isLt
        have hy := y.1.isLt
        have he : x.1 = y.1 := Fin.ext (by omega)
        rw [he]
    obtain ⟨i,hi⟩ := hc.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow] at hi
    have he : ((finRotate m : Fin m → Fin m)^[i] x.1,x.2) = y := Prod.ext hi h
    have hcy := successor_sameCycle_iterate ρ x i
    rw [hTrace,he] at hcy
    exact hcy

/-- One seed label in each lane marks the two cycles of the physical
factor whose return advances the copy label. -/
theorem MarkedCycleSegments.bicycle_at_copy {σ : Equiv.Perm V} {m : ℕ}
    {mark : Fin m × Fin 2 ↪ V} (H : MarkedCycleSegments σ mark (cycleAbsorberReturn m))
    (j : Fin m) :
    MarkedBicycle σ (mark (j,cycleAbsorberLane false)) (mark (j,cycleAbsorberLane true)) := by
  refine ⟨?_,?_⟩
  · intro h
    exact Bool.false_ne_true (cycleAbsorberLane.injective (cycleAbsorberReturn_sameCycle _ _ |>.mp
      ((H.sameCycle _ _).mp h)))
  · intro v
    obtain ⟨⟨i,a⟩,h⟩ := H.cycle_meets_mark v
    obtain ⟨l,hl⟩ := cycleAbsorberLane.surjective a
    have hAt := (H.sameCycle (j,cycleAbsorberLane l) (i,a)).mpr
      ((cycleAbsorberReturn_sameCycle _ _).mpr hl)
    cases l
    · exact .inl (hAt.trans h)
    · exact .inr (hAt.trans h)

/-- Take the complete orbit trace at each of the two bicycle marks. -/
noncomputable def markedBicycle_return_segments (σ : Equiv.Perm V) (seed : Bool ↪ V)
    (H : MarkedBicycle σ (seed false) (seed true)) :
    MarkedCycleSegments σ seed (Equiv.refl Bool) := by
  let span (l : Bool) := minimalPeriod (σ : V → V) (seed l)
  refine ⟨span,fun l => minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts (seed l)),
    fun l => isPeriodicPt_minimalPeriod _ _,?_,?_⟩
  · intro l i hi hir k he
    by_cases h : l = k
    · subst k
      have hzero : (σ : V → V)^[i] (seed l) = (σ : V → V)^[0] (seed l) := he
      exact (Nat.ne_of_gt hi) (iterate_injOn_Iio_minimalPeriod hir (hi.trans hir) hzero)
    · have hcy := he ▸ successor_sameCycle_iterate σ (seed l) i
      cases l <;> cases k
      · exact h rfl
      · exact H.1 hcy
      · exact H.1 hcy.symm
      · exact h rfl
  · intro v
    have locate (l : Bool) (hn : σ.SameCycle (seed l) v) :
        ∃ d, d < span l ∧ (σ : V → V)^[d] (seed l) = v := by
      obtain ⟨d,hd⟩ := hn.exists_nat_pow_eq
      rw [Equiv.Perm.coe_pow] at hd
      have hp : 0 < span l := minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts (seed l))
      exact ⟨d % span l,Nat.mod_lt _ hp,iterate_mod_minimalPeriod_eq.trans hd⟩
    rcases H.2 v with h | h
    · obtain ⟨i,hi,he⟩ := locate false h
      exact ⟨false,i,hi,he⟩
    · obtain ⟨i,hi,he⟩ := locate true h
      exact ⟨true,i,hi,he⟩

def threeMarkOffset (u v : ℕ) (j : Fin 3) : ℕ :=
  if j = 0 then 0 else if j = 1 then u else v

/-- Cut the two orbit traces at the same two positive offsets. -/
noncomputable def parity_mark_subdivision {σ : Equiv.Perm V} {seed : Bool ↪ V}
    (H : MarkedCycleSegments σ seed (Equiv.refl Bool)) (u v : ℕ) (hu : 0 < u) (hv : u < v)
    (hSpan : ∀ l, v < H.span l) :
    MarkedSegmentSubdivision H (Equiv.prodCongr (Equiv.refl Bool) (finRotate 3)) := by
  let d (p : Bool × Fin 3) := if p.2 = 0 then u else if p.2 = 1 then v-u else H.span p.1-v
  refine ⟨Prod.fst,fun j => threeMarkOffset u v j.2,d,?_,?_,?_,?_⟩
  · rintro ⟨l,j⟩
    have := hSpan l
    fin_cases j <;> simp [d] <;> omega
  · rintro ⟨l,j⟩
    have := hSpan l
    fin_cases j <;> simp [d,threeMarkOffset] <;> omega
  · rintro ⟨l,j⟩
    have := hSpan l
    fin_cases j
    · exact .inl ⟨rfl,by simp [d,threeMarkOffset,finRotate_apply]⟩
    · exact .inl ⟨rfl,by simp [d,threeMarkOffset,finRotate_apply]; omega⟩
    · exact .inr ⟨rfl,rfl,by simp [d,threeMarkOffset]; omega⟩
  · intro l i hi
    have hS := hSpan l
    by_cases h₀ : i < u
    · refine ⟨(l,0),⟨rfl,by simp [threeMarkOffset],by simpa [threeMarkOffset,d]⟩,?_⟩
      rintro ⟨l',j⟩ ⟨rfl,hLo,_⟩
      fin_cases j <;> simp [threeMarkOffset] at hLo ⊢ <;> omega
    · by_cases h₁ : i < v
      · refine ⟨(l,1),⟨rfl,by simpa [threeMarkOffset] using Nat.le_of_not_gt h₀,?_⟩,?_⟩
        · simp [threeMarkOffset,d]
          omega
        · rintro ⟨l',j⟩ ⟨rfl,hLo,hHi⟩
          fin_cases j <;> simp [threeMarkOffset,d] at hLo hHi ⊢ <;> omega
      · refine ⟨(l,2),⟨rfl,by simpa [threeMarkOffset] using Nat.le_of_not_gt h₁,?_⟩,?_⟩
        · simp [threeMarkOffset,d]
          omega
        · rintro ⟨l',j⟩ ⟨rfl,hLo,hHi⟩
          fin_cases j <;> simp [threeMarkOffset,d] at hLo hHi ⊢ <;> omega

/-- The six physical marks in their required cyclic order. -/
theorem markedBicycle.exists_three_column_order (σ : Equiv.Perm V) (seed : Bool ↪ V)
    (H : MarkedBicycle σ (seed false) (seed true)) (u v : ℕ) (hu : 0 < u) (hv : u < v)
    (hPeriod : ∀ l, v < minimalPeriod (σ : V → V) (seed l)) :
    ∃ mark : Bool × Fin 3 ↪ V,
      Nonempty (MarkedCycleSegments σ mark (Equiv.prodCongr (Equiv.refl Bool) (finRotate 3))) ∧
      (∀ l, mark (l,0) = seed l) ∧
      (∀ l, mark (l,1) = (σ : V → V)^[u] (seed l)) ∧
      ∀ l, mark (l,2) = (σ : V → V)^[v] (seed l) := by
  let S := parity_mark_subdivision (markedBicycle_return_segments σ seed H) u v hu hv hPeriod
  refine ⟨S.mark,⟨S.segments⟩,?_,?_,?_⟩
  · intro l
    change (σ : V → V)^[threeMarkOffset u v 0] (seed l) = seed l
    simp [threeMarkOffset]
  · intro l
    change (σ : V → V)^[threeMarkOffset u v 1] (seed l) = _
    simp [threeMarkOffset]
  · intro l
    change (σ : V → V)^[threeMarkOffset u v 2] (seed l) = _
    simp [threeMarkOffset]

end OverfullWork.DirectedRobustExpansion
