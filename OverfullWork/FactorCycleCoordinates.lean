module

public import OverfullWork.OsthusStadenCycleUnwinding

@[expose] public section


/-! Index the cycles of an actual factor by its orbits, with positions
given by the least period of one representative in each orbit. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset Function DirectedPrefactor
open scoped Classical
universe u

structure FactorCycleCoordinates {V : Type u} (σ : Equiv.Perm V) where
  Orb : Type u
  length : Orb → ℕ
  order : (Σ i, Fin (length i)) ≃ V
  length_ge_two : ∀ i, 2 ≤ length i
  successor : ∀ i j, σ (order ⟨i,j⟩) = order ⟨i,finRotate (length i) j⟩
  same_orbit : ∀ i j (a : Fin (length i)) (b : Fin (length j)),
    σ.SameCycle (order ⟨i,a⟩) (order ⟨j,b⟩) ↔ i = j

noncomputable def factorCycleCoordinates {V : Type u} [Fintype V] (σ : Equiv.Perm V)
    (hFixed : ∀ v, σ v ≠ v) : FactorCycleCoordinates σ := by
  let S := Equiv.Perm.SameCycle.setoid σ
  let Q := Quotient S
  let f : V → V := σ
  let n (i : Q) := minimalPeriod f i.out
  let c (i : Q) (j : Fin (n i)) := f^[j.val] i.out
  have hTag (i : Q) (j : Fin (n i)) : (Quotient.mk S (c i j)) = i := by
    have hh : σ.SameCycle i.out (c i j) := by
      rw [show c i j = (σ^j.val) i.out by simp [c,f,Equiv.Perm.coe_pow]]
      exact (Equiv.Perm.SameCycle.refl σ _).pow_right
    exact (Quotient.sound hh.symm).trans (Quotient.out_eq i)
  let g : (Σ i, Fin (n i)) → V := fun x => c x.1 x.2
  have hInj : Function.Injective g := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    have h := congrArg (Quotient.mk S) he
    change Quotient.mk S (c i a) = Quotient.mk S (c j b) at h
    rw [hTag,hTag] at h
    subst j
    congr 1
    exact Fin.ext (iterate_injOn_Iio_minimalPeriod a.isLt b.isLt he)
  have hOnto : Function.Surjective g := by
    intro x
    let i : Q := Quotient.mk S x
    have hi : σ.SameCycle i.out x := Quotient.exact (Quotient.out_eq i)
    have hmem := (orbit_mem_iff σ i.out x).mpr hi
    rw [orbit_eq_forward_trace] at hmem
    obtain ⟨k,hk,he⟩ := mem_image.mp hmem
    exact ⟨⟨i,⟨k,mem_range.mp hk⟩⟩,he⟩
  let e := Equiv.ofBijective g ⟨hInj,hOnto⟩
  have hPos (i : Q) : 0 < n i :=
    minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts i.out)
  refine ⟨Q,n,e,?_,?_,?_⟩
  · intro i
    by_contra! h
    have hOne : n i = 1 := by have := hPos i; omega
    have he : f^[n i] i.out = i.out := isPeriodicPt_minimalPeriod f i.out
    rw [hOne,iterate_one] at he
    exact hFixed i.out he
  · intro i j
    letI : NeZero (n i) := ⟨(hPos i).ne'⟩
    change f (f^[j.val] i.out) = f^[(finRotate (n i) j).val] i.out
    rw [←iterate_succ_apply' f j.val i.out]
    have he : (finRotate (n i) j).val = (j.val+1) % n i := by
      rw [finRotate_apply,Fin.add_def]
      have := j.isLt
      have hp := hPos i
      by_cases h : n i = 1
      · simp [h]
      · rw [show ((1 : Fin (n i)):ℕ) = 1 by
          simp [Fin.val_one, Nat.mod_eq_of_lt (show 1 < n i by omega)]]
    rw [he,iterate_mod_minimalPeriod_eq]
  · intro i j a b
    constructor
    · intro h
      exact (hTag i a).symm.trans ((Quotient.sound h).trans (hTag j b))
    · intro h
      subst j
      exact Quotient.exact ((hTag i a).trans (hTag i b).symm)

end OverfullWork.DirectedRobustExpansion
