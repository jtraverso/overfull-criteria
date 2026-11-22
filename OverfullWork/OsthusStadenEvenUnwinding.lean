module

public import OverfullWork.OsthusStadenCycleUnwinding
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section


/-! The even first refinement required by Osthus–Staden §5.3. The
first refinement needs only a family of disjoint spanning cycles. -/
namespace OverfullWork.DirectedRobustExpansion

private def carryOrder (n s : ℕ) [NeZero s] : Fin n × ZMod s ≃ Fin (s*n) :=
  (Equiv.prodComm _ _).trans (((ZMod.finEquiv s).toEquiv.symm.prodCongr (Equiv.refl _)).trans finProdFinEquiv)

private theorem carry_val {n s : ℕ} [NeZero s] (x : Fin n × ZMod s) :
    (carryOrder n s x).val = x.1.val + n * x.2.val := by
  change x.1.val + n * ((ZMod.finEquiv s).symm x.2).val = _
  congr 1
  cases s
  · exact (NeZero.ne 0 rfl).elim
  · rfl

private theorem carry_step {n s : ℕ} [NeZero s] (x : Fin n × ZMod s) :
    (carryOrder n s).permCongr.symm (finRotate (s*n)) x =
      (finRotate n x.1, x.2 + if x.1.val+1 < n then 0 else 1) := by
  have hFin : 0 < n := x.1.pos
  have hS : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero (s*n) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  apply (carryOrder n s).injective
  rw [Equiv.permCongr_symm_apply, Equiv.apply_symm_apply]
  apply Fin.ext
  rw [carry_val,finRotate_apply,Fin.val_add,carry_val]
  have hv := ZMod.val_lt x.2
  have hOne : (1 : Fin (s*n)).val = 1 % (s*n) := rfl
  rw [hOne,Nat.add_mod_mod]
  split
  · rename_i h
    have hr : (finRotate n x.1).val = x.1.val+1 := by
      rw [finRotate_apply,Fin.val_add,show (1 : Fin n).val = 1%n from rfl,
        Nat.add_mod_mod,Nat.mod_eq_of_lt h]
    simp only [Prod.fst,Prod.snd,add_zero]
    rw [hr]
    have hBound : x.1.val+1 + n*x.2.val < s*n := by
      have hmul := Nat.mul_le_mul_left n (show x.2.val+1 ≤ s by omega)
      rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm n s] at hmul
      omega
    rw [show x.1.val + n*x.2.val + 1 = x.1.val+1+n*x.2.val by omega, Nat.mod_eq_of_lt hBound]
  · rename_i h
    have hLast : x.1.val+1 = n := by omega
    have hRot : (finRotate n x.1).val = 0 := by
      rw [finRotate_apply,Fin.val_add,show (1 : Fin n).val = 1%n from rfl,
        Nat.add_mod_mod,hLast,Nat.mod_self]
    simp only [Prod.fst,Prod.snd]
    rw [hRot,zero_add,show x.1.val+n*x.2.val+1 = n*(x.2.val+1) by
      rw [Nat.mul_add,Nat.mul_one]; omega]
    rw [ZMod.val_add,ZMod.val_one_eq_one_mod,Nat.add_mod_mod,Nat.mul_comm s n,Nat.mul_mod_mul_left]

private def evenUnwindingOffset (n m : ℕ) (d : Fin (2*m-1)) (j : Fin n) : ZMod (2*m) :=
  if n % 2 = 1 ∧ j.val+1 = n then (d.val : ZMod (2*m)) + (if d.val < m then d.val else d.val+1 : ℕ)
  else if j.val % 2 = 1 then d.val else 0

private def shiftCells {n s : ℕ} (a : Fin n → ZMod s) : Fin n × ZMod s ≃ Fin n × ZMod s :=
  Equiv.sigmaCongrRight (fun i => Equiv.addRight (a i)) |> fun e =>
    (Equiv.sigmaEquivProd _ _).symm.trans (e.trans (Equiv.sigmaEquivProd _ _))

private theorem even_label_injections (m : ℕ) (hm : 0 < m) :
    let a : Fin (2*m-1) → ZMod (2*m) := fun d => d.val
    let b : Fin (2*m-1) → ZMod (2*m) := fun d => (if d.val < m then d.val else d.val+1 : ℕ)
    Function.Injective a ∧ Function.Injective b ∧ Function.Injective (fun d => a d + b d) := by
  letI : NeZero (2*m) := ⟨by omega⟩
  dsimp
  refine ⟨?_,?_,?_⟩
  · intro d e he
    apply Fin.ext
    exact (ZMod.val_natCast_of_lt (show d.val < 2*m by have := d.isLt; omega)).symm.trans
      ((congrArg ZMod.val he).trans (ZMod.val_natCast_of_lt (show e.val < 2*m by have := e.isLt; omega)))
  · intro d e he
    have hd := d.isLt
    have he' := e.isLt
    have hb (j : Fin (2*m-1)) : (if j.val < m then j.val else j.val+1) < 2*m := by
      have := j.isLt
      split <;> omega
    have h := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (hb d), ZMod.val_natCast_of_lt (hb e)] at h
    apply Fin.ext
    split at h <;> split at h <;> omega
  · intro d e he
    have hd := d.isLt
    have he' := e.isLt
    have h := congrArg ZMod.val he
    simp only [← Nat.cast_add,ZMod.val_natCast] at h
    apply Fin.ext
    change (d.val + (if d.val < m then d.val else d.val+1)) % (2*m) =
      (e.val + (if e.val < m then e.val else e.val+1)) % (2*m) at h
    split at h <;> split at h
    · rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_sub_mod (show 2*m ≤ e.val+(e.val+1) by omega),
        Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_sub_mod (show 2*m ≤ d.val+(d.val+1) by omega),
        Nat.mod_eq_of_lt (show d.val+(d.val+1)-2*m < 2*m by omega),Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_sub_mod (show 2*m ≤ d.val+(d.val+1) by omega),
        Nat.mod_eq_sub_mod (show 2*m ≤ e.val+(e.val+1) by omega),
        Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at h
      omega

/-- The `2m`-fold blow-up of a cycle of length at least two contains
`2m−1` disjoint Hamilton cycles. -/
theorem exists_even_cycle_unwinding (n m : ℕ) (hn : 2 ≤ n) (hm : 0 < m) :
    ∃ F : Fin (2*m-1) → Equiv.Perm (Fin n × ZMod (2*m)),
      (∀ d x y, (F d).SameCycle x y) ∧
      (∀ d x, (F d x).1 = finRotate n x.1) ∧
      ∀ d e, d ≠ e → ∀ x, F d x ≠ F e x := by
  letI : NeZero (2*m) := ⟨by omega⟩
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero (2*m*n) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  let a := evenUnwindingOffset n m
  let e (d : Fin (2*m-1)) := (shiftCells (a d)).symm.trans (carryOrder n (2*m))
  let F (d : Fin (2*m-1)) := (e d).permCongr.symm (finRotate (2*m*n))
  have hStep d (x : Fin n × ZMod (2*m)) :
      F d x = (finRotate n x.1, x.2 - a d x.1 +
        (if x.1.val+1 < n then 0 else 1) + a d (finRotate n x.1)) := by
    have h := carry_step ((shiftCells (a d)).symm x)
    have h' := congrArg (shiftCells (a d)) h
    simpa [F,e,shiftCells,sub_eq_add_neg] using h'
  refine ⟨F,?_,fun d x => congrArg Prod.fst (hStep d x),?_⟩
  · intro d x y
    have hN : 2 ≤ 2*m*n := by nlinarith
    have hNo (z : Fin (2*m*n)) : finRotate (2*m*n) z ≠ z := by
      have := z.isLt
      rw [finRotate_apply]
      intro h
      have h' := congrArg Fin.val h
      rw [Fin.val_add,show (1 : Fin (2*m*n)).val = 1 % (2*m*n) from rfl,Nat.add_mod_mod] at h'
      by_cases hz : z.val+1 < 2*m*n
      · rw [Nat.mod_eq_of_lt hz] at h'
        omega
      · rw [Nat.mod_eq_sub_mod (show 2*m*n ≤ z.val+1 by omega),
          Nat.mod_eq_of_lt (by omega)] at h'
        omega
    have h := (isCycle_finRotate_of_le hN).sameCycle (hNo (e d x)) (hNo (e d y))
    obtain ⟨k,_,hk⟩ := h.exists_pow_eq'
    have h' := (conjugate_power (e d) (finRotate (2*m*n)) k x).trans hk
    rw [← (e d).injective h',Equiv.Perm.sameCycle_pow_right]
  · intro d d' hne x h
    obtain ⟨ha,hb,hab⟩ := even_label_injections m hm
    rw [hStep,hStep] at h
    have h' := congrArg Prod.snd h
    have hx := x.1.isLt
    simp only [Prod.snd] at h'
    by_cases hlt : x.1.val+1 < n
    · have hr : (finRotate n x.1).val = x.1.val+1 := by
        rw [finRotate_apply,Fin.val_add,show (1 : Fin n).val = 1%n from rfl,
          Nat.add_mod_mod,Nat.mod_eq_of_lt hlt]
      simp only [hlt,if_true,add_zero] at h' 
      by_cases hlast : n%2=1 ∧ x.1.val+2=n
      · have hp : x.1.val%2=1 := by omega
        simp only [a,evenUnwindingOffset,hr] at h'
        simp [show x.1.val+1 ≠ n by omega,hlast, hp] at h'
        apply hne (hb ?_)
        simp only [Nat.cast_ite, Nat.cast_add, Nat.cast_one]
        linear_combination h' 
      · by_cases hp : x.1.val%2=1
        · have hp' : (x.1.val+1)%2 ≠ 1 := by omega
          simp only [a,evenUnwindingOffset,hr] at h'
          simp [show x.1.val+1 ≠ n by omega,hlast,hp,hp'] at h'
          exact hne (ha h')
        · have hp' : (x.1.val+1)%2 = 1 := by omega
          simp only [a,evenUnwindingOffset,hr] at h'
          simp [show x.1.val+1 ≠ n by omega,hlast,hp,hp'] at h'
          apply hne (ha ?_)
          linear_combination h'
    · have hLast : x.1.val+1 = n := by omega
      have hr : (finRotate n x.1).val = 0 := by
        rw [finRotate_apply,Fin.val_add,show (1 : Fin n).val = 1%n from rfl,
          Nat.add_mod_mod,hLast,Nat.mod_self]
      simp only [hlt,if_false] at h'
      by_cases hOdd : n%2=1
      · simp only [a,evenUnwindingOffset,hr] at h'
        simp [hLast,hOdd,show 1 ≠ n by omega] at h'
        apply hne (hab ?_)
        simpa only [Nat.cast_ite, Nat.cast_add, Nat.cast_one] using h' 
      · have hp : x.1.val%2=1 := by omega
        simp only [a,evenUnwindingOffset,hr] at h'
        simp [hLast,hOdd,hp] at h'
        exact hne (ha h')

end OverfullWork.DirectedRobustExpansion
