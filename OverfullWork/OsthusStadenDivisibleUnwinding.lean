module

public import OverfullWork.OsthusStadenCoprimeUnwinding
public import OverfullWork.FactorMergeCoarsening
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section


/-! When the prime divides the cluster count, subdivide the wrap of
the shortened cycle with two extra clusters. Their increments are d
and -d, so each increment still identifies its own lifted cycle. -/
namespace OverfullWork.DirectedRobustExpansion
open scoped Classical

def extendedShift (n p : ℕ) (d : ZMod p) (i : Fin (n+2)) : ZMod p :=
  if i.val = n+1 then -d else d

def extendedUnwinding (n p : ℕ) (d : ZMod p) : Equiv.Perm (Fin (n+2) × ZMod p) where
  toFun x := (finRotate (n+2) x.1,x.2+extendedShift n p d x.1)
  invFun x := ((finRotate (n+2)).symm x.1,x.2-extendedShift n p d ((finRotate (n+2)).symm x.1))
  left_inv x := by simp
  right_inv x := by simp

private theorem extended_first (n p : ℕ) (d : ZMod p) (x : Fin (n+2) × ZMod p) :
    (extendedUnwinding n p d x).1 = finRotate (n+2) x.1 := rfl

private theorem extended_at_lt (n p : ℕ) (d : ZMod p) (x : Fin (n+2) × ZMod p)
    (hx : x.1.val < n+1) :
    extendedUnwinding n p d x = (⟨x.1.val+1,by omega⟩,x.2+d) := by
  apply Prod.ext
  · exact finRotate_of_lt hx
  · change x.2+extendedShift n p d x.1 = x.2+d
    simp [extendedShift,ne_of_lt hx]

private theorem extended_at_last (n p : ℕ) (d : ZMod p) (y : ZMod p) :
    extendedUnwinding n p d (Fin.last (n+1),y) = (0,y-d) := by
  apply Prod.ext
  · exact finRotate_last
  · change y+extendedShift n p d (Fin.last (n+1)) = y-d
    simp [extendedShift,sub_eq_add_neg]

private def embedShort (n p : ℕ) [NeZero n] (x : ZMod n × ZMod p) : Fin (n+2) × ZMod p :=
  (⟨x.1.val,(ZMod.val_lt x.1).trans (by omega)⟩,x.2)

private theorem short_step_lifts (n p : ℕ) [NeZero n] (d : ZMod p) (x : ZMod n × ZMod p) :
    ∃ k : ℕ, ((extendedUnwinding n p d)^k) (embedShort n p x) =
      embedShort n p (unwindingSuccessor n p d x) := by
  have hx := ZMod.val_lt x.1
  change ∃ k : ℕ, ((extendedUnwinding n p d)^k) (embedShort n p x) =
    embedShort n p (x.1+1,x.2+d)
  by_cases hWrap : x.1.val+1 = n
  · have h0 : x.1+1 = 0 := by
      rw [←ZMod.natCast_zmod_val x.1,←Nat.cast_one,←Nat.cast_add,hWrap,ZMod.natCast_self]
    refine ⟨3,?_⟩
    have h1 : extendedUnwinding n p d (embedShort n p x) = (⟨n,by omega⟩,x.2+d) := by
      rw [extended_at_lt _ _ _ _ (by simpa [embedShort] using hx.trans (by omega : n < n+1))]
      congr 1
      exact Fin.ext hWrap
    have h2 : extendedUnwinding n p d (⟨n,by omega⟩,x.2+d) =
        (Fin.last (n+1),x.2+d+d) := extended_at_lt _ _ _ _ (by simp)
    have h3 := extended_at_last n p d (x.2+d+d)
    rw [show (3:ℕ) = 2+1 from rfl,pow_succ,Equiv.Perm.mul_apply,h1,pow_two,Equiv.Perm.mul_apply,h2,h3]
    simp [embedShort,h0]
  · have hlt : x.1.val+1 < n := by omega
    refine ⟨1,?_⟩
    rw [pow_one,extended_at_lt _ _ _ _ (by simpa [embedShort] using hx.trans (by omega : n < n+1))]
    apply Prod.ext
    · apply Fin.ext
      change x.1.val+1 = (x.1+1).val
      have hcast : ((x.1.val+1:ℕ):ZMod n) = x.1+1 := by
        rw [Nat.cast_add,Nat.cast_one,ZMod.natCast_zmod_val]
      rw [←hcast,ZMod.val_natCast,Nat.mod_eq_of_lt hlt]
    · rfl

private theorem short_power_lifts (n p : ℕ) [NeZero n] (d : ZMod p)
    (k : ℕ) (x : ZMod n × ZMod p) :
    ∃ t : ℕ, ((extendedUnwinding n p d)^t) (embedShort n p x) =
      embedShort n p (((unwindingSuccessor n p d)^k) x) := by
  induction k with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    obtain ⟨t,ht⟩ := ih
    obtain ⟨b,hb⟩ := short_step_lifts n p d (((unwindingSuccessor n p d)^k) x)
    exact ⟨b+t,by rw [pow_add,Equiv.Perm.mul_apply,ht,hb,pow_succ',Equiv.Perm.mul_apply]⟩

theorem extended_unwinding_spanning (n p : ℕ) [NeZero n] [NeZero p]
    (hp : p.Prime) (hC : n.Coprime p) (d : ZMod p) (hd : d ≠ 0) :
    HasSpanningCycle (fun x y => extendedUnwinding n p d x = y) := by
  let σ := unwindingSuccessor n p d
  let ρ := extendedUnwinding n p d
  let a := embedShort n p (0,0)
  obtain ⟨L,z,_,hAll,_,hChain⟩ := coprime_unwinding_spanning n p hp hC d hd
  have hShort (x : ZMod n × ZMod p) : ρ.SameCycle a (embedShort n p x) := by
    have h := sameCycle_of_successor_chain σ hChain (List.mem_append_left _ (hAll (0,0)))
      (List.mem_append_left _ (hAll x))
    obtain ⟨k,_,hk⟩ := h.exists_pow_eq'
    obtain ⟨t,ht⟩ := short_power_lifts n p d k (0,0)
    rw [hk] at ht
    rw [←ht,Equiv.Perm.sameCycle_pow_right]
  apply spanning_cycle_of_single_orbit ρ a
  rintro ⟨i,y⟩
  by_cases hi : i.val < n
  · have he : embedShort n p ((i.val:ZMod n),y) = (i,y) := by
      apply Prod.ext
      · exact Fin.ext (ZMod.val_natCast_of_lt hi)
      · rfl
    exact he ▸ hShort ((i.val:ZMod n),y)
  have hN := NeZero.pos n
  let x : ZMod n × ZMod p := (((n-1:ℕ):ZMod n),y-d)
  have h1 : ρ (embedShort n p x) = (⟨n,by omega⟩,y) := by
    have hx : (embedShort n p x).1.val = n-1 := ZMod.val_natCast_of_lt (by omega)
    rw [extended_at_lt _ _ _ _ (by omega)]
    apply Prod.ext
    · exact Fin.ext (by simp only [hx]; omega)
    · change y-d+d = y
      exact sub_add_cancel _ _
  have hMid : ρ.SameCycle a (⟨n,by omega⟩,y) := h1 ▸ (hShort x).apply_right
  by_cases hn : i.val = n
  · exact (show (⟨n,by omega⟩,y) = (i,y) from Prod.ext (Fin.ext hn.symm) rfl) ▸ hMid
  have he : i = Fin.last (n+1) := Fin.ext (by have := i.isLt; simp; omega)
  have h2 : ρ (⟨n,by omega⟩,y-d) = (i,y) := by
    rw [he,extended_at_lt _ _ _ _ (by simp)]
    exact Prod.ext rfl (sub_add_cancel _ _)
  have hPrev : ρ.SameCycle a (⟨n,by omega⟩,y-d) := by
    let w : ZMod n × ZMod p := (((n-1:ℕ):ZMod n),y-d-d)
    have hw : (embedShort n p w).1.val = n-1 := ZMod.val_natCast_of_lt (by omega)
    have ht : ρ (embedShort n p w) = (⟨n,by omega⟩,y-d) := by
      rw [extended_at_lt _ _ _ _ (by omega)]
      exact Prod.ext (Fin.ext (by simp only [hw]; omega)) (sub_add_cancel _ _)
    exact ht ▸ (hShort w).apply_right
  exact h2 ▸ hPrev.apply_right

private def shortenedLabel (n p : ℕ) (d : ZMod p) (x : Fin (n+2) × ZMod p) : ZMod p :=
  if x.1.val = n+1 then x.2-d else x.2

private theorem shortenedLabel_step (n p : ℕ) (d : ZMod p) (x : Fin (n+2) × ZMod p) :
    shortenedLabel n p d (extendedUnwinding n p d x) =
      shortenedLabel n p d x + (if x.1.val < n then d else 0) := by
  obtain ⟨i,y⟩ := x
  have hi := i.isLt
  by_cases h : i.val < n
  · rw [extended_at_lt _ _ _ _ (by simp; omega)]
    simp [shortenedLabel,h,show i.val ≠ n+1 by omega,show i.val ≠ n by omega]
  by_cases hm : i.val = n
  · rw [extended_at_lt _ _ _ _ (by simp; omega)]
    simp [shortenedLabel,h,hm]
  have he : i = Fin.last (n+1) := Fin.ext (by simp; omega)
  subst i
  rw [extended_at_last]
  simp [shortenedLabel]

private theorem shortenedLabel_power (n p : ℕ) (d : ZMod p) (k : ℕ)
    (x : Fin (n+2) × ZMod p) :
    ∃ c ≤ k, shortenedLabel n p d (((extendedUnwinding n p d)^k) x) =
      shortenedLabel n p d x + (c:ZMod p)*d := by
  induction k generalizing x with
  | zero => exact ⟨0,le_rfl,by simp⟩
  | succ k ih =>
    let ρ := extendedUnwinding n p d
    obtain ⟨c,hc,he⟩ := ih (ρ x)
    rw [pow_succ,Equiv.Perm.mul_apply,he,shortenedLabel_step]
    by_cases hx : x.1.val < n
    · exact ⟨c+1,by omega,by rw [if_pos hx,Nat.cast_add,Nat.cast_one,add_mul,one_mul]; abel⟩
    · exact ⟨c,by omega,by simp [hx]⟩

/-- The two inserted clusters do not reduce the distance between
vertices of equal label in the original clusters. -/
theorem extended_same_label_distance (n p : ℕ) [NeZero p] (hp : p.Prime)
    (d : ZMod p) (hd : d ≠ 0) (k : ℕ) (hk : 0 < k) (x : Fin (n+2) × ZMod p)
    (hx : x.1.val < n) (hy : ((((extendedUnwinding n p d)^k) x).1).val < n)
    (he : (((extendedUnwinding n p d)^k) x).2 = x.2) : p ≤ k := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  let ρ := extendedUnwinding n p d
  obtain ⟨c,hc,hcEq⟩ := shortenedLabel_power n p d t (ρ x)
  have hPow : (ρ^(t+1)) x = (ρ^t) (ρ x) := by rw [pow_succ,Equiv.Perm.mul_apply]
  have hEq : (c+1:ℕ) ≤ t+1 ∧ ((c+1:ℕ):ZMod p)*d = 0 := by
    rw [←hPow,shortenedLabel_step,if_pos hx] at hcEq
    have hx' : x.1.val ≠ n+1 := by omega
    have hy' : ((ρ^(t+1)) x).1.val ≠ n+1 := by change ((ρ^(t+1)) x).1.val < n at hy; omega
    change ((ρ^(t+1)) x).2 = x.2 at he
    simp only [shortenedLabel,if_neg hx',if_neg hy',he] at hcEq
    refine ⟨by omega,add_left_cancel (show x.2+(((c+1:ℕ):ZMod p)*d) = x.2+0 by
      calc
        _ = x.2+d+(c:ZMod p)*d := by push_cast; ring
        _ = _ := by simpa only [add_zero] using hcEq.symm)⟩
  have hNat : p ≤ c+1 := unwinding_same_label_distance n p hp d hd (c+1) (by omega) (0,0)
    (by
      rw [unwindingSuccessor_iterate]
      change 0 + ((c+1:ℕ):ZMod p)*d = 0
      rw [zero_add,hEq.2])
  exact hNat.trans hEq.1

/-- The non-coprime branch of Lemma 4.4. The first n clusters are
the original clusters of the shortened cycle. -/
theorem divisible_unwinding_family (n p : ℕ) [NeZero n] [NeZero p] (hp : p.Prime)
    (hp2 : 2 < p) (hDvd : p ∣ n+2) :
    (∀ d : {d : ZMod p // d ≠ 0}, HasSpanningCycle (fun x y => extendedUnwinding n p d.val x = y)) ∧
    (∀ (d : {d : ZMod p // d ≠ 0}) x, (extendedUnwinding n p d.val x).1 = finRotate (n+2) x.1) ∧
    (∀ (d e : {d : ZMod p // d ≠ 0}), d ≠ e → ∀ x,
      extendedUnwinding n p d.val x ≠ extendedUnwinding n p e.val x) ∧
    ∀ (d : {d : ZMod p // d ≠ 0}) k (x : Fin (n+2) × ZMod p), 0 < k →
      x.1.val < n → (((extendedUnwinding n p d.val)^k) x).1.val < n →
      (((extendedUnwinding n p d.val)^k) x).2 = x.2 → p ≤ k := by
  have hc : n.Coprime p := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hp2
      (by simpa using Nat.dvd_sub hDvd h)
  refine ⟨fun d => extended_unwinding_spanning n p hp hc d.val d.prop,fun _ _ => rfl,?_,?_⟩
  · intro d e h x he
    have hh : x.2+extendedShift n p d.val x.1 = x.2+extendedShift n p e.val x.1 := congrArg Prod.snd he
    have hShift := add_left_cancel hh
    apply h
    apply Subtype.ext
    by_cases hx : x.1.val = n+1
    · simpa [extendedShift,hx] using hShift
    · simpa [extendedShift,hx] using hShift
  · intro d k x hk hx hy he
    exact extended_same_label_distance n p hp d.val d.prop k hk x hx hy he

end OverfullWork.DirectedRobustExpansion
