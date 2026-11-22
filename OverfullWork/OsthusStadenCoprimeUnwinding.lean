module

public import OverfullWork.MergeConnectedCycles
public import Mathlib.Data.ZMod.Basic

@[expose] public section


/-! The coprime case of Osthus–Staden Lemma 4.4. The two coordinates
record the cluster and the label within its fibre. -/
namespace OverfullWork.DirectedRobustExpansion
open scoped Classical

def unwindingSuccessor (n p : ℕ) (d : ZMod p) : Equiv.Perm (ZMod n × ZMod p) :=
  Equiv.addRight ((1 : ZMod n),d)

theorem unwindingSuccessor_iterate (n p : ℕ) (d : ZMod p) (k : ℕ)
    (x : ZMod n × ZMod p) :
    ((unwindingSuccessor n p d)^k) x = (x.1+(k:ZMod n),x.2+(k:ZMod p)*d) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih]
    change (x.1+(k:ZMod n)+1,x.2+(k:ZMod p)*d+d) =
      (x.1+((k+1:ℕ):ZMod n),x.2+((k+1:ℕ):ZMod p)*d)
    simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_assoc]

private theorem coprime_unwinding_spanning_unit (n p : ℕ) [NeZero n] [NeZero p]
    (hC : n.Coprime p) (d : (ZMod p)ˣ) :
    HasSpanningCycle (fun x y => unwindingSuccessor n p d.val x = y) := by
  letI : NeZero (n*p) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne p)⟩
  apply spanning_cycle_of_single_orbit (unwindingSuccessor n p d.val) (0,0)
  intro y
  let e := ZMod.chineseRemainder hC
  let a := e.symm (y.1,y.2*↑d⁻¹)
  have h := e.apply_symm_apply (y.1,y.2*↑d⁻¹)
  have he : ((a.val:ZMod n),(a.val:ZMod p)) = (y.1,y.2*↑d⁻¹) := by
    calc
      _ = e (a.val : ZMod (n*p)) := by
        rw [map_natCast]
        rfl
      _ = _ := by rw [ZMod.natCast_zmod_val]; exact h
  have hPow : ((unwindingSuccessor n p d.val)^a.val) (0,0) = y := by
    rw [unwindingSuccessor_iterate]
    simp only [zero_add]
    have h₁ : (a.val:ZMod n) = y.1 := congrArg Prod.fst he
    have h₂ : (a.val:ZMod p) = y.2*↑d⁻¹ := congrArg Prod.snd he
    exact Prod.ext h₁ (by rw [h₂,Units.inv_mul_cancel_right])
  rw [←hPow,Equiv.Perm.sameCycle_pow_right]

private theorem unwinding_isUnit (p : ℕ) [NeZero p] (hp : p.Prime) (d : ZMod p) (hd : d ≠ 0) :
    IsUnit d := by
  have hPos : 0 < d.val := by
    by_contra! h
    exact hd (by rw [←ZMod.natCast_zmod_val d,Nat.eq_zero_of_le_zero h,Nat.cast_zero])
  have hNot : ¬p ∣ d.val := Nat.not_dvd_of_pos_of_lt hPos (ZMod.val_lt d)
  rw [←ZMod.natCast_zmod_val d,ZMod.isUnit_iff_coprime]
  exact (hp.coprime_iff_not_dvd.mpr hNot).symm

theorem coprime_unwinding_spanning (n p : ℕ) [NeZero n] [NeZero p] (hp : p.Prime)
    (hC : n.Coprime p) (d : ZMod p) (hd : d ≠ 0) :
    HasSpanningCycle (fun x y => unwindingSuccessor n p d x = y) := by
  obtain ⟨u,rfl⟩ := unwinding_isUnit p hp d hd
  exact coprime_unwinding_spanning_unit n p hC u

/-- Each step uses a successor-cluster arc. Distinct nonzero increments
give edge-disjoint Hamilton cycles in the complete blow-up. -/
theorem coprime_unwinding_family (n p : ℕ) [NeZero n] [NeZero p] (hp : p.Prime) (hC : n.Coprime p) :
    (∀ d : {d : ZMod p // d ≠ 0}, HasSpanningCycle (fun x y => unwindingSuccessor n p d.val x = y)) ∧
    (∀ (d : {d : ZMod p // d ≠ 0}) x, (unwindingSuccessor n p d.val x).1 = x.1+1) ∧
    ∀ (d e : {d : ZMod p // d ≠ 0}), d ≠ e → ∀ x,
      unwindingSuccessor n p d.val x ≠ unwindingSuccessor n p e.val x := by
  refine ⟨fun d => coprime_unwinding_spanning n p hp hC d.val d.prop,fun _ _ => rfl,?_⟩
  intro d e h x he
  exact h (Subtype.ext (add_left_cancel (congrArg Prod.snd he)))

theorem unwinding_same_label_distance (n p : ℕ) [NeZero p] (hp : p.Prime) (d : ZMod p) (hd : d ≠ 0)
    (k : ℕ) (hk : 0 < k) (x : ZMod n × ZMod p)
    (he : (((unwindingSuccessor n p d)^k) x).2 = x.2) : p ≤ k := by
  rw [unwindingSuccessor_iterate] at he
  have h0 : (k:ZMod p)*d = 0 := add_left_cancel (he.trans (add_zero x.2).symm)
  obtain ⟨u,hu⟩ := unwinding_isUnit p hp d hd
  rw [←hu,Units.mul_left_eq_zero] at h0
  exact Nat.le_of_dvd hk ((ZMod.natCast_eq_zero_iff k p).mp h0)

theorem count_unwinding_increments (p : ℕ) [NeZero p] :
    Fintype.card {d : ZMod p // d ≠ 0} = p-1 := by
  rw [Fintype.card_subtype_compl (fun d : ZMod p => d = 0),ZMod.card]
  simp

end OverfullWork.DirectedRobustExpansion
