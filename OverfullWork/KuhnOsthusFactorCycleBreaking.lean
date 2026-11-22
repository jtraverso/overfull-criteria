module

public import OverfullWork.FactorCycleCoordinates

@[expose] public section


/-! Break all cycles in a style class of a leftover 1-factor.
A class is represented by the sources of its retained arcs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*}

def factorArcsOn (σ : Equiv.Perm V) (S : Finset V) : Digraph V :=
  ⟨fun x y => x ∈ S ∧ σ x = y⟩

def NoDirectedCycle (D : Digraph V) : Prop :=
  ∀ x, ¬ Relation.TransGen D.Adj x x

private theorem factor_path_iterate (σ : Equiv.Perm V) (S : Finset V) {x y : V}
    (h : Relation.TransGen (factorArcsOn σ S).Adj x y) :
    ∃ k : ℕ, 0 < k ∧ (σ^k) x = y ∧ ∀ j < k, (σ^j) x ∈ S := by
  induction h with
  | single hy =>
    exact ⟨1,by decide,by simpa only [pow_one] using hy.2,fun j hj => by
      have hj0 : j = 0 := by omega
      simpa only [hj0,pow_zero,Equiv.Perm.one_apply] using hy.1⟩
  | tail hxy hyz ih =>
    obtain ⟨k,hk,he,hAll⟩ := ih
    refine ⟨k+1,by omega,?_,?_⟩
    · rw [pow_succ',Equiv.Perm.mul_apply,he]
      exact hyz.2
    · intro j hj
      by_cases heq : j = k
      · rw [heq,he]
        exact hyz.1
      · exact hAll j (by omega)

variable [Fintype V]

theorem factor_cycle_requires_full_orbit (σ : Equiv.Perm V) (S : Finset V) (x : V)
    (h : Relation.TransGen (factorArcsOn σ S).Adj x x) :
    ∀ y, σ.SameCycle x y → y ∈ S := by
  obtain ⟨k,hk,hEnd,hSteps⟩ := factor_path_iterate σ S h
  intro y horb
  obtain ⟨j,_,hj⟩ := horb.exists_pow_eq'
  have hPeriodic := show IsPeriodicPt (σ : V → V) k x from by
    change (σ : V → V)^[k] x = x
    rwa [←Equiv.Perm.coe_pow]
  have hMod := hPeriodic.iterate_mod_apply j
  simp only [←Equiv.Perm.coe_pow] at hMod
  exact (hMod.trans hj) ▸ hSteps (j%k) (Nat.mod_lt _ hk)

/-- The two source sets partition the class. The first selects exactly
one source from any orbit entirely in the class, and the second
contains no cycle. The first itself contains no cycle in a loopless factor. -/
theorem split_factor_style_class (σ : Equiv.Perm V) (S : Finset V)
    (hFixed : ∀ x, σ x ≠ x) :
    ∃ A B : Finset V, A ∪ B = S ∧ Disjoint A B ∧
      NoDirectedCycle (factorArcsOn σ A) ∧ NoDirectedCycle (factorArcsOn σ B) ∧
      (∀ x y, x ∈ A → y ∈ A → σ.SameCycle x y → x = y) ∧
      (∀ x ∈ A, ∀ y, σ.SameCycle x y → y ∈ S) ∧
      ∀ x, (∀ y, σ.SameCycle x y → y ∈ S) → ∃ y ∈ A, σ.SameCycle x y := by
  let Q := Equiv.Perm.SameCycle.setoid σ
  let tag : V → Quotient Q := Quotient.mk Q
  let A := S.filter (fun x => x = (tag x).out ∧ ∀ y, σ.SameCycle x y → y ∈ S)
  let B := S \ A
  have hOne (x y : V) (hx : x ∈ A) (hy : y ∈ A) (horb : σ.SameCycle x y) : x = y := by
    have he : tag x = tag y := Quotient.sound horb
    exact (mem_filter.mp hx).2.1.trans ((congrArg Quotient.out he).trans (mem_filter.mp hy).2.1.symm)
  have hDis : Disjoint A B := by
    rw [disjoint_left]
    exact fun _ ha hb => (mem_sdiff.mp hb).2 ha
  refine ⟨A,B,union_sdiff_of_subset (filter_subset _ _),hDis,?_,?_,hOne,fun _ hx => (mem_filter.mp hx).2.2,?_⟩
  · intro x h
    have hOrb := factor_cycle_requires_full_orbit σ A x h
    have he := hOne x (σ x) (hOrb x (Equiv.Perm.SameCycle.refl σ x))
      (hOrb (σ x) (Equiv.Perm.SameCycle.refl σ x).apply_right)
      (Equiv.Perm.SameCycle.refl σ x).apply_right
    exact hFixed x he.symm
  · intro x h
    let y := (tag x).out
    have hy : σ.SameCycle x y := (Quotient.exact (Quotient.out_eq (tag x))).symm
    have hOrbit := factor_cycle_requires_full_orbit σ B x h
    have hb := hOrbit y hy
    have he : tag y = tag x := Quotient.out_eq (tag x)
    exact (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨(mem_sdiff.mp hb).1,by rw [he],
      fun z hz => (mem_sdiff.mp (hOrbit z (hy.trans hz))).1⟩)
  · intro x hx
    let y := (tag x).out
    have hy : σ.SameCycle x y := (Quotient.exact (Quotient.out_eq (tag x))).symm
    have he : tag y = tag x := Quotient.out_eq (tag x)
    exact ⟨y,mem_filter.mpr ⟨hx y hy,by rw [he],fun z hz => hx z (hy.trans hz)⟩,hy⟩

end OverfullWork.DirectedRobustExpansion
