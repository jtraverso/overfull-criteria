module

public import OverfullWork.PrefactorShortCycleInheritance

@[expose] public section


namespace OverfullWork.DirectedPrefactor
open Finset Function
open scoped Classical
variable {V : Type*} [Fintype V] {D : Digraph V} {x : V}

theorem orbit_eq_forward_trace (σ : Equiv.Perm V) (v : V) :
    orbit σ v=(range (minimalPeriod (σ : V → V) v)).image
      (fun i => (σ : V → V)^[i] v) := by
  ext w
  rw [orbit_mem_iff,mem_image]
  constructor
  · intro hw
    obtain ⟨i,_,hi⟩ := hw.exists_pow_eq'
    rw [Equiv.Perm.coe_pow] at hi
    refine ⟨i % minimalPeriod (σ : V → V) v,mem_range.mpr (Nat.mod_lt _ ?_),?_⟩
    · exact minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts v)
    · rw [iterate_mod_minimalPeriod_eq,hi]
  · rintro ⟨i,_,rfl⟩
    rw [←Equiv.Perm.coe_pow,Equiv.Perm.sameCycle_pow_right]

theorem orbit_card_eq_period (σ : Equiv.Perm V) (v : V) :
    (orbit σ v).card=minimalPeriod (σ : V → V) v := by
  rw [orbit_eq_forward_trace,card_image_iff.mpr ?_,card_range]
  intro i hi j hj he
  exact iterate_injOn_Iio_minimalPeriod (mem_range.mp hi) (mem_range.mp hj) he

/-- The origin's orbit strictly grows if the original path is protected
and the final terminus lies outside the original orbit. -/
theorem open_orbit_grows {F₀ F : Prefactor D x} {steps k : ℕ}
    (hReach : Reach (forbiddenEnds k) F₀ steps F)
    (hK : (orbit F₀.successor x).card ≤ k)
    (hNew : terminus F ∉ orbit F₀.successor x) :
    (orbit F₀.successor x).card < (orbit F.successor x).card := by
  let s := (orbit F₀.successor x).card
  have hs : s=minimalPeriod (F₀.successor : V → V) x := orbit_card_eq_period _ _
  have hOpen : ∀ i < s-1,(F₀.successor : V → V)^[i] x ≠ terminus F₀ := by
    intro i hi he
    have hNext : (F₀.successor : V → V)^[i+1] x=(F₀.successor : V → V)^[0] x := by
      rw [iterate_succ_apply',he,iterate_zero_apply]
      exact F₀.successor.apply_symm_apply x
    have heq := iterate_injOn_Iio_minimalPeriod (show i+1 < _ by omega)
      (show 0 < _ by omega) hNext
    omega
  have hPrefix := protected_prefix_survives hReach (s-1) hOpen
    (fun G i hi => mem_union_left _ (mem_image.mpr ⟨i,mem_range.mpr (by omega),rfl⟩))
  have hSub : orbit F₀.successor x ⊆ orbit F.successor x := by
    intro v hv
    rw [orbit_eq_forward_trace] at hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    rw [←hPrefix.1 i (by have := mem_range.mp hi; omega),orbit_mem_iff,
      ←Equiv.Perm.coe_pow,Equiv.Perm.sameCycle_pow_right]
  exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSub,fun he =>
    hNew (he ▸ (orbit_mem_iff F.successor x _).mpr
      (Equiv.Perm.sameCycle_symm_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)))⟩)

end OverfullWork.DirectedPrefactor
