module

public import OverfullWork.PrefactorCycleBounds

@[expose] public section


/-! Short closed cycles are inherited through arbitrary admissible
extension sequences that protect both ends of the open path. -/
namespace OverfullWork.DirectedPrefactor
open Finset Function
open scoped Classical
variable {V : Type*} [Fintype V] {D : Digraph V} {x : V}

theorem path_short_or_has_long_backward_trace (F : Prefactor D x) (k : ℕ) :
    (∃ i < k,(F.successor : V → V)^[i] x=terminus F) ∨
      k ≤ minimalPeriod (F.successor.symm : V → V) (terminus F) := by
  let σ := F.successor
  let y := terminus F
  let m := minimalPeriod (σ.symm : V → V) y
  by_cases h : k ≤ m
  · exact Or.inr h
  have hm : 0 < m :=
    minimalPeriod_pos_of_mem_periodicPts (σ.symm.injective.mem_periodicPts y)
  have hBack : (σ⁻¹^m) y=y := by
    rw [Equiv.Perm.coe_pow]
    exact iterate_minimalPeriod
  have hFront : (σ^m) y=y := by
    symm
    apply (Equiv.symm_apply_eq (σ^m)).mp
    change ((σ^m)⁻¹) y=y
    rwa [←inv_pow]
  have hx : σ y=x := σ.apply_symm_apply x
  have hLast : (σ : V → V)^[m-1] x=y := by
    rw [←hx,←iterate_succ_apply, show (m-1).succ=m by omega]
    simpa only [Equiv.Perm.coe_pow] using hFront
  exact Or.inl ⟨m-1,by omega,hLast⟩

theorem short_closed_orbit_inherited_along_reach {B : Prefactor D x → Finset V}
    {F₀ F : Prefactor D x} {steps : ℕ} (hReach : Reach B F₀ steps F) (k : ℕ)
    (hPrefix : ∀ G : Prefactor D x,∀ i < k,(G.successor : V → V)^[i] x ∈ B G)
    (hSuffix : ∀ G : Prefactor D x,∀ i < k,
      (G.successor.symm : V → V)^[i] (terminus G) ∈ B G)
    (v : V) (hOrigin : x ∉ orbit F.successor v) (hShort : (orbit F.successor v).card < k) :
    orbit F.successor v = orbit F₀.successor v := by
  induction hReach with
  | zero => rfl
  | keep _ ih => exact ih hOrigin hShort
  | @step _ G _ z hz ha hAvoid ih =>
    have hEq := short_closed_orbit_inherited G z hz ha k
      (path_short_or_has_long_backward_trace G k)
      (fun i hi he => hAvoid (he ▸ hPrefix G i hi))
      (fun i hi he => hAvoid (he ▸ hSuffix G i hi)) v hOrigin hShort
    exact hEq.trans (ih (hEq ▸ hOrigin) (hEq ▸ hShort))

/-- The two protected segments in the proof of Lo–Patel Theorem 5.3.
For short open paths the traces wrap and their union is a set. -/
noncomputable def forbiddenEnds (k : ℕ) (F : Prefactor D x) : Finset V :=
  (range k).image (fun i => (F.successor : V → V)^[i] x) ∪
    (range k).image (fun i => (F.successor.symm : V → V)^[i] (terminus F))

theorem card_forbiddenEnds_le (k : ℕ) (F : Prefactor D x) :
    (forbiddenEnds k F).card ≤ 2*k := by
  unfold forbiddenEnds
  refine (card_union_le _ _).trans ?_
  simpa only [card_range,two_mul] using
    Nat.add_le_add (card_image_le (s:=range k) (f:=fun i => (F.successor : V → V)^[i] x))
      (card_image_le (s:=range k) (f:=fun i => (F.successor.symm : V → V)^[i] (terminus F)))

theorem short_cycle_inherited {F₀ F : Prefactor D x} {steps k : ℕ}
    (hReach : Reach (forbiddenEnds k) F₀ steps F) (v : V)
    (hOrigin : x ∉ orbit F.successor v) (hShort : (orbit F.successor v).card < k) :
    orbit F.successor v=orbit F₀.successor v :=
  short_closed_orbit_inherited_along_reach hReach k
    (fun _ i hi => mem_union_left _ (mem_image.mpr ⟨i,mem_range.mpr hi,rfl⟩))
    (fun _ i hi => mem_union_right _ (mem_image.mpr ⟨i,mem_range.mpr hi,rfl⟩))
    v hOrigin hShort

end OverfullWork.DirectedPrefactor
