module

public import OverfullWork.RobustHamiltonDecomposition
public import OverfullWork.PrefactorOpenOrbit

@[expose] public section


/-! The final connectivity argument in Osthus–Staden §5.11. Once each
cluster group is contained in one orbit, bridges between groups suffice. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset Function DirectedPrefactor
open scoped Classical
variable {V I : Type*} [Fintype V]

theorem spanning_cycle_of_single_orbit (σ : Equiv.Perm V) (v : V)
    (hOrbit : ∀ w,σ.SameCycle v w) : HasSpanningCycle (fun x y => σ x = y) := by
  let f : V → V := σ
  let k := minimalPeriod f v
  have hk : 0 < k := minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts v)
  let T := List.ofFn (fun i : Fin k => f^[i.val] v)
  have hND : T.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j he
    exact Fin.ext (iterate_injOn_Iio_minimalPeriod i.isLt j.isLt he)
  have hAll (w : V) : w ∈ T := by
    have hw := (orbit_mem_iff σ v w).mpr (hOrbit w)
    rw [orbit_eq_forward_trace] at hw
    obtain ⟨i,hi,he⟩ := mem_image.mp hw
    exact List.mem_ofFn.mpr ⟨⟨i,mem_range.mp hi⟩,he⟩
  have hLen : T.length = k := List.length_ofFn
  have hAt (i : ℕ) (hi : i < T.length) : T[i] = f^[i] v := by simp [T]
  have hHead : T.head? = some v := by
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_eq_getElem (by omega : 0 < T.length),hAt]
    rfl
  refine ⟨T,v,hND,hAll,hHead,List.isChain_iff_getElem.mpr ?_⟩
  intro i hi
  have hi' : i < T.length := by simp at hi; omega
  rw [List.getElem_append_left hi',hAt]
  change f (f^[i] v) = _
  rw [←iterate_succ_apply' f i v]
  by_cases hs : i+1 < T.length
  · rw [List.getElem_append_left hs,hAt]
  · have he : i+1 = T.length := by omega
    change f^[i+1] v = _
    rw [List.getElem_append_right (by omega),List.getElem_singleton,he,hLen]
    exact isPeriodicPt_minimalPeriod f v

/-- Merge the orbits of a permutation from a connected set of group
bridges. The relation can record preserved segments or exceptional
vertices that witness the bridges. -/
theorem spanning_cycle_of_connected_groups (σ : Equiv.Perm V) (f : V → I) (v : V)
    (r : I → I → Prop) (hOnto : Surjective f)
    (hGroup : ∀ x y, f x = f y → σ.SameCycle x y)
    (hBridge : ∀ i j, r i j → ∃ x y, f x = i ∧ f y = j ∧ σ.SameCycle x y)
    (hConnected : ∀ i, Relation.EqvGen r (f v) i) :
    HasSpanningCycle (fun x y => σ x = y) := by
  choose rep hrep using hOnto
  have hClose (i j : I) (h : Relation.EqvGen r i j) : σ.SameCycle (rep i) (rep j) := by
    induction h with
    | rel i j h =>
      obtain ⟨x,y,hx,hy,hxy⟩ := hBridge i j h
      exact (hGroup _ _ ((hrep i).trans hx.symm)).trans
        (hxy.trans (hGroup _ _ (hy.trans (hrep j).symm)))
    | refl i => exact Equiv.Perm.SameCycle.refl _ _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂
  apply spanning_cycle_of_single_orbit σ v
  intro w
  exact (hGroup _ _ (hrep (f v)).symm).trans
    ((hClose _ _ (hConnected (f w))).trans (hGroup _ _ (hrep (f w))))

end OverfullWork.DirectedRobustExpansion
