module

public import OverfullWork.OsthusStadenCleanPrimaryGeometry
public import OverfullWork.OsthusStadenRedOrientationSchedule

@[expose] public section


/-! Select the directional red cells on the already constructed layers. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

/-- Clean labels and the red labels of (21) on an actual pair of unwinds.
The true direction receives red edges and the false direction sends them. -/
structure PrimaryRedSelection {I : Type*} {r s p : ℕ} [NeZero (2*s)]
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    (C : ∀ t a, FactorCycleCoordinates (F t a)) where
  clean : Fin r → UnwindingLabel (2*s) → I → ZMod (2*s)
  clean_last : ∀ t a o (k : Fin ((C t a).length o)), (C t a).length o-2 ≤ k.val →
    ((C t a).order ⟨o,k⟩).2 = clean t a ((C t a).order ⟨o,k⟩).1
  select : Bool → RefinedFactorIndex r (2*s) p → I → Finset (Fin (2*s))
  size : ∀ q j i, (select q j i).card = s-1
  disjoint : ∀ j i, Disjoint (select true j i) (select false j i)
  avoids_clean : ∀ q j i z, z ∈ select q j i →
    ZMod.finEquiv (2*s) z ≠ clean j.1 j.2.1 i
  in_half : ∀ q j i z, z ∈ select q j i →
    if q = usesFirstRedHalf j then z.val < s else s ≤ z.val
  reverse : ∀ q j i, select q (reverseLayerOrientation j) i = select (!q) j i

/-- Complete the choice of clean cells and both red directions at once,
using one pair of directional sets for each intermediate factor. -/
theorem exists_primary_red_selection
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero (2*s)] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ η d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    (A : UnwoundPrimarySlices G thin E g σ τ η d R)
    (hp : 1 < p) (hpOdd : Odd p) (hFixed : ∀ t i, σ t i ≠ i) :
    Nonempty (PrimaryRedSelection (p := p) A.coordinates) := by
  choose clean hLast using fun t a => exists_clean_first_factor_labels
    (σ t) (A.first t a) (A.coordinates t a) (hFixed t) (A.first_proj t a)
    (A.first_sameCycle hp t a)
  choose L U hL hU hLU hGoodL hGoodU using fun t a i =>
    exists_directional_red_labels s ((ZMod.finEquiv (2*s)).symm (clean t a i))
  let selected (q : Bool) (j : RefinedFactorIndex r (2*s) p) (i : I) :=
    if q = usesFirstRedHalf j then L j.1 j.2.1 i else U j.1 j.2.1 i
  refine ⟨⟨clean,hLast,selected,?_,?_,?_,?_,?_⟩⟩
  · intro q j i
    dsimp only [selected]
    split_ifs
    · exact hL _ _ _
    · exact hU _ _ _
  · intro j i
    cases h : usesFirstRedHalf j
    · simpa only [selected,h,Bool.true_eq_false,Bool.false_eq_true,if_false,if_true] using
        (hLU j.1 j.2.1 i).symm
    · simpa only [selected,h,Bool.false_eq_true,if_false,if_true] using hLU j.1 j.2.1 i
  · intro q j i z hz he
    have he' : z = (ZMod.finEquiv (2*s)).symm (clean j.1 j.2.1 i) := by
      rw [←he,(ZMod.finEquiv (2*s)).symm_apply_apply]
    dsimp only [selected] at hz
    split_ifs at hz
    · exact (hGoodL _ _ _ _ hz).2 he'
    · exact (hGoodU _ _ _ _ hz).2 he'
  · intro q j i z hz
    dsimp only [selected] at hz
    split_ifs at hz ⊢ with h
    · exact (hGoodL _ _ _ _ hz).1
    · exact (hGoodU _ _ _ _ hz).1
  · intro q j i
    change (if q = usesFirstRedHalf (reverseLayerOrientation j) then L j.1 j.2.1 i else U j.1 j.2.1 i) =
      (if (!q) = usesFirstRedHalf j then L j.1 j.2.1 i else U j.1 j.2.1 i)
    rw [usesFirstRedHalf_reverse hpOdd]
    cases q <;> cases h : usesFirstRedHalf j <;> rfl

/-- Attach the red phase of an original factor to an intermediate
label. This is the selected p-cell before choosing its physical half. -/
def redPLabel {I : Type*} {s p : ℕ} [NeZero (2*s)] (t : ℕ) (i : I)
    (j : Fin (2*s)) : RefinedVertex I (2*s) p :=
  ((i,ZMod.finEquiv (2*s) j),(redPhase p t).1)

def PrimaryRedSelection.selectedPCell {I : Type*} {r s p : ℕ} [NeZero (2*s)]
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)} (D : PrimaryRedSelection (p := p) C)
    (q : Bool) (j : RefinedFactorIndex r (2*s) p) (x : RefinedVertex I (2*s) p) : Prop :=
  ∃ i z, z ∈ D.select q j i ∧ x = redPLabel j.1.val i z

theorem PrimaryRedSelection.pCell_unique_direction {I : Type*} {r s p : ℕ} [NeZero (2*s)]
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)} (D : PrimaryRedSelection (p := p) C)
    (j : RefinedFactorIndex r (2*s) p) (x : RefinedVertex I (2*s) p) :
    ¬ (D.selectedPCell true j x ∧ D.selectedPCell false j x) := by
  rintro ⟨⟨i,z,hz,hx⟩,k,w,hw,hy⟩
  have he := hx.symm.trans hy
  have hik : i = k := congrArg (fun a => a.1.1) he
  have hzw : z = w := (ZMod.finEquiv (2*s)).injective (congrArg (fun a => a.1.2) he)
  subst k
  subst w
  exact disjoint_left.mp (D.disjoint j i) hz hw

/-- The red rule gives Red5 on the physical layer's reduced cycle,
for either choice of direction at either endpoint. -/
theorem PrimaryRedSelection.distance
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero (2*s)] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ η d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    {A : UnwoundPrimarySlices G thin E g σ τ η d R}
    (D : PrimaryRedSelection (p := p) A.coordinates) (hp : 1 < p)
    {j : RefinedFactorIndex r (2*s) p} {x y : RefinedVertex I (2*s) p} {q q' : Bool}
    (hx : D.selectedPCell q j x) (hy : D.selectedPCell q' j y)
    {k : ℕ} (hk : 0 < k) (hPath : ((A.factor j)^k) x = y) : p ≤ k := by
  obtain ⟨i,z,hz,hxz⟩ := hx
  obtain ⟨i',z',hz',hyz⟩ := hy
  have hXRed : x.1.2 ≠ D.clean j.1 j.2.1 x.1.1 := by
    rw [hxz]
    exact D.avoids_clean _ _ _ _ hz
  have hYRed : y.1.2 ≠ D.clean j.1 j.2.1 y.1.1 := by
    rw [hyz]
    exact D.avoids_clean _ _ _ _ hz'
  have hXp : x.2 = (redPhase p j.1.val).1 := congrArg Prod.snd hxz
  have hYp : y.2 = (redPhase p j.1.val).1 := congrArg Prod.snd hyz
  rcases j with ⟨t,a,b⟩
  let C := A.coordinates t a
  obtain ⟨⟨o,u⟩,hu⟩ := C.order.surjective x.1
  obtain ⟨⟨o',v⟩,hv⟩ := C.order.surjective y.1
  have hSame : (A.factor (t,a,b)).SameCycle x y := by
    rw [←hPath]
    exact (Equiv.Perm.SameCycle.refl _ _).pow_right
  have hOrig := (A.cycles t a b x y).mp hSame
  have hFirst := (A.first_sameCycle hp t a x.1 y.1).mpr hOrig
  have ho : o = o' := (C.same_orbit o o' u v).mp (by rwa [hu,hv])
  subst o'
  have hU : u.val < C.length o-2 := by
    by_contra! h
    exact hXRed (by rw [←hu]; exact D.clean_last t a o u h)
  have hV : v.val < C.length o-2 := by
    by_contra! h
    exact hYRed (by rw [←hv]; exact D.clean_last t a o v h)
  exact A.distance t a b o (u,x.2) (v,y.2) k hk hU hV (hXp.trans hYp.symm)
    (by
      change ((A.factor (t,a,b))^k) (C.order ⟨o,u⟩,x.2) = (C.order ⟨o,v⟩,y.2)
      simpa only [hu,hv,Prod.eta] using hPath)

end OverfullWork.DirectedRobustExpansion
