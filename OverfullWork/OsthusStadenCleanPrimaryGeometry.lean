module

public import OverfullWork.OsthusStadenUnwoundPrimarySlices
public import OverfullWork.OsthusStadenCleanWindow

@[expose] public section


/-! The clean intermediate cells for the actual unwind in §5.3–§5.4. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

private theorem sameCycle_project_of_successor {X Y : Type*} [Finite X]
    (F : Equiv.Perm X) (S : Equiv.Perm Y) (project : X → Y)
    (hProj : ∀ x, project (F x) = S (project x)) {x y : X} (h : F.SameCycle x y) :
    S.SameCycle (project x) (project y) := by
  obtain ⟨k,rfl⟩ := h.exists_nat_pow_eq
  have hPow (a : ℕ) : project ((F^a) x) = (S^a) (project x) := by
    induction a with
    | zero => simp
    | succ a ih => simpa only [pow_succ',Equiv.Perm.mul_apply,hProj,ih]
  rw [hPow]
  exact (Equiv.Perm.SameCycle.refl S _).pow_right

/-- The second unwind preserves the original cycle classes, and its
projection onto the intermediate factor recovers those classes there. -/
theorem UnwoundPrimarySlices.first_sameCycle
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero s] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ η d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) s p m τ τ τ}
    (A : UnwoundPrimarySlices G thin E g σ τ η d R)
    (hp : 1 < p) (t : Fin r) (a : UnwindingLabel s) (x y : I × ZMod s) :
    (A.first t a).SameCycle x y ↔ (σ t).SameCycle x.1 y.1 := by
  constructor
  · exact sameCycle_project_of_successor (A.first t a) (σ t) Prod.fst (A.first_proj t a)
  · intro h
    letI : Fact (1 < p) := ⟨hp⟩
    let b : UnwindingLabel p := ⟨1,by
      intro he
      have h₁ := congrArg ZMod.val he
      rw [ZMod.val_one, ZMod.val_zero] at h₁
      omega⟩
    have hLift : (A.factor (t,a,b)).SameCycle (x,0) (y,0) :=
      (A.cycles t a b (x,0) (y,0)).mpr h
    exact sameCycle_project_of_successor (A.factor (t,a,b)) (A.first t a) Prod.fst
      (A.factor_proj t a b) hLift

/-- Join the last-turn windows of all intermediate cycles. Every
primary cluster contributes exactly one clean intermediate label. -/
theorem exists_clean_first_factor_labels {I W : Type*} [Fintype I]
    (σ : Equiv.Perm I) (F : Equiv.Perm (I × W)) [Nonempty W]
    (C : FactorCycleCoordinates F) (hFixed : ∀ i, σ i ≠ i)
    (hProj : ∀ x, (F x).1 = σ x.1)
    (hOrbit : ∀ x y, F.SameCycle x y ↔ σ.SameCycle x.1 y.1) :
    ∃ clean : I → W, ∀ o (i : Fin (C.length o)),
      C.length o-2 ≤ i.val → (C.order ⟨o,i⟩).2 = clean (C.order ⟨o,i⟩).1 := by
  let B := factorCycleCoordinates σ hFixed
  have hSurj : Function.Surjective (Prod.fst : I × W → I) := fun i => ⟨(i,Classical.choice inferInstance),rfl⟩
  choose oBase window hWindow hLast using fun o =>
    exists_clean_cycle_window σ F Prod.fst B C hProj hSurj hOrbit o
  let inClean (x : I × W) : Prop := window (C.order.symm x).1 (C.order.symm x).2
  have hMem (o : C.Orb) (v : Fin (C.length o)) :
      inClean (C.order ⟨o,v⟩) ↔ window o v := by
    change (fun z : Σ j, Fin (C.length j) => window z.1 z.2) (C.order.symm (C.order ⟨o,v⟩)) ↔ _
    rw [C.order.symm_apply_apply]
  have hBase (o : C.Orb) (v : Fin (C.length o)) :
      (B.order.symm (C.order ⟨o,v⟩).1).1 = oBase o := by
    letI : NeZero (B.length (oBase o)) := ⟨by have := B.length_ge_two (oBase o); omega⟩
    obtain ⟨u,hu,_⟩ := hWindow o (0 : Fin (B.length (oBase o)))
    have h : σ.SameCycle (C.order ⟨o,v⟩).1 (B.order ⟨oBase o,0⟩) := by
      rw [←hu.2,←hOrbit,C.same_orbit]
    let z := B.order.symm (C.order ⟨o,v⟩).1
    have hz : B.order ⟨z.1,z.2⟩ = (C.order ⟨o,v⟩).1 :=
      B.order.apply_symm_apply _
    rw [←hz,B.same_orbit] at h
    exact h
  have hLocalUnique (o : C.Orb) (i : I) (hi : (B.order.symm i).1 = oBase o) :
      ∃! u : Fin (C.length o), window o u ∧ (C.order ⟨o,u⟩).1 = i := by
    let z := B.order.symm i
    have hz : B.order z = i := B.order.apply_symm_apply i
    change z.1 = oBase o at hi
    cases hTag : z with
    | mk b j =>
      rw [hTag] at hi hz
      change b = oBase o at hi
      subst b
      simpa only [hz] using hWindow o j
  have hChoice (i : I) : ∃! w : W, inClean (i,w) := by
    let x := (i,Classical.choice (inferInstance : Nonempty W))
    obtain ⟨⟨o,v⟩,hv⟩ := C.order.surjective x
    have hi : (C.order ⟨o,v⟩).1 = i := congrArg Prod.fst hv
    obtain ⟨u,hu,hUnique⟩ := hLocalUnique o i (hi ▸ hBase o v)
    let w := (C.order ⟨o,u⟩).2
    have hw : C.order ⟨o,u⟩ = (i,w) := Prod.ext hu.2 rfl
    have hwClean : inClean (i,w) := by
      rw [←hw]
      exact (hMem o u).mpr hu.1
    refine ⟨w,hwClean,?_⟩
    intro w' hw'
    obtain ⟨⟨o',v'⟩,hv'⟩ := C.order.surjective (i,w')
    have hSame : F.SameCycle (C.order ⟨o',v'⟩) (C.order ⟨o,u⟩) := by
      rw [hv',hw,hOrbit]
    have eo := (C.same_orbit o' o v' u).mp hSame
    subst o'
    have hvClean : inClean (C.order ⟨o,v'⟩) := by rwa [hv']
    have hvEq : v' = u := hUnique v' ⟨(hMem o v').mp hvClean,congrArg Prod.fst hv'⟩
    subst v'
    exact congrArg Prod.snd (hv'.symm.trans hw)
  simp only [ExistsUnique] at hChoice
  choose clean hClean hUnique using hChoice
  exact ⟨clean,fun o v hv => hUnique _ _ ((hMem o v).mpr (hLast o v hv))⟩

end OverfullWork.DirectedRobustExpansion
