module

public import OverfullWork.FactorCycleCoordinates
public import OverfullWork.OsthusStadenRedClusters

@[expose] public section


/-! The last full turn of an intermediate cycle meets each primary cluster
above its original cycle exactly once, as in Osthus–Staden §5.3. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical

private theorem finRotate_before_end {n : ℕ} [NeZero n] (i : Fin n) (h : i.val+1 < n) :
    finRotate n i = ⟨i.val+1,h⟩ := by
  apply Fin.ext
  rw [finRotate_apply,Fin.val_add,show (1 : Fin n).val = 1%n from rfl,
    Nat.add_mod_mod,Nat.mod_eq_of_lt h]

/-- A label that advances one step in its base cycle at every step of a
lifted cycle takes each base position exactly once in the last full turn. -/
theorem clean_window_unique {k n : ℕ} [NeZero k] (hkn : k ≤ n)
    (label : Fin n → Fin k)
    (hStep : ∀ i, label (finRotate n i) = finRotate k (label i)) :
    ∀ u : Fin k, ∃! i : Fin n, n-k ≤ i.val ∧ label i = u := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  letI : NeZero n := ⟨by omega⟩
  let start : Fin n := ⟨n-k,by omega⟩
  let last (i : Fin k) : Fin n := ⟨n-k+i.val,by have := i.isLt; omega⟩
  have hLast (i : Fin k) : label (last i) = label start + i := by
    obtain ⟨a,ha⟩ := i
    induction a with
    | zero =>
      have he : (⟨0,ha⟩ : Fin k) = 0 := by
        apply Fin.ext
        exact (Nat.zero_mod k).symm
      rw [he,add_zero]
      congr 1
    | succ a ih =>
      let i : Fin k := ⟨a,by omega⟩
      have hnext : finRotate n (last i) = last ⟨a+1,ha⟩ := by
        rw [finRotate_before_end _ (by simp only [last,i]; omega)]
        rfl
      have hBase : finRotate k i = ⟨a+1,ha⟩ :=
        finRotate_before_end i ha
      rw [← hnext,hStep,ih i.isLt,finRotate_apply,←hBase,finRotate_apply,add_assoc]
  intro u
  let i : Fin k := u-label start
  refine ⟨last i,⟨by change n-k ≤ n-k+i.val; omega,?_⟩,?_⟩
  · rw [hLast]
    simp [i,add_comm]
  · intro j hj
    let i' : Fin k := ⟨j.val-(n-k),by have := j.isLt; omega⟩
    have he : last i' = j := by
      apply Fin.ext
      change n-k+(j.val-(n-k)) = j.val
      exact Nat.add_sub_of_le hj.1
    have hLabel : label start + i' = label start + i := by
      rw [←hLast,he,hj.2]
      simp [i,add_comm]
    rw [←he,add_left_cancel hLabel]

/-- Recover the base-cycle labels of a lifted orbit directly from two
sets of cycle coordinates and the projection of successors. -/
theorem exists_projected_cycle_labels {U W : Type*}
    (σ : Equiv.Perm U) (F : Equiv.Perm W) (project : W → U)
    (B : FactorCycleCoordinates σ) (C : FactorCycleCoordinates F)
    (hProj : ∀ w, project (F w) = σ (project w)) (j : C.Orb) :
    ∃ b : B.Orb, ∃ label : Fin (C.length j) → Fin (B.length b),
      (∀ i, project (C.order ⟨j,i⟩) = B.order ⟨b,label i⟩) ∧
      ∀ i, label (finRotate (C.length j) i) = finRotate (B.length b) (label i) := by
  letI : NeZero (C.length j) := ⟨by have := C.length_ge_two j; omega⟩
  obtain ⟨⟨b,c⟩,hStart⟩ := B.order.surjective (project (C.order ⟨j,0⟩))
  letI : NeZero (B.length b) := ⟨by have := B.length_ge_two b; omega⟩
  let label (i : Fin (C.length j)) : Fin (B.length b) := c + Fin.ofNat _ i.val
  have hMap (i : Fin (C.length j)) : project (C.order ⟨j,i⟩) = B.order ⟨b,label i⟩ := by
    obtain ⟨a,ha⟩ := i
    induction a with
    | zero =>
      have he : (⟨0,ha⟩ : Fin (C.length j)) = 0 := by
        apply Fin.ext
        exact (Nat.zero_mod _).symm
      have hz : label ⟨0,ha⟩ = c := by
        simp [label,Fin.ofNat]
      rw [he,←hStart]
      congr 2
      simpa only [he] using hz.symm
    | succ a ih =>
      let i : Fin (C.length j) := ⟨a,by omega⟩
      have hRot : finRotate (C.length j) i = ⟨a+1,ha⟩ := finRotate_before_end i ha
      have hLabel : label ⟨a+1,ha⟩ = finRotate (B.length b) (label i) := by
        rw [finRotate_apply]
        change c + Fin.ofNat _ (a+1) = c + Fin.ofNat _ a + 1
        rw [add_assoc]
        congr 1
        apply Fin.ext
        change (a+1) % (B.length b) =
          (a % (B.length b) + 1 % (B.length b)) % (B.length b)
        rw [Nat.add_mod_mod,Nat.mod_add_mod]
      rw [← hRot,← C.successor,hProj,ih i.isLt,B.successor,hRot,hLabel]
  refine ⟨b,label,hMap,?_⟩
  intro i
  have he : B.order ⟨b,label (finRotate (C.length j) i)⟩ =
      B.order ⟨b,finRotate (B.length b) (label i)⟩ := by
    rw [←hMap,←C.successor,hProj,hMap,B.successor]
  exact eq_of_heq (Sigma.mk.inj_iff.mp (B.order.injective he)).2

/-- Construct the clean intermediate cells. The orbit projection
guarantees that every primary cluster over the base cycle appears
exactly once among the clean cells, and that the last two are clean. -/
theorem exists_clean_cycle_window {U W : Type*}
    (σ : Equiv.Perm U) (F : Equiv.Perm W) (project : W → U)
    (B : FactorCycleCoordinates σ) (C : FactorCycleCoordinates F)
    (hProj : ∀ w, project (F w) = σ (project w))
    (hSurj : Function.Surjective project)
    (hOrbit : ∀ x y, F.SameCycle x y ↔ σ.SameCycle (project x) (project y))
    (j : C.Orb) :
    ∃ b : B.Orb, ∃ Clean : Fin (C.length j) → Prop,
      (∀ u : Fin (B.length b), ∃! i : Fin (C.length j),
        Clean i ∧ project (C.order ⟨j,i⟩) = B.order ⟨b,u⟩) ∧
      ∀ i : Fin (C.length j), C.length j-2 ≤ i.val → Clean i := by
  obtain ⟨b,label,hLabel,hStep⟩ := exists_projected_cycle_labels σ F project B C hProj j
  letI : NeZero (C.length j) := ⟨by have := C.length_ge_two j; omega⟩
  letI : NeZero (B.length b) := ⟨by have := B.length_ge_two b; omega⟩
  have hLabelSurj : Function.Surjective label := by
    intro u
    obtain ⟨w,hw⟩ := hSurj (B.order ⟨b,u⟩)
    obtain ⟨⟨j',i⟩,rfl⟩ := C.order.surjective w
    have h : F.SameCycle (C.order ⟨j,0⟩) (C.order ⟨j',i⟩) := by
      rw [hOrbit,hLabel,hw,B.same_orbit]
    have hj := (C.same_orbit j j' _ _).mp h
    subst j'
    exact ⟨i,eq_of_heq (Sigma.mk.inj_iff.mp (B.order.injective ((hLabel i).symm.trans hw))).2⟩
  have hLength := Fintype.card_le_of_surjective _ hLabelSurj
  simp only [Fintype.card_fin] at hLength
  refine ⟨b,fun i => C.length j-B.length b ≤ i.val,?_,?_⟩
  · intro u
    have he (i : Fin (C.length j)) :
        project (C.order ⟨j,i⟩) = B.order ⟨b,u⟩ ↔ label i = u := by
      rw [hLabel,B.order.injective.eq_iff]
      exact ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.mp h).2,fun h => by rw [h]⟩
    simp only [he]
    exact clean_window_unique hLength label hStep u
  · intro i hi
    have := B.length_ge_two b
    omega

end OverfullWork.DirectedRobustExpansion
