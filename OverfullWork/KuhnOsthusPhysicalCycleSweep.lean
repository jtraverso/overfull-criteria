module

public import OverfullWork.KuhnOsthusResidueHalfSplice
public import OverfullWork.KuhnOsthusCycleParityAssembly

@[expose] public section


/-! Read the switch schedule of Lemma 10.2 from the physical Claim 1
paths and the ordered rows of the constructed auxiliary factor. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*}

theorem OrderedClusterPaths.sameCycle_from_start {G : Digraph V}
    {A : ℕ → Finset V} {J : Type*} {n : ℕ} (P : OrderedClusterPaths G A J 0 n)
    (τ : Equiv.Perm V) (hP : ∀ {x y}, P.unionPaths.Adj x y → τ x = y)
    (j : J) (k : ℕ) (hk : k ≤ n) :
    τ.SameCycle (P.vertex 0 j) (P.vertex k j) := by
  induction k with
  | zero => exact Equiv.Perm.SameCycle.refl _ _
  | succ k ih =>
    have h := ih (by omega)
    have he : τ (P.vertex k j) = P.vertex (k+1) j :=
      hP (Digraph.iSup_adj.mpr ⟨j,k,Nat.zero_le k,by omega,rfl,rfl⟩)
    exact he ▸ h.apply_right

/-- Only consecutive labels in the path order are used. The switch
between the last and first labels and the repair column are unused. -/
noncomputable def CycleAbsorberResidualFactor.sweepData {G H D : Digraph V}
    {A B : ℕ → Finset V} {m n b c r t : ℕ} {C : CycleAbsorberClaimOne G A m n}
    {E : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c)}
    (R : CycleAbsorberResidualFactor C B E D r) (hm : 0 < m) (hn : 8 ≤ n)
    (F : Fin t → Equiv.Perm V) (i j : Fin t)
    (hP : ∀ {x y}, C.paths.unionPaths.Adj x y → F i x = y)
    (hCover : ∀ z, ∃ a, (F i).SameCycle (C.paths.vertex 0 a) z)
    (hAux : F j = R.permutation) : CycleAbsorberSweepData (Fin (2*m+1)) F i j := by
  let label (p : ℕ) : Fin (2*m) := ⟨p % (2*m), Nat.mod_lt _ (by omega)⟩
  let col (p : ℕ) : Fin (2*m+1) := ⟨p % (2*m+1), Nat.mod_lt _ (by omega)⟩
  have hLabel (p : ℕ) (hp : p < 2*m) : (label p).val = p := Nat.mod_eq_of_lt hp
  have hCol (p : ℕ) (hp : p < 2*m+1) : (col p).val = p := Nat.mod_eq_of_lt hp
  have hSource (p : ℕ) (hp : p < 2*m-1) :
      (F i).SameCycle (C.paths.vertex 0 (label p)) (R.rows.mark (false,col p)) ∧
      (F i).SameCycle (C.paths.vertex 0 (label (p+1))) (R.rows.mark (true,col p)) ∧
      F i (R.rows.mark (false,col p)) = F j (R.rows.mark (true,col p)) ∧
      F i (R.rows.mark (true,col p)) = F j (R.rows.mark (false,col p)) := by
    obtain ⟨⟨k,l⟩,hk⟩ := (cycleAbsorberSwitchSlot m).surjective (label p)
    have hVal : 2*k.val+l.val = p := (cycleAbsorberSwitchSlot_val _ _).symm.trans
      ((congrArg Fin.val hk).trans (hLabel _ (by omega)))
    have hColEq : col p = cycleAbsorberColumn k l := by
      apply Fin.ext
      rw [hCol _ (by omega)]
      change p = (cycleAbsorberSwitchSlot m (k,l)).val
      rw [cycleAbsorberSwitchSlot_val,hVal]
    have hNext : label (p+1) = finRotate (2*m) (label p) := by
      apply Fin.ext
      rw [hLabel _ (by omega),finRotate_val_modulo,hLabel _ (by omega),Nat.mod_eq_of_lt (by omega)]
    have hFirst (a : Fin (2*m)) :
        F i (C.first.source a) = C.first.target a := by
      rw [← C.firstSource,← C.firstTarget]
      exact hP (Digraph.iSup_adj.mpr ⟨a,3,by decide,by omega,rfl,rfl⟩)
    have hSecond (a : Fin (2*m)) :
        F i (C.second.source a) = C.second.target a := by
      rw [← C.secondSource,← C.secondTarget]
      exact hP (Digraph.iSup_adj.mpr ⟨a,7,by decide,by omega,rfl,rfl⟩)
    have hLane₀ : cycleAbsorberLane false = 0 := rfl
    have hLane₁ : cycleAbsorberLane true = 1 := rfl
    fin_cases l
    · change col p = cycleAbsorberColumn k 0 at hColEq
      change cycleAbsorberSwitchSlot m (k,0) = label p at hk
      have hNext' := hNext.trans ((congrArg (finRotate (2*m)) hk.symm).trans
        (cycleAbsorberSwitchSlot_next k))
      rw [hColEq,hk.symm,hNext',hAux,(R.first k true).2,(R.first k false).2,
        (R.first k false).1,(R.first k true).1,hLane₀,hLane₁]
      refine ⟨?_,?_,?_,?_⟩
      · rw [← C.firstSource]
        exact C.paths.sameCycle_from_start _ hP _ 3 (by omega)
      · rw [← C.firstSource]
        exact C.paths.sameCycle_from_start _ hP _ 3 (by omega)
      · exact hFirst _
      · exact hFirst _
    · change col p = cycleAbsorberColumn k 1 at hColEq
      change cycleAbsorberSwitchSlot m (k,1) = label p at hk
      have hk' : alternateCycleAbsorberSwitchSlot m (k,0) = label p :=
        (cycleAbsorberSwitchSlot_next k).trans hk
      have hNext' := hNext.trans ((congrArg (finRotate (2*m)) hk'.symm).trans
        (alternate_cycle_absorber_switch_slot_next k))
      rw [hColEq,hk'.symm,hNext',hAux,(R.second k true).2,(R.second k false).2,
        (R.second k false).1,(R.second k true).1,hLane₀,hLane₁]
      refine ⟨?_,?_,?_,?_⟩
      · rw [← C.secondSource]
        exact C.paths.sameCycle_from_start _ hP _ 7 (by omega)
      · rw [← C.secondSource]
        exact C.paths.sameCycle_from_start _ hP _ 7 (by omega)
      · exact hSecond _
      · exact hSecond _
  refine {
    size := 2*m-1
    root := fun p => C.paths.vertex 0 (label p)
    left := fun p => R.rows.mark (false,col p)
    right := fun p => R.rows.mark (true,col p)
    sources := fun p _ h => Bool.false_ne_true (congrArg Prod.fst (R.rows.mark.injective h))
    distinct := ?_
    roots := fun p hp => ⟨(hSource p hp).1,(hSource p hp).2.1⟩
    cover := ?_
    cross := fun p hp => (hSource p hp).2.2
    mark := R.rows.mark
    step := finRotate (2*m+1)
    col := col
    final := Fin.last (2*m)
    reaches := ?_
    unused := ?_
    marks := fun _ _ => ⟨rfl,rfl⟩
    order := hAux.symm ▸ R.rows.orderedReserve }
  · intro p q hp hq
    have hne (u v : Bool) : R.rows.mark (u,col q) ≠ R.rows.mark (v,col p) := by
      intro he
      have h := congrArg (fun z : Bool × Fin (2*m+1) => z.2.val) (R.rows.mark.injective he)
      change (col q).val = (col p).val at h
      rw [hCol _ (by omega),hCol _ (by omega)] at h
      omega
    exact ⟨hne _ _,hne _ _,hne _ _,hne _ _⟩
  · intro z
    obtain ⟨a,ha⟩ := hCover z
    have he : label a.val = a := Fin.ext (hLabel _ a.isLt)
    exact ⟨a.val,by have := a.isLt; omega,he.symm ▸ ha⟩
  · intro s
    have hN : 2 ≤ 2*m+1 := by omega
    exact (isCycle_finRotate_of_le hN).sameCycle
      (finRotate_interval_ne_self hN s) (finRotate_interval_ne_self hN _)
  · intro p hp he
    have h := congrArg Fin.val he
    change (col p).val = 2*m at h
    rw [hCol _ (by omega)] at h
    omega

/-- Every source used by a sweep is on one of the two ordinary
switch layers of its associated half. -/
theorem CycleAbsorberResidualFactor.sweepData_source_slots {G H D : Digraph V}
    {A B : ℕ → Finset V} {m n b c r t : ℕ} {C : CycleAbsorberClaimOne G A m n}
    {E : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c)}
    (R : CycleAbsorberResidualFactor C B E D r) (hm : 0 < m) (hn : 8 ≤ n)
    (F : Fin t → Equiv.Perm V) (i j : Fin t)
    (hP : ∀ {x y}, C.paths.unionPaths.Adj x y → F i x = y)
    (hCover : ∀ z, ∃ a, (F i).SameCycle (C.paths.vertex 0 a) z)
    (hAux : F j = R.permutation) :
    let S := R.sweepData hm hn F i j hP hCover hAux
    ∀ p < S.size, ∀ x, x = S.left p ∨ x = S.right p → x ∈ A 3 ∨ x ∈ A 7 := by
  intro S p hp x hx
  obtain ⟨l,hl⟩ : ∃ l : Bool, x = R.rows.mark (l,S.col p) :=
    hx.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  have hCol : ∃ d : Fin (2*m), S.col p = d.castSucc := by
    have hv : (S.col p).val < 2*m := by
      have hle := (S.col p).isLt
      have hne : (S.col p).val ≠ 2*m := fun h => S.unused p hp (Fin.ext h)
      omega
    exact ⟨⟨(S.col p).val,hv⟩,Fin.ext rfl⟩
  obtain ⟨a,ha⟩ := hCol
  obtain ⟨⟨k,d⟩,rfl⟩ := (cycleAbsorberSwitchSlot m).surjective a
  rw [hl,ha]
  fin_cases d
  · change R.rows.mark (l,cycleAbsorberColumn k 0) ∈ A 3 ∨ _
    rw [(R.first k l).1]
    exact .inl (C.first.source _).prop
  · change _ ∨ R.rows.mark (l,cycleAbsorberColumn k 1) ∈ A 7
    rw [(R.second k l).1]
    exact .inr (C.second.source _).prop

end OverfullWork.DirectedRobustExpansion
