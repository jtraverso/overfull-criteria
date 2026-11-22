module

public import OverfullWork.OsthusStadenCutCoverage
public import OverfullWork.OsthusStadenMergeStage

@[expose] public section


/-! Construct a winding link for two consecutive red pairs. The path
starts just after the old cut and ends just before the new cut. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {E I W R : Type*} [Fintype E] [Fintype I] [Fintype W]

theorem consecutive_pair_winding_link (σ : Equiv.Perm I) (start : R → I)
    (hpairs : Function.Injective start) (cut : ℕ) (hcut : 2 ≤ cut)
    (hLength : ∀ a, cut+1 < nextPairDistance σ start a)
    (a b : R) (hNext : (σ^(nextPairDistance σ start a)) (start a) = start b)
    (F : Equiv.Perm (SliceVertex E I W))
    (hMatch : ∀ i, IsBlackBetweenPairs σ start i → (sliceCell i).image F = sliceCell (σ i))
    (hInMatch : ∀ r, (sliceCell (σ (start r))).image F = sliceCell (σ (σ (start r))))
    (hCross : ∃ x ∈ sliceCell (start b), F x ∈ sliceCell (σ (start b))) :
    OsthusStadenLink F (fun r => sliceCell ((σ^cut) (start r))) a b := by
  let d := nextPairDistance σ start a
  let k := d-(cut+1)
  let n := d-1
  let C := fun j => sliceCell (E := E) (W := W) ((σ^(cut+1+j)) (start a))
  have hd : cut+1 < d := hLength a
  have hk : k < n := by dsimp [k,n]; omega
  have hAfter (j : ℕ) (hj : k ≤ j) :
      (σ^(cut+1+j)) (start a) = (σ^(j-k)) (start b) := by
    rw [←hNext,←Equiv.Perm.mul_apply,←pow_add]
    congr 2
    dsimp [k]
    omega
  have hAt : C k = sliceCell (start b) := by
    unfold C
    rw [hAfter k le_rfl,Nat.sub_self,pow_zero,Equiv.Perm.one_apply]
  have hAt' : C (k+1) = sliceCell (σ (start b)) := by
    unfold C
    rw [hAfter (k+1) (by omega),show k+1-k = 1 by omega,pow_one]
  have hSucc (j : ℕ) : σ ((σ^(cut+1+j)) (start a)) = (σ^(cut+1+(j+1))) (start a) := by
    rw [show cut+1+(j+1) = cut+1+j+1 by omega,pow_succ',Equiv.Perm.mul_apply]
  have hImage {X Y : Finset (SliceVertex E I W)} (d₁ d₂ : DecidableEq (SliceVertex E I W))
      (h : @Finset.image _ _ d₁ F X = Y) : @Finset.image _ _ d₂ F X = Y := by
    ext v
    simpa only [mem_image] using Iff.of_eq (congrArg (fun S : Finset (SliceVertex E I W) => v ∈ S) h)
  refine .winding C n k hk ?_ ?_ ?_ ?_ ?_
  · unfold C
    rw [add_zero,pow_succ',Equiv.Perm.mul_apply]
    exact (hImage _ _ (hMatch _ (black_before_next_pair σ start a cut hcut (by omega)))).symm
  · unfold C
    rw [hAfter n hk.le,show n-k = cut by dsimp [n,k]; omega]
  · intro j hj hjk
    by_cases h : j < k
    · unfold C
      rw [←hSucc]
      apply hImage _ _
      apply hMatch
      exact black_before_next_pair σ start a _ (by omega) (by dsimp [k] at h; omega)
    · have h' : k ≤ j := by omega
      unfold C
      rw [hAfter j h',hAfter (j+1) (by omega)]
      have he : j+1-k = j-k+1 := by omega
      rw [he,pow_succ',Equiv.Perm.mul_apply]
      by_cases hj' : j-k = 1
      · rw [hj',pow_one]
        exact hImage _ _ (hInMatch b)
      · apply hImage _ _
        apply hMatch
        exact black_before_next_pair σ start b _ (by omega) (by
          have hLen := hLength b
          dsimp [n,k] at hj ⊢
          omega)
  · rwa [hAt,hAt']
  · intro j hj x hx r hxr
    have hEq : (σ^(cut+1+j)) (start a) = (σ^cut) (start r) :=
      Option.some.inj (((mem_sliceCell _ x).mp hx).symm.trans ((mem_sliceCell _ x).mp hxr))
    have heq {u v : R} {s t : ℕ} (hs : s < nextPairDistance σ start u)
        (ht : t < nextPairDistance σ start v) (he : (σ^s) (start u) = (σ^t) (start v)) :
        s = t := by
      exact congrArg (fun z : Σ a : R, Fin (nextPairDistance σ start a) => z.2.val)
        (pair_interval_location_injective σ start hpairs
          (a₁ := ⟨u,⟨s,hs⟩⟩) (a₂ := ⟨v,⟨t,ht⟩⟩) he)
    by_cases hj' : j < k
    · have h := heq (show cut+1+j < nextPairDistance σ start a by dsimp [k,d] at hj'; omega)
        (show cut < nextPairDistance σ start r from (Nat.lt_succ_self cut).trans (hLength r)) hEq
      omega
    · rw [hAfter j (by omega)] at hEq
      have h := heq (show j-k < nextPairDistance σ start b by
          have hLen := hLength b
          dsimp [n,k] at hj ⊢
          omega)
        (show cut < nextPairDistance σ start r from (Nat.lt_succ_self cut).trans (hLength r)) hEq
      dsimp [n,k] at hj h
      omega

/-- Consecutive red-pair links connect all cuts on any one reduced
cycle. Induct on the number of steps, subtracting the first return. -/
theorem consecutive_pair_links_connect_orbit (σ : Equiv.Perm I) (start : R → I)
    (hInj : Function.Injective start) {r : R → R → Prop}
    (hLink : ∀ a b, (σ^(nextPairDistance σ start a)) (start a) = start b → r a b) :
    ∀ a b, σ.SameCycle (start a) (start b) → Relation.EqvGen r a b := by
  have hSteps : ∀ k : ℕ, ∀ a b, (σ^k) (start a) = start b → Relation.EqvGen r a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a b he
      by_cases hk : k = 0
      · subst k
        have hab : a = b := hInj (by simpa only [pow_zero,Equiv.Perm.one_apply] using he)
        subst b
        exact Relation.EqvGen.refl _
      · let d := nextPairDistance σ start a
        obtain ⟨hPos,c,hc⟩ := nextPairDistance_spec σ start a
        have hd : d ≤ k := nextPairDistance_min σ start a k (Nat.pos_of_ne_zero hk) ⟨b,he.symm⟩
        have hdc : (σ^d) (start a) = start c := hc.symm
        have hcb : (σ^(k-d)) (start c) = start b := by
          rw [←hdc,←Equiv.Perm.mul_apply,←pow_add,Nat.sub_add_cancel hd]
          exact he
        have hPos' : 0 < d := hPos
        exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (hLink a c hdc))
          (ih (k-d) (by omega) c b hcb)
  intro a b h
  obtain ⟨k,_,hk⟩ := h.exists_pow_eq'
  exact hSteps k a b hk

/-- The primary Hamilton order links the already connected intervals
of the reduced cycles, using one prepared exceptional bridge per step. -/
theorem bridge_chain_connects_cut_indices {P : Type*} [Fintype P]
    (σ : Equiv.Perm I) (start : R → I) (hInj : Function.Injective start)
    (project : I → P) (C : Equiv.Perm P) (anchor : P → R)
    (r : R → R → Prop)
    (hNext : ∀ a b, (σ^(nextPairDistance σ start a)) (start a) = start b → r a b)
    (hCycle : ∀ u v, C.SameCycle u v)
    (hAnchor : ∀ a, σ.SameCycle (start a) (start (anchor (project (start a)))))
    (hBridge : ∀ u, ∃ a b, σ.SameCycle (start (anchor u)) (start a) ∧ r a b ∧
      σ.SameCycle (start b) (start (anchor (C u)))) :
    ∀ a b, Relation.EqvGen r a b := by
  have hWithin := consecutive_pair_links_connect_orbit σ start hInj hNext
  have hStep (u : P) : Relation.EqvGen r (anchor u) (anchor (C u)) := by
    obtain ⟨a,b,hA,hR,hB⟩ := hBridge u
    exact Relation.EqvGen.trans _ _ _ (hWithin _ _ hA)
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hR) (hWithin _ _ hB))
  have hPow (u : P) (k : ℕ) : Relation.EqvGen r (anchor u) (anchor ((C^k) u)) := by
    induction k with
    | zero => simpa only [pow_zero,Equiv.Perm.one_apply] using Relation.EqvGen.refl (r := r) (anchor u)
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact Relation.EqvGen.trans _ _ _ ih (hStep ((C^k) u))
  intro a b
  let u := project (start a)
  let v := project (start b)
  obtain ⟨k,_,h⟩ := (hCycle u v).exists_pow_eq'
  have hm := hPow u k
  rw [h] at hm
  exact Relation.EqvGen.trans _ _ _ (hWithin _ _ (hAnchor a))
    (Relation.EqvGen.trans _ _ _ hm (Relation.EqvGen.symm _ _ (hWithin _ _ (hAnchor b))))

end OverfullWork.DirectedRobustExpansion
