module

public import OverfullWork.OsthusStadenWindingLinks

@[expose] public section


/-! The physical exceptional bridges of Red0 yield links between cuts
on the two designated reduced cycles in Osthus–Staden §5.11. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {E I W : Type*} [Fintype E] [Fintype I] [Fintype W]

/-- A bridge whose incoming and outgoing arcs are confined to designated
red cells links two cuts on their respective reduced orbits. -/
theorem exceptional_bridge_touches_local_cuts
    (σ : Equiv.Perm I) (incoming outgoing : Finset I) (p : ℕ)
    (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:I) = (b:I) → p ≤ j)
    (hBaseOrbit : ∀ i, IsBlackAfterBalancing σ incoming outgoing i →
      ∃ a, σ.SameCycle (shadowSend σ incoming outgoing a) i)
    (hNoIn : ∀ i w y, i ∈ Set.range (shadowSend σ incoming outgoing) → (y,Sum.inr (i,w)) ∉ A)
    (hNoOut : ∀ i w y, i ∈ Set.range (shadowReceive σ incoming outgoing) → (Sum.inr (i,w),y) ∉ A)
    (e : E) (a b : ↥(incoming ∪ outgoing))
    (hPred : ∀ x, (x,Sum.inl e) ∈ A → x ∈ sliceCell (shadowSend σ incoming outgoing a))
    (hNext : ∀ x, (Sum.inl e,x) ∈ A → x ∈ sliceCell (shadowReceive σ incoming outgoing b))
    (q : Fin (p-4)) :
    ∃ c d : ↥(incoming ∪ outgoing),
      σ.SameCycle (shadowSend σ incoming outgoing c) (shadowSend σ incoming outgoing a) ∧
      σ.SameCycle (shadowSend σ incoming outgoing d) (shadowReceive σ incoming outgoing b) ∧
      ∀ F : Equiv.Perm (SliceVertex E I W),
        (∀ x, (x,F x) ∈ A ∨ ∃ j w z, x = .inr (j,w) ∧ F x = .inr (σ j,z)) →
        (∀ i, IsBlackAfterBalancing σ incoming outgoing i → ∀ x ∈ sliceCell i, (x,F x) ∉ A) →
        OsthusStadenLink F (fun r => sliceCell ((σ^(2+q.val)) (shadowSend σ incoming outgoing r))) c d := by
  let x : SliceVertex E I W := .inl e
  let u := shadowSend σ incoming outgoing a
  let v := shadowReceive σ incoming outgoing b
  have hLeftBlack : IsBlackAfterBalancing σ incoming outgoing (σ.symm u) :=
    black_before_red_pair σ incoming outgoing p (by have := q.isLt; omega) hSpacing a
  have hRightBlack : IsBlackAfterBalancing σ incoming outgoing (σ v) := by
    have hv : σ v = (σ^2) (shadowSend σ incoming outgoing b) := by simp [v,shadowReceive,pow_two]
    rw [hv]
    exact black_after_red_pair σ incoming outgoing p hSpacing b 2 (by decide) (by have := q.isLt; omega)
  obtain ⟨c,hc,hCut₁⟩ := black_cluster_local_cut (E := E) (W := W) σ incoming outgoing p
    hSpacing (σ.symm u) hLeftBlack (hBaseOrbit _ hLeftBlack)
  obtain ⟨d,hd,hCut₂⟩ := black_cluster_local_cut (E := E) (W := W) σ incoming outgoing p
    hSpacing (σ v) hRightBlack (hBaseOrbit _ hRightBlack)
  refine ⟨c,d,hc.of_symm_apply_right,hd.of_apply_right,?_⟩
  intro F hUse hBlack
  have hF : F (F.symm x) = x := F.apply_symm_apply _
  have hA₁ : (F.symm x,x) ∈ A := by
    have h := hUse (F.symm x)
    rw [hF] at h
    rcases h with h | ⟨_,_,_,_,h⟩
    · exact h
    · simp [x] at h
  have hA₂ : (x,F x) ∈ A := by
    rcases hUse x with h | ⟨_,_,_,h,_⟩
    · exact h
    · simp [x] at h
  have hLeft : F.symm x ∈ sliceCell u := hPred _ hA₁
  have hRight : F x ∈ sliceCell v := hNext _ hA₂
  have hLeftCell : F.symm (F.symm x) ∈ sliceCell (σ.symm u) := by
    obtain ⟨w,hw,he⟩ := mem_map.mp hLeft
    change (Sum.inr (u,w) : SliceVertex E I W) = F.symm x at he
    have h₂ : F (F.symm (F.symm x)) = .inr (u,w) := (F.apply_symm_apply _).trans he.symm
    obtain ⟨j,s,t,hs,ht⟩ := (hUse (F.symm (F.symm x))).resolve_left (by
      rw [h₂]
      exact hNoIn u w _ ⟨a,rfl⟩)
    have hj : σ j = u := (Prod.mk.inj (Sum.inr.inj (ht.symm.trans h₂))).1
    rw [hs,←σ.symm_apply_eq.mpr hj.symm]
    exact (mem_sliceCell _ _).mpr rfl
  have hRightCell : F (F x) ∈ sliceCell (σ v) := by
    obtain ⟨w,hw,he⟩ := mem_map.mp hRight
    change (Sum.inr (v,w) : SliceVertex E I W) = F x at he
    obtain ⟨j,s,t,hs,ht⟩ := (hUse (F x)).resolve_left (by
      rw [←he]
      exact hNoOut v w _ ⟨b,rfl⟩)
    have hj : j = v := (Prod.mk.inj (Sum.inr.inj (hs.symm.trans he.symm))).1
    rw [ht,hj]
    exact (mem_sliceCell _ _).mpr rfl
  have h₁ := (touchesCut_congr ((Equiv.Perm.SameCycle.refl F (F.symm x)).symm_apply_right)).mpr
    (hCut₁ q A F hUse hBlack _ hLeftCell)
  have h₂ := (touchesCut_congr ((Equiv.Perm.SameCycle.refl F (F x)).apply_right)).mpr
    (hCut₂ q A F hUse hBlack _ hRightCell)
  exact .exceptional x h₁ h₂

end OverfullWork.DirectedRobustExpansion
