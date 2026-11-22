module

public import OverfullWork.OsthusStadenExceptionalLinks

@[expose] public section


/-! One common graph of links for every factor assigned to a rotation
family. The exceptional bridges join the reduced orbits along the
Hamilton order on the primary clusters. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {E I W : Type*}

def UsesSliceArcs (σ : Equiv.Perm I)
    (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (F : Equiv.Perm (SliceVertex E I W)) : Prop :=
  ∀ x, (x,F x) ∈ A ∨ ∃ j w z, x = .inr (j,w) ∧ F x = .inr (σ j,z)

structure RedArcRouting [Fintype W] (σ : Equiv.Perm I) (incoming outgoing : Finset I)
    (A : Finset (SliceVertex E I W × SliceVertex E I W)) where
  black : ∀ i, IsBlackAfterBalancing σ incoming outgoing i →
    ∀ x ∈ sliceCell i, ∀ y, (x,y) ∉ A
  noIn : ∀ i w y, i ∈ Set.range (shadowSend σ incoming outgoing) → (y,Sum.inr (i,w)) ∉ A
  noOut : ∀ i w y, i ∈ Set.range (shadowReceive σ incoming outgoing) → (Sum.inr (i,w),y) ∉ A
  independent : ∀ e f : E, (Sum.inl e,Sum.inl f) ∉ A
  proper : ∀ a : ↥(incoming ∪ outgoing), ∃ S : Finset (SliceVertex E I W),
    S.card < Fintype.card W ∧
      ∀ x ∈ sliceCell (shadowSend σ incoming outgoing a), ∀ y, (x,y) ∈ A → x ∈ S

variable [Fintype E] [Fintype I] [Fintype W]

/-- The exceptional stars prepared in Red0 fix the input and output
reduced cycles. The same cut-link graph works for all 1-factors. -/
theorem exists_common_cut_links {P : Type*} [Fintype P]
    (σ : Equiv.Perm I) (φ : Equiv.Perm P) (project : I → P) (C : Equiv.Perm P)
    (incoming outgoing : Finset I) (p : ℕ)
    (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (routing : RedArcRouting σ incoming outgoing A)
    (hSep : ∀ u ∈ outgoing, σ u ∉ incoming)
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:I) = (b:I) → p ≤ j)
    (hOrbit : ∀ x y, σ.SameCycle x y ↔ φ.SameCycle (project x) (project y))
    (hPrimary : ∀ u, ∃ a : ↥(incoming ∪ outgoing),
      φ.SameCycle (project (shadowSend σ incoming outgoing a)) u)
    (hC : ∀ u v, C.SameCycle u v)
    (hBridges : ∀ u, ∃ (e : E) (a b : ↥(incoming ∪ outgoing)),
      φ.SameCycle (project (shadowSend σ incoming outgoing a)) u ∧
      φ.SameCycle (project (shadowReceive σ incoming outgoing b)) (C u) ∧
      (∀ x, (x,Sum.inl e) ∈ A → x ∈ sliceCell (shadowSend σ incoming outgoing a)) ∧
      (∀ x, (Sum.inl e,x) ∈ A → x ∈ sliceCell (shadowReceive σ incoming outgoing b)))
    (q : Fin (p-4)) :
    let R := ↥(incoming ∪ outgoing)
    let cut := fun a : R => sliceCell ((σ^(2+q.val)) (shadowSend σ incoming outgoing a))
    ∃ rel : R → R → Prop,
      (∀ a b, Relation.EqvGen rel a b) ∧
      ∀ F : Equiv.Perm (SliceVertex E I W), UsesSliceArcs σ A F →
        (∀ x, ∃ a, touchesCut F (cut a) x) ∧
        ∀ a b, rel a b → OsthusStadenLink F cut a b := by
  let R := ↥(incoming ∪ outgoing)
  let S : R → I := shadowSend σ incoming outgoing
  let k := 2+q.val
  let cut (a : R) := sliceCell (E := E) (W := W) ((σ^k) (S a))
  let rel (a b : R) := ∀ F : Equiv.Perm (SliceVertex E I W),
      UsesSliceArcs σ A F → OsthusStadenLink F cut a b
  choose anchor hAnchor using hPrimary
  have hBase (i : I) : ∃ a : R, σ.SameCycle (S a) i :=
    ⟨anchor (project i),(hOrbit _ _).mpr (hAnchor (project i))⟩
  have hInj := shadowSend_injective σ incoming outgoing hSep
  have hLen (a : R) : k+1 < nextPairDistance σ S a := by
    obtain ⟨hPos,b,hEq⟩ := nextPairDistance_spec σ S a
    have h := shadow_starts_spaced σ incoming outgoing p hSpacing a b _ hPos hEq.symm
    have hq := q.isLt
    dsimp [k]
    omega
  have hNext (a b : R) (he : (σ^(nextPairDistance σ S a)) (S a) = S b) : rel a b := by
    intro F hUse
    apply consecutive_pair_winding_link σ S hInj k (by dsimp [k]; omega) hLen a b he F
    · intro i hi
      exact factor_black_successor_matching σ A F i hUse (fun x hx => routing.black i hi x hx _)
    · intro r
      apply factor_black_successor_matching σ A F _ hUse
      intro x hx
      obtain ⟨w,_,he⟩ := mem_map.mp hx
      change Sum.inr (σ (S r),w) = x at he
      rw [←he]
      exact routing.noOut _ _ _ ⟨r,rfl⟩
    · obtain ⟨red,hSize,hRed⟩ := routing.proper b
      exact factor_unmarked_red_transition σ A F _ red hUse
        (fun x hx hA => hRed x hx _ hA) hSize
  have hInter (u : P) : ∃ a b : R, σ.SameCycle (S (anchor u)) (S a) ∧ rel a b ∧
      σ.SameCycle (S b) (S (anchor (C u))) := by
    obtain ⟨e,a,b,hA,hB,hPred,hDest⟩ := hBridges u
    obtain ⟨f,g,hf,hg,hLink⟩ := exceptional_bridge_touches_local_cuts σ incoming outgoing p A hSpacing
      (fun i _ => hBase i) routing.noIn routing.noOut e a b hPred hDest q
    refine ⟨f,g,?_,fun F hF => hLink F hF (fun i hi x hx => routing.black i hi x hx _),?_⟩
    · exact ((hOrbit _ _).mpr ((hAnchor u).trans hA.symm)).trans hf.symm
    · exact hg.trans ((hOrbit _ _).mpr (hB.trans (hAnchor (C u)).symm))
  refine ⟨rel,?_,?_⟩
  · apply bridge_chain_connects_cut_indices σ S hInj project C anchor rel hNext hC _ hInter
    intro a
    exact (hOrbit _ _).mpr (hAnchor (project (S a))).symm
  · intro F hF
    have hBlack (i : I) (hi : IsBlackAfterBalancing σ incoming outgoing i) (x : SliceVertex E I W)
        (hx : x ∈ sliceCell i) := routing.black i hi x hx (F x)
    refine ⟨factor_orbit_cut_coverage σ incoming outgoing p A F hSpacing (fun i _ => hBase i)
      hF hBlack (every_factor_orbit_hits_black σ incoming outgoing p (by have := q.isLt; omega)
        A F hSpacing hF routing.noIn routing.noOut routing.independent) q,?_⟩
    exact fun a b h => h F hF

end OverfullWork.DirectedRobustExpansion
