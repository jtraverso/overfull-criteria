module

public import OverfullWork.OsthusStadenBatchSchedule
public import OverfullWork.OsthusStadenFactorGeometry

@[expose] public section


/-! Construct the black intervals used for factor orbit coverage from
the reduced permutation and the physical cluster coordinates. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {E I W : Type*} [Fintype E] [Fintype I] [Fintype W]

/-- A black cluster fixes a cut in every family independently of the
factor and the vertex that reaches the cut. -/
theorem black_cluster_local_cut
    (σ : Equiv.Perm I) (incoming outgoing : Finset I) (p : ℕ)
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:I) = (b:I) → p ≤ j)
    (i : I) (hi : IsBlackAfterBalancing σ incoming outgoing i)
    (hOrbit : ∃ a, σ.SameCycle (shadowSend σ incoming outgoing a) i) :
    ∃ a : ↥(incoming ∪ outgoing),
      σ.SameCycle (shadowSend σ incoming outgoing a) i ∧
      ∀ (q : Fin (p-4)) (A : Finset (SliceVertex E I W × SliceVertex E I W))
        (F : Equiv.Perm (SliceVertex E I W)),
        (∀ x, (x,F x) ∈ A ∨ ∃ j w z, x = .inr (j,w) ∧ F x = .inr (σ j,z)) →
        (∀ j, IsBlackAfterBalancing σ incoming outgoing j → ∀ x ∈ sliceCell j, (x,F x) ∉ A) →
        ∀ y ∈ sliceCell i,
          touchesCut F (sliceCell ((σ^(2+q.val)) (shadowSend σ incoming outgoing a))) y := by
  letI : DecidableEq (SliceVertex E I W) := Classical.decEq _
  let S := shadowSend σ incoming outgoing
  have hBlackEq (i : I) : IsBlackBetweenPairs σ S i ↔ IsBlackAfterBalancing σ incoming outgoing i := Iff.rfl
  let len (a : ↥(incoming ∪ outgoing)) := nextPairDistance σ S a-3
  let cell (a : ↥(incoming ∪ outgoing)) (j : ℕ) : Finset (SliceVertex E I W) :=
    sliceCell ((σ^(2+j)) (S a))
  have hLen (a : ↥(incoming ∪ outgoing)) : p-1 ≤ nextPairDistance σ S a := by
    obtain ⟨hPos,b,hEq⟩ := nextPairDistance_spec σ S a
    exact shadow_starts_spaced σ incoming outgoing p hSpacing a b _ hPos hEq.symm
  obtain ⟨a,j,hj,hj',he⟩ := every_black_in_pair_interval σ S i ((hBlackEq i).mpr hi) hOrbit
  refine ⟨a,he ▸ (Equiv.Perm.SameCycle.refl σ (S a)).pow_right,?_⟩
  intro q A F hUse hBlack y hy
  have hImage (a : ↥(incoming ∪ outgoing)) (j : ℕ) (hj : j < len a) :
      (cell a j).image F = cell a (j+1) := by
    let i := (σ^(2+j)) (S a)
    have he : σ i = (σ^(2+(j+1))) (S a) := by
      rw [show 2+(j+1) = 2+j+1 by omega,pow_succ',Equiv.Perm.mul_apply]
    have hi : IsBlackAfterBalancing σ incoming outgoing i :=
      (hBlackEq i).mp (black_before_next_pair σ S a (2+j) (by omega) (by dsimp [len] at hj; omega))
    have h := factor_black_successor_matching σ A F i hUse (hBlack i hi)
    ext x
    have he' := Iff.of_eq (congrArg (fun T : Finset (SliceVertex E I W) => x ∈ T) h)
    simpa only [cell,mem_image,he,i] using he'
  have hAt : y ∈ cell a (j-2) := by
    dsimp [cell]
    rwa [show 2+(j-2) = j by omega,he]
  have hJ : j-2 ≤ len a := by dsimp [len]; omega
  have hQ : q.val ≤ len a := by
    have hp := hLen a
    have hq := q.isLt
    dsimp [len]
    omega
  exact orbit_hits_of_cluster_interval F (cell a) (len a) (j-2) q.val hJ hQ (hImage a) hAt

/-- A black vertex reaches a cut on its own reduced cycle in each rotation family. -/
theorem black_vertex_touches_local_cut
    (σ : Equiv.Perm I) (incoming outgoing : Finset I) (p : ℕ)
    (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (F : Equiv.Perm (SliceVertex E I W))
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:I) = (b:I) → p ≤ j)
    (hBaseOrbit : ∀ i, IsBlackAfterBalancing σ incoming outgoing i →
      ∃ a, σ.SameCycle (shadowSend σ incoming outgoing a) i)
    (hUse : ∀ x, (x,F x) ∈ A ∨ ∃ j w z, x = .inr (j,w) ∧ F x = .inr (σ j,z))
    (hBlack : ∀ i, IsBlackAfterBalancing σ incoming outgoing i →
      ∀ x ∈ sliceCell i, (x,F x) ∉ A)
    (i : I) (y : SliceVertex E I W) (hi : IsBlackAfterBalancing σ incoming outgoing i)
    (hy : y ∈ sliceCell i) (q : Fin (p-4)) :
    ∃ a : ↥(incoming ∪ outgoing),
      σ.SameCycle (shadowSend σ incoming outgoing a) i ∧
        touchesCut F (sliceCell ((σ^(2+q.val)) (shadowSend σ incoming outgoing a))) y := by
  obtain ⟨a,ha,hCut⟩ := black_cluster_local_cut (E := E) (W := W) σ incoming outgoing p
    hSpacing i hi (hBaseOrbit i hi)
  exact ⟨a,ha,hCut q A F hUse hBlack y hy⟩

/-- Every factor orbit that hits a black cluster hits a cut from each
rotation family. The cuts lie in the first `p−3` black clusters of
each full interval, even when an interval is longer. -/
theorem factor_orbit_cut_coverage
    (σ : Equiv.Perm I) (incoming outgoing : Finset I) (p : ℕ)
    (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (F : Equiv.Perm (SliceVertex E I W))
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:I) = (b:I) → p ≤ j)
    (hBaseOrbit : ∀ i, IsBlackAfterBalancing σ incoming outgoing i →
      ∃ a, σ.SameCycle (shadowSend σ incoming outgoing a) i)
    (hUse : ∀ x, (x,F x) ∈ A ∨ ∃ j w z, x = .inr (j,w) ∧ F x = .inr (σ j,z))
    (hBlack : ∀ i, IsBlackAfterBalancing σ incoming outgoing i →
      ∀ x ∈ sliceCell i, (x,F x) ∉ A)
    (hHit : ∀ x, ∃ i y, IsBlackAfterBalancing σ incoming outgoing i ∧
      y ∈ sliceCell i ∧ F.SameCycle x y) :
    ∀ (q : Fin (p-4)) x, ∃ a : ↥(incoming ∪ outgoing),
      touchesCut F (sliceCell ((σ^(2+q.val)) (shadowSend σ incoming outgoing a))) x := by
  intro q x
  obtain ⟨i,y,hi,hy,hxy⟩ := hHit x
  obtain ⟨a,_,ha⟩ := black_vertex_touches_local_cut σ incoming outgoing p A F hSpacing hBaseOrbit
    hUse hBlack i y hi hy q
  exact ⟨a,(touchesCut_congr hxy).mpr ha⟩

/-- The orientation restriction in Red6′ and independence of the
exceptional set imply that every factor orbit meets a black cluster.
This is the first coverage assertion in §5.11. -/
theorem every_factor_orbit_hits_black
    (σ : Equiv.Perm I) (incoming outgoing : Finset I) (p : ℕ) (hp : 4 ≤ p)
    (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (F : Equiv.Perm (SliceVertex E I W))
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:I) = (b:I) → p ≤ j)
    (hUse : ∀ x, (x,F x) ∈ A ∨ ∃ j w z, x = .inr (j,w) ∧ F x = .inr (σ j,z))
    (hNoIn : ∀ i w y, i ∈ Set.range (shadowSend σ incoming outgoing) → (y,Sum.inr (i,w)) ∉ A)
    (hNoOut : ∀ i w y, i ∈ Set.range (shadowReceive σ incoming outgoing) → (Sum.inr (i,w),y) ∉ A)
    (hEx : ∀ e f : E, (Sum.inl e,Sum.inl f) ∉ A) :
    ∀ x, ∃ i y, IsBlackAfterBalancing σ incoming outgoing i ∧
      y ∈ sliceCell i ∧ F.SameCycle x y := by
  let black : Set (SliceVertex E I W) := {v | ∃ i, IsBlackAfterBalancing σ incoming outgoing i ∧ v ∈ sliceCell i}
  let redIn : Set (SliceVertex E I W) := {v | ∃ a : ↥(incoming ∪ outgoing),
    v ∈ sliceCell (shadowReceive σ incoming outgoing a)}
  let redOut : Set (SliceVertex E I W) := {v | ∃ a : ↥(incoming ∪ outgoing),
    v ∈ sliceCell (shadowSend σ incoming outgoing a)}
  have hOrd : ∀ i w, (Sum.inr (i,w) : SliceVertex E I W) ∈ black ∨
      (Sum.inr (i,w) : SliceVertex E I W) ∈ redIn ∨ (Sum.inr (i,w) : SliceVertex E I W) ∈ redOut := by
    intro i w
    by_cases hi : IsBlackAfterBalancing σ incoming outgoing i
    · exact Or.inl ⟨i,hi,(mem_sliceCell _ _).mpr rfl⟩
    · by_cases ho : i ∈ Set.range (shadowSend σ incoming outgoing)
      · obtain ⟨a,ha⟩ := ho
        exact Or.inr (Or.inr ⟨a,(mem_sliceCell _ _).mpr (congrArg some ha.symm)⟩)
      · have hi' : i ∈ Set.range (shadowReceive σ incoming outgoing) := by
          by_contra! h
          exact hi ⟨ho,h⟩
        obtain ⟨a,ha⟩ := hi'
        exact Or.inr (Or.inl ⟨a,(mem_sliceCell _ _).mpr (congrArg some ha.symm)⟩)
  have hForward : ∀ x ∈ redIn, F x ∈ black := by
    rintro x ⟨a,ha⟩
    let r := shadowReceive σ incoming outgoing a
    obtain ⟨w,_,rfl⟩ := mem_map.mp ha
    change ∃ j, IsBlackAfterBalancing σ incoming outgoing j ∧ F (.inr (r,w)) ∈ sliceCell j
    obtain ⟨i,v,z,hx,hy⟩ := (hUse (.inr (r,w))).resolve_left (hNoOut r w _ ⟨a,rfl⟩)
    have hir : i = r := (Prod.mk.inj (Sum.inr.inj hx)).1.symm
    subst i
    refine ⟨σ r,?_,(mem_sliceCell _ _).mpr (by rw [hy]; rfl)⟩
    have he : σ r = (σ^2) (shadowSend σ incoming outgoing a) := by simp [r,shadowReceive,pow_two]
    rw [he]
    exact black_after_red_pair σ incoming outgoing p hSpacing a 2 (by decide) (by omega)
  have hBackward : ∀ x ∈ redOut, F.symm x ∈ black := by
    rintro x ⟨a,ha⟩
    let r := shadowSend σ incoming outgoing a
    obtain ⟨w,_,rfl⟩ := mem_map.mp ha
    change ∃ j, IsBlackAfterBalancing σ incoming outgoing j ∧ F.symm (.inr (r,w)) ∈ sliceCell j
    have he : F (F.symm (Sum.inr (r,w))) = Sum.inr (r,w) := F.apply_symm_apply _
    obtain ⟨j,v,z,hx,hy⟩ := (hUse (F.symm (.inr (r,w)))).resolve_left (by
      rw [he]
      exact hNoIn r w _ ⟨a,rfl⟩)
    have hr : r = σ j := (Prod.mk.inj (Sum.inr.inj (he.symm.trans hy))).1
    have hj : j = σ.symm r := (σ.symm_apply_eq.mpr hr).symm
    refine ⟨j,?_,(mem_sliceCell _ _).mpr (by rw [hx]; rfl)⟩
    rw [hj]
    exact black_before_red_pair σ incoming outgoing p hp hSpacing a
  have hExc : ∀ x, x ∉ black → x ∉ redIn → x ∉ redOut → F x ∈ black ∨ F x ∈ redIn ∨ F x ∈ redOut := by
    intro x hb hi ho
    rcases x with e | ⟨i,w⟩
    · rcases hF : F (.inl e) with f | ⟨j,v⟩
      · have hh := hUse (.inl e)
        rw [hF] at hh
        rcases hh with hh | ⟨_,_,_,hh,_,_⟩
        exact (hEx e f hh).elim
      · exact hOrd j v
    · exact ((hOrd i w).elim hb (fun h => h.elim hi ho)).elim
  intro x
  obtain ⟨y,⟨i,hi,hy⟩,h⟩ := every_orbit_hits_black F black redIn redOut hForward hBackward hExc x
  exact ⟨i,y,hi,hy,h⟩

/-- The orbit projection of the unwinding and one red cluster per
primary cluster ensure that every refined orbit has a red-pair source. -/
theorem every_refined_orbit_hits_red_pair {U : Type*}
    (σ : Equiv.Perm I) (φ : Equiv.Perm U) (project : I → U)
    (incoming outgoing : Finset I)
    (hOrbit : ∀ x y, σ.SameCycle x y ↔ φ.SameCycle (project x) (project y))
    (hRed : ∀ u, ∃ a : ↥(incoming ∪ outgoing), project a = u) :
    ∀ i, ∃ a : ↥(incoming ∪ outgoing), σ.SameCycle (shadowSend σ incoming outgoing a) i := by
  intro i
  obtain ⟨a,ha⟩ := hRed (project i)
  have h : σ.SameCycle (a:I) i := (hOrbit _ _).mpr (ha ▸ Equiv.Perm.SameCycle.refl φ (project i))
  refine ⟨a,?_⟩
  by_cases hin : (a:I) ∈ incoming
  · simpa only [shadowSend,hin,if_true] using h.symm_apply_left
  · simpa only [shadowSend,hin,if_false] using h

/-- Cuts from distinct red pairs or rotation families have disjoint
physical source cells. -/
theorem disjoint_black_cut_cells (σ : Equiv.Perm I) (incoming outgoing : Finset I) (p : ℕ)
    (hSep : ∀ u ∈ outgoing, σ u ∉ incoming)
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:I) = (b:I) → p ≤ j)
    (a b : ↥(incoming ∪ outgoing) × Fin (p-4)) (h : a ≠ b) :
    Disjoint (sliceCell (E := E) (W := W) ((σ^(2+a.2.val)) (shadowSend σ incoming outgoing a.1)))
      (sliceCell ((σ^(2+b.2.val)) (shadowSend σ incoming outgoing b.1))) := by
  rw [disjoint_left]
  intro x hx hy
  exact h (black_cut_sources_injective σ incoming outgoing p hSep hSpacing
    (Option.some.inj (((mem_sliceCell _ x).mp hx).symm.trans ((mem_sliceCell _ x).mp hy))))

end OverfullWork.DirectedRobustExpansion
