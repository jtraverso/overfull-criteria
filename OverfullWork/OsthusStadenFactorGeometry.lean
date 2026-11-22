module

public import OverfullWork.OsthusStadenPhysicalFactors
public import OverfullWork.OsthusStadenCorridors

@[expose] public section


/-! Read the successor matchings and the unmarked red transition
directly from the physical factorization of §5.10. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {E I W : Type*} [Fintype W]

noncomputable def sliceCell (i : I) : Finset (SliceVertex E I W) :=
  (univ : Finset W).map ⟨fun w => .inr (i,w),fun _ _ h => (Prod.mk.inj (Sum.inr.inj h)).2⟩

theorem mem_sliceCell (i : I) (v : SliceVertex E I W) :
    v ∈ sliceCell i ↔ sliceLabel v = some i := by
  simp only [sliceCell,mem_map,mem_univ,true_and]
  constructor
  · rintro ⟨w,rfl⟩
    rfl
  · intro h
    rcases v with e | ⟨j,w⟩
    · cases h
    · have hji : j = i := Option.some.inj h
      subst j
      exact ⟨w,rfl⟩

theorem sliceCell_card (i : I) : (sliceCell (E := E) (W := W) i).card = Fintype.card W := by
  simp [sliceCell]

omit [Fintype W] in
theorem factor_uses_physical_arc (σ : Equiv.Perm I) (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (D : I → Digraph W) {κ : ℕ} (F : Fin κ → Equiv.Perm (SliceVertex E I W))
    (hMult : ∀ x y, ((univ : Finset (Fin κ)).filter (fun f => F f x = y)).card =
      arcMultiplicity A x y + DirectedMultigraphFactors.successorPairArcs σ D x y)
    (f : Fin κ) (x : SliceVertex E I W) :
    (x,F f x) ∈ A ∨ ∃ i w z, x = .inr (i,w) ∧ F f x = .inr (σ i,z) ∧ (D i).Adj w z := by
  by_cases hAx : (x,F f x) ∈ A
  · exact Or.inl hAx
  right
  have hPos := card_pos.mpr (show ((univ : Finset (Fin κ)).filter (fun q => F q x = F f x)).Nonempty from
    ⟨f,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩)
  rw [hMult] at hPos
  simp only [arcMultiplicity,if_neg hAx,zero_add] at hPos
  generalize F f x = y at hPos ⊢
  rcases x with e | ⟨i,w⟩
  · simp [DirectedMultigraphFactors.successorPairArcs] at hPos
  · rcases y with e | ⟨j,z⟩
    · simp [DirectedMultigraphFactors.successorPairArcs] at hPos
    · have h : j = σ i ∧ (D i).Adj w z := by
        by_contra h
        simp [DirectedMultigraphFactors.successorPairArcs,h] at hPos
      exact ⟨i,w,z,rfl,by rw [h.1],h.2⟩

/-- Black cells give a genuine perfect matching of each factor to the
successor cell. No cardinality can be lost since the cells are equal. -/
theorem factor_black_successor_matching (σ : Equiv.Perm I)
    (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (F : Equiv.Perm (SliceVertex E I W)) (i : I)
    (hUse : ∀ x, (x,F x) ∈ A ∨ ∃ j w z, x = .inr (j,w) ∧ F x = .inr (σ j,z))
    (hBlack : ∀ x ∈ sliceCell i, (x,F x) ∉ A) :
    (sliceCell i).image F = sliceCell (σ i) := by
  apply eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨j,w,z,hx',hy'⟩ := (hUse x).resolve_left (hBlack x hx)
    have hj : j = i := by
      have hLabel := (mem_sliceCell i x).mp hx
      rw [hx'] at hLabel
      exact Option.some.inj hLabel
    rw [hy',hj]
    exact (mem_sliceCell _ _).mpr rfl
  · rw [card_image_of_injective _ F.injective,sliceCell_card,sliceCell_card]

/-- At least one original successor arc crosses a red pair whenever
the vertices allowed to start non-successor arcs are a proper subset. -/
theorem factor_unmarked_red_transition (σ : Equiv.Perm I)
    (A : Finset (SliceVertex E I W × SliceVertex E I W))
    (F : Equiv.Perm (SliceVertex E I W)) (i : I) (red : Finset (SliceVertex E I W))
    (hUse : ∀ x, (x,F x) ∈ A ∨ ∃ j w z, x = .inr (j,w) ∧ F x = .inr (σ j,z))
    (hRed : ∀ x ∈ sliceCell i, (x,F x) ∈ A → x ∈ red)
    (hSize : red.card < Fintype.card W) :
    ∃ x ∈ sliceCell i, F x ∈ sliceCell (σ i) := by
  apply exists_unmarked_transition F _ _ red (by rwa [sliceCell_card])
  intro x hx h
  obtain ⟨j,w,z,hx',hy'⟩ := (hUse x).resolve_left (fun hA => h (hRed x hx hA))
  have hj : j = i := by
    have hLabel := (mem_sliceCell i x).mp hx
    rw [hx'] at hLabel
    exact Option.some.inj hLabel
  rw [hy',hj]
  exact (mem_sliceCell _ _).mpr rfl

end OverfullWork.DirectedRobustExpansion
