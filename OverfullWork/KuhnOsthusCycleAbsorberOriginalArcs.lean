module

public import Mathlib.Combinatorics.Digraph.Basic

@[expose] public section


/-! Replace the exceptional shortcuts of a factor by their
original two-arc paths. An exceptional vertex may be used by
several intervals, so the shortcut occurrences are kept distinct. -/
namespace OverfullWork.DirectedRobustExpansion

open Function
open scoped Classical
variable {V Z J K : Type*}

/-- Expand each designated outgoing arc into a two-arc path through
its specified exceptional vertex. Different occurrences may use the
same exceptional vertex. -/
def restoreExceptionalFactor (σ : Equiv.Perm V) (source : J ↪ V) (exceptional : J → Z) :
    Digraph (V ⊕ Z) :=
  ⟨fun x y => match x,y with
    | .inl u,.inl v => σ u = v ∧ u ∉ Set.range source
    | .inl u,.inr z => ∃ j, source j = u ∧ exceptional j = z
    | .inr z,.inl v => ∃ j, exceptional j = z ∧ σ (source j) = v
    | .inr _,.inr _ => False⟩

/-- At an ordinary vertex, reinserting the exceptional vertices
preserves the unique incoming and outgoing slots of the factor. -/
theorem restoreExceptionalFactor_ordinary_slots (σ : Equiv.Perm V)
    (source : J ↪ V) (exceptional : J → Z) (u : V) :
    (∃! x, (restoreExceptionalFactor σ source exceptional).Adj (.inl u) x) ∧
    (∃! x, (restoreExceptionalFactor σ source exceptional).Adj x (.inl u)) := by
  classical
  constructor
  · by_cases h : u ∈ Set.range source
    · obtain ⟨j,rfl⟩ := h
      refine ⟨.inr (exceptional j),⟨j,rfl,rfl⟩,?_⟩
      rintro (v | z) hv
      · exact (hv.2 ⟨j,rfl⟩).elim
      · obtain ⟨k,hk,hz⟩ := hv
        have he := source.injective hk
        exact congrArg Sum.inr ((congrArg exceptional he).symm.trans hz).symm
    · refine ⟨.inl (σ u),⟨rfl,h⟩,?_⟩
      rintro (v | z) hv
      · exact congrArg Sum.inl hv.1.symm
      · obtain ⟨j,hj,_⟩ := hv
        exact (h ⟨j,hj⟩).elim
  · by_cases h : σ.symm u ∈ Set.range source
    · obtain ⟨j,hj⟩ := h
      have he : σ (source j) = u := σ.eq_symm_apply.mp hj
      refine ⟨.inr (exceptional j),⟨j,rfl,he⟩,?_⟩
      rintro (v | z) hv
      · have hEq : v = σ.symm u := σ.eq_symm_apply.mpr hv.1
        exact (hv.2 ⟨j,hj.trans hEq.symm⟩).elim
      · obtain ⟨k,hz,hk⟩ := hv
        have hEq : k = j := source.injective (σ.injective (hk.trans he.symm))
        exact congrArg Sum.inr ((congrArg exceptional hEq).symm.trans hz).symm
    · refine ⟨.inl (σ.symm u),⟨σ.apply_symm_apply _,h⟩,?_⟩
      rintro (v | z) hv
      · exact congrArg Sum.inl (σ.eq_symm_apply.mpr hv.1)
      · obtain ⟨j,_,hj⟩ := hv
        exact (h ⟨j,σ.eq_symm_apply.mpr hj⟩).elim

/-- If each exceptional vertex occurs once, the restored arcs are
the exact graph of a permutation of the original vertices. -/
theorem exists_restored_exceptional_permutation (σ : Equiv.Perm V) (source : Z ↪ V) :
    ∃ τ : Equiv.Perm (V ⊕ Z), ∀ x y, (restoreExceptionalFactor σ source id).Adj x y ↔ τ x = y := by
  let D := restoreExceptionalFactor σ source id
  have out (x : V ⊕ Z) : ∃! y, D.Adj x y := by
    cases x with
    | inl v => exact (restoreExceptionalFactor_ordinary_slots σ source id v).1
    | inr z =>
      refine ⟨.inl (σ (source z)),⟨z,rfl,rfl⟩,?_⟩
      rintro (y | w) h
      · obtain ⟨j,he,hy⟩ := h
        change j = z at he
        subst j
        exact congrArg Sum.inl hy.symm
      · exact h.elim
  have inc (y : V ⊕ Z) : ∃! x, D.Adj x y := by
    cases y with
    | inl v => exact (restoreExceptionalFactor_ordinary_slots σ source id v).2
    | inr z =>
      refine ⟨.inl (source z),⟨z,rfl,rfl⟩,?_⟩
      rintro (x | w) h
      · obtain ⟨j,hx,he⟩ := h
        change j = z at he
        subst j
        exact congrArg Sum.inl hx.symm
      · exact h.elim
  choose f hf hUnique using out
  let τ : Equiv.Perm (V ⊕ Z) := Equiv.ofBijective f ⟨by
    intro x y he
    obtain ⟨z,_,hz⟩ := inc (f x)
    exact (hz x (hf x)).trans (hz y (he.symm ▸ hf y)).symm,by
    intro y
    obtain ⟨x,hx,_⟩ := inc y
    exact ⟨x,(hUnique x y hx).symm⟩⟩
  exact ⟨τ,fun x y => ⟨fun h => (hUnique x y h).symm,fun h => h ▸ hf x⟩⟩

/-- All restored arcs belong to the original host if the retained
ordinary arcs and the two arcs of each expanded shortcut do. -/
theorem restoreExceptionalFactor_le {G : Digraph (V ⊕ Z)} (σ : Equiv.Perm V)
    (source : J ↪ V) (exceptional : J → Z)
    (hOrd : ∀ u, u ∉ Set.range source → G.Adj (.inl u) (.inl (σ u)))
    (hPaths : ∀ j, G.Adj (.inl (source j)) (.inr (exceptional j)) ∧
      G.Adj (.inr (exceptional j)) (.inl (σ (source j)))) :
    restoreExceptionalFactor σ source exceptional ≤ G := by
  rintro (u | z) (v | w) h
  · obtain ⟨rfl,hu⟩ := h
    exact hOrd u hu
  · obtain ⟨j,rfl,rfl⟩ := h
    exact (hPaths j).1
  · obtain ⟨j,rfl,rfl⟩ := h
    exact (hPaths j).2
  · exact h.elim

/-- Disjoint factors downstairs lift to disjoint sets of original
arcs when the incoming and outgoing exceptional arcs supplied by
the exceptional path systems are disjoint. -/
theorem restoreExceptionalFactor_disjoint (σ τ : Equiv.Perm V)
    (a : J ↪ V) (b : K ↪ V) (e : J → Z) (f : K → Z)
    (hOrd : ∀ x, σ x ≠ τ x)
    (hIn : ∀ j k, e j = f k → a j ≠ b k)
    (hOut : ∀ j k, e j = f k → σ (a j) ≠ τ (b k)) :
    Disjoint (restoreExceptionalFactor σ a e) (restoreExceptionalFactor τ b f) := by
  rw [disjoint_iff_inf_le]
  rintro (x | z) (y | w) ⟨h,h'⟩
  · exact hOrd x (h.1.trans h'.1.symm)
  · obtain ⟨j,hj,he⟩ := h
    obtain ⟨k,hk,hf⟩ := h'
    exact hIn j k (he.trans hf.symm) (hj.trans hk.symm)
  · obtain ⟨j,he,hj⟩ := h
    obtain ⟨k,hf,hk⟩ := h'
    exact hOut j k (he.trans hf.symm) (hj.trans hk.symm)
  · exact h

end OverfullWork.DirectedRobustExpansion
