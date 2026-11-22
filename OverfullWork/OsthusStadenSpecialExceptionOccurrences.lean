module

public import OverfullWork.OsthusStadenRequestSplit
public import OverfullWork.OsthusStadenUnwoundPrimarySlices

@[expose] public section


/-! Count the actual special exceptions after unwinding and bridge deletions. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

/-- Special exceptions are the vertices outside the retained ordinary cells,
excluding the core and the bridge vertices of this layer. -/
noncomputable def specialExceptions {V U L : Type*} [Fintype V] [Fintype U]
    (core : Finset V) (cell : L → U → Finset V) (erase : L → U → V)
    (bridges : L → Finset V) (j : L) : Finset V :=
  (univ.biUnion (fun u => (cell j u).erase (erase j u)))ᶜ \ (core ∪ bridges j)

/-- The special exceptional set can grow by at most one vertex per
p-cell relative to the original type. Core and bridge vertices are omitted. -/
theorem special_exception_size_on_trimmed_layers
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero s] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ η d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) s p m τ τ τ}
    (A : UnwoundPrimarySlices G thin E g σ τ η d R) (core : Finset V)
    (erase : RefinedFactorIndex r s p → RefinedVertex I s p → V)
    (bridges : RefinedFactorIndex r s p → Finset V) (j : RefinedFactorIndex r s p) :
    (specialExceptions core (fun k => primaryPCells (R k.1)) erase bridges j).card ≤
      ((exceptional (g j.1)) \ core).card+Fintype.card (RefinedVertex I s p) := by
  let erased := (univ : Finset (RefinedVertex I s p)).image (erase j)
  have hSub : specialExceptions core (fun k => primaryPCells (R k.1)) erase bridges j ⊆
      (exceptional (g j.1) \ core) ∪ erased := by
    intro x hx
    obtain ⟨hOutside,hExc⟩ := mem_sdiff.mp hx
    cases hTag : A.label j.1 x with
    | none =>
      have hg := (A.label_exceptional j.1 x).mp hTag
      exact mem_union_left _ (mem_sdiff.mpr ⟨(mem_exceptional (g j.1) x).mpr hg,
        fun h => hExc (mem_union_left _ h)⟩)
    | some u =>
      have hHere := (A.label_cell j.1 x u).mp hTag
      have he : x = erase j u := Classical.byContradiction fun h =>
        (mem_compl.mp hOutside) (mem_biUnion.mpr ⟨u,mem_univ _,mem_erase.mpr ⟨h,hHere⟩⟩)
      exact mem_union_right _ (mem_image.mpr ⟨u,mem_univ _,he.symm⟩)
  have hEraseSize : erased.card ≤ Fintype.card (RefinedVertex I s p) := by
    simpa only [erased,card_univ] using
      (card_image_le (f := erase j) (s := (univ : Finset (RefinedVertex I s p))))
  exact (card_le_card hSub).trans ((card_union_le _ _).trans (Nat.add_le_add_left hEraseSize _))

/-- An exceptional vertex either comes from an affected original type or was
deleted in this layer. Global injectivity of the deletions charges the latter
at most once. The bridge vertices themselves are excluded by `specialExceptions`. -/
theorem special_exception_occurrences_on_trimmed_layers
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero s] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ η d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) s p m τ τ τ}
    (A : UnwoundPrimarySlices G thin E g σ τ η d R) (core : Finset V)
    (erase : RefinedFactorIndex r s p → RefinedVertex I s p → V)
    (bridges : RefinedFactorIndex r s p → Finset V)
    (hFresh : Function.Injective (fun q : RefinedFactorIndex r s p × RefinedVertex I s p => erase q.1 q.2))
    (cap : ℕ) (hTypes : ∀ x ∉ core, ((univ : Finset (Fin r)).filter (fun t => g t x = none)).card ≤ cap)
    (x : V) :
    let Z := specialExceptions core (fun j => primaryPCells (R j.1)) erase bridges
    ((univ : Finset (RefinedFactorIndex r s p)).filter (fun j => x ∈ Z j)).card ≤ cap*((s-1)*(p-1))+1 := by
  intro Z
  by_cases hx : x ∈ core
  · have he : ((univ : Finset (RefinedFactorIndex r s p)).filter (fun j => x ∈ Z j)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact (mem_sdiff.mp (mem_filter.mp hj).2).2 (mem_union_left _ hx)
    rw [he,card_empty]
    exact Nat.zero_le _
  let types := (univ : Finset (Fin r)).filter (fun t => g t x = none)
  let compensating := (univ : Finset (RefinedFactorIndex r s p)).filter (fun j => ∃ u, erase j u = x)
  have hComp : compensating.card ≤ 1 := card_le_one.mpr (by
    intro j hj k hk
    obtain ⟨u,hu⟩ := (mem_filter.mp hj).2
    obtain ⟨v,hv⟩ := (mem_filter.mp hk).2
    have h : (j,u) = (k,v) := hFresh (hu.trans hv.symm)
    exact congrArg Prod.fst h)
  have hSub (j : RefinedFactorIndex r s p) (hj : x ∈ Z j) : j.1 ∈ types ∨ j ∈ compensating := by
    cases hLabel : A.label j.1 x with
    | none => exact Or.inl (mem_filter.mpr ⟨mem_univ _,(A.label_exceptional j.1 x).mp hLabel⟩)
    | some u =>
      right
      have hCell := (A.label_cell j.1 x u).mp hLabel
      have hOrd := mem_compl.mp (mem_sdiff.mp hj).1
      have he : x = erase j u := Classical.byContradiction fun h =>
        hOrd (mem_biUnion.mpr ⟨u,mem_univ _,mem_erase.mpr ⟨h,hCell⟩⟩)
      exact mem_filter.mpr ⟨mem_univ _,u,he.symm⟩
  have h := exceptional_slice_occurrences_le types compensating (univ.filter (fun j => x ∈ Z j))
    hComp (fun j hj => hSub j (mem_filter.mp hj).2)
  simp only [UnwindingLabel,count_unwinding_increments] at h
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hTypes x hx)) _)

end OverfullWork.DirectedRobustExpansion
