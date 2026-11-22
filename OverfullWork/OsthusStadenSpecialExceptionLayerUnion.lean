module

public import OverfullWork.OsthusStadenCoreExceptionLayerUnion
public import OverfullWork.OsthusStadenSpecialExceptionOccurrences

@[expose] public section


/-! Adjoin the layer-specific exceptional arcs after the bridges and the core. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- The three exceptional families cover the complement of the same
trimmed ordinary cells used in the physical layer. -/
theorem exceptional_cover_of_trimmed_cells {V U L : Type*} [Fintype V] [Fintype U]
    (core : Finset V) (cell : L → U → Finset V) (erase : L → U → V)
    (bridges : L → Finset V) (j : L) :
    let ordinary := univ.biUnion (fun u => (cell j u).erase (erase j u))
    Disjoint core ordinary → Disjoint (bridges j) ordinary →
      core ∪ bridges j ∪ specialExceptions core cell erase bridges j = ordinaryᶜ := by
  intro ordinary hCore hBridge
  apply subset_antisymm
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hx with hx | hx
      · exact mem_compl.mpr (disjoint_left.mp hCore hx)
      · exact mem_compl.mpr (disjoint_left.mp hBridge hx)
    · exact (mem_sdiff.mp hx).1
  · intro x hx
    by_cases h : x ∈ core ∪ bridges j
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hx,h⟩)

/-- The two contributions to the ordinary endpoint bound in (Red3)
sum after adjoining an exceptional arc family. -/
theorem exceptional_profile_sup_le {V : Type*} [Fintype V] (D E : Digraph V)
    (s : Bool) (Z : Finset V) (x : V) :
    let profile := fun H => if s then outProfile H x else inProfile H x
    profileCount Z (profile (D ⊔ E)) ≤ profileCount Z (profile D)+profileCount Z (profile E) := by
  intro profile
  have he : Z ∩ profile (D ⊔ E) = (Z ∩ profile D) ∪ (Z ∩ profile E) := by
    ext v
    cases s <;>
      simp [profile,inProfile,outProfile,and_or_left]
  unfold profileCount
  rw [he]
  exact_mod_cast card_union_le _ _

/-- When adding the special exceptions, their arcs may meet different
exceptional sets in different layers. Disjointness across the two
families is ensured by their physical reserves. Within a layer the
new arcs leave the ordinary pairs and all previous exceptional degrees intact. -/
theorem adjoin_exact_special_exception_arcs {V L : Type*} [Fintype V]
    (G : Digraph V) (Z ordinary : L → Finset V) (old special : L → Digraph V) (κ : ℕ)
    (hOld : ∀ j, old j ≤ G) (hSpecial : ∀ j, special j ≤ G)
    (hDisOld : ∀ j k, j ≠ k → Disjoint (old j) (old k))
    (hDisSpecial : ∀ j k, j ≠ k → Disjoint (special j) (special k))
    (hDisMixed : ∀ j k, Disjoint (old j) (special k))
    (hZ : ∀ j, Disjoint (Z j) (ordinary j))
    (hAvoid : ∀ j x y, (old j).Adj x y → x ∉ Z j ∧ y ∉ Z j)
    (hSupport : ∀ j x y, (special j).Adj x y →
      (x ∈ Z j ∧ y ∈ ordinary j) ∨ (y ∈ Z j ∧ x ∈ ordinary j))
    (hInd : ∀ j x y, x ∉ ordinary j → y ∉ ordinary j → ¬ (old j).Adj x y)
    (hOldExact : ∀ j x, x ∉ ordinary j → x ∉ Z j → inDegree (old j) x = κ ∧ outDegree (old j) x = κ)
    (hExact : ∀ j x, x ∈ Z j → inDegree (special j) x = κ ∧ outDegree (special j) x = κ) :
    let G' := fun j => old j ⊔ special j
    (∀ j, G' j ≤ G) ∧ (∀ j k, j ≠ k → Disjoint (G' j) (G' k)) ∧
    (∀ j x, x ∉ ordinary j → inDegree (G' j) x = κ ∧ outDegree (G' j) x = κ) ∧
    (∀ j, ∀ x ∈ ordinary j, ∀ y ∈ ordinary j, (G' j).Adj x y ↔ (old j).Adj x y) ∧
    ∀ j x y, x ∉ ordinary j → y ∉ ordinary j → ¬ (G' j).Adj x y := by
  intro G'
  have hLocal (j : L) := adjoin_exact_core_exception_arcs G (Z j)
    (fun _ : Unit => ordinary j) (fun _ => old j) (fun _ => special j) κ
    (fun _ => hOld j) (fun _ => hSpecial j)
    (fun u v h => (h (Subsingleton.elim u v)).elim)
    (fun u v h => (h (Subsingleton.elim u v)).elim)
    (fun _ => hZ j) (fun _ => hAvoid j) (fun _ => hSupport j) (fun _ => hInd j) (fun _ => hExact j)
  refine ⟨fun j => sup_le (hOld j) (hSpecial j),?_,?_,?_,?_⟩
  · intro j k hne
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hj,hk⟩
    rcases hj with hj | hj <;> rcases hk with hk | hk
    · exact disjoint_iff_inf_le.mp (hDisOld j k hne) ⟨hj,hk⟩
    · exact disjoint_iff_inf_le.mp (hDisMixed j k) ⟨hj,hk⟩
    · exact disjoint_iff_inf_le.mp (hDisMixed k j).symm ⟨hj,hk⟩
    · exact disjoint_iff_inf_le.mp (hDisSpecial j k hne) ⟨hj,hk⟩
  · intro j x hx
    obtain ⟨_,_,hNew,hKeep,_,_⟩ := hLocal j
    by_cases hxZ : x ∈ Z j
    · exact hNew () x hxZ
    · have h := hOldExact j x hx hxZ
      have hk := hKeep () x hxZ hx
      exact ⟨hk.1.trans h.1,hk.2.trans h.2⟩
  · intro j x hx y hy
    exact (hLocal j).2.2.2.2.1 () x hx y hy
  · intro j x y hx hy
    exact (hLocal j).2.2.2.2.2 () x y hx hy

end OverfullWork.DirectedRobustExpansion
