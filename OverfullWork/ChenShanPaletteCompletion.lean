module

public import OverfullWork.ChenShanPaletteRecolouring
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset SimpleGraph MultiGraph.GeneralCopies
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem retained_copy_roles (u v : PaletteVertexRole)
    (hCore : ¬ (u.isCore = true ∧ v.isCore = true))
    (hFirst : ¬ (u.preferredSign ≠ 0 ∧ v.isCore = true))
    (hSecond : ¬ (v.preferredSign ≠ 0 ∧ u.isCore = true)) :
    (u.isCore = false ∧ v.isCore = false) ∨ u.isLowCore v = true := by
  cases u <;> cases v <;>
    simp_all [PaletteVertexRole.isCore, PaletteVertexRole.preferredSign, PaletteVertexRole.isLowCore]

/-- Complete the selected palettes and the complement in §5.1.4.
The input estimates are on the original labels and on the ambient
core degrees, before the selected copies have been removed. -/
theorem palette_partition_colourable_of_original_row_bounds
    {I : Type*} [Fintype I] {k : ℕ} (M : MultiGraph V) (A B : Finset V)
    (role : V → PaletteVertexRole) (colour : Copies M → Fin k)
    (block : I → Finset V) (P : I → Finset (Fin k))
    (available core : I → Finset (Copies M)) (a : ℕ)
    (hA : ∀ v, role v = .coreA ↔ v ∈ A) (hB : ∀ v, role v = .coreB ↔ v ∈ B)
    (hProper : ∀ v, Set.InjOn colour {d | v ∈ d.1})
    (hCovered : ∀ v ∈ (A ∪ B)ᶜ, ∀ j, ∃ d, v ∈ d.1 ∧ colour d = j)
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, M.degree v = k)
    (hCore : ∀ v ∈ A ∪ B, M.degree v ≤ a)
    (hPalettes : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hSize : ∀ i, 2*a < (P i).card)
    (hRemSize : 2*a + ∑ i, (P i).card < k)
    (hRemRow : ∀ v, (role v).preferredSign ≠ 0 →
      2*a + ∑ i, (P i).card < M.degreeInto (A ∪ B) v) :
    let original i := univ.filter (fun d => colour d ∈ P i)
    let S i := paletteSelectedCopies (ends M) role (original i) (core i)
    (∀ i, IsPaletteBlockSelection (ends M) role (block i) (original i) (available i) (core i)) →
    (∀ i d, d ∈ original i → (role (ends M d).1).isLowCore (role (ends M d).2) = false) →
    (∀ i v, (role v).preferredSign ≠ 0 → 2*a < (paletteCoreRow (ends M) role (original i) v).card) →
    Pairwise (fun i j => Disjoint (S i) (S j)) →
    (∀ i, Nonempty ((paletteCopySubgraph M (S i)).EdgeColoring (P i).card)) ∧
    Nonempty ((paletteCopySubgraph M (univ \ univ.biUnion S)).EdgeColoring
      (k - ∑ i, (P i).card)) := by
  classical
  intro original S hSel hOriginalLow hRow hDisjoint
  let U := A ∪ B
  let active := univ.filter (fun v => (role v).preferredSign ≠ 0)
  let rem := (univ.biUnion P)ᶜ
  have hU (v : V) : (role v).isCore = true ↔ v ∈ U := by
    change (role v).isCore = true ↔ v ∈ A ∪ B
    rw [mem_union, ← hA v, ← hB v]
    cases role v <;> decide
  have hActive (v : V) : v ∈ active ↔ (role v).preferredSign ≠ 0 := by simp [active]
  have hNonCore (v : V) (hv : v ∈ active) : (role v).isCore = false := by
    have h := (hActive v).mp hv
    cases hRole : role v <;> simp_all [PaletteVertexRole.preferredSign, PaletteVertexRole.isCore]
  have hUA : Disjoint U active := by
    refine disjoint_left.mpr fun v hv ha => ?_
    have h := (hU v).mpr hv
    rw [hNonCore v ha] at h
    contradiction
  have hSmall (T : Finset (Copies M)) (v : V) (hv : v ∈ U) :
      (paletteCopySubgraph M T).degree v ≤ a := by
    unfold MultiGraph.degree
    exact (sum_le_sum fun e _ => paletteCopySubgraph_mult_le M T e).trans (hCore v hv)
  have hBlockSat (i : I) (v : V) (hv : v ∈ Uᶜ) :
      (paletteCopySubgraph M (S i)).degree v = (P i).card :=
    (paletteCopySubgraph_saturated_and_balanced_of_selection M role A B (block i) (P i)
      colour (available i) (core i) hA hB hProper (fun v hv j _ => hCovered v hv j) (hSel i)).1 v hv
  have hRemCard : rem.card = k - ∑ i, (P i).card := palette_complement_card P hPalettes
  have hProtected (d : Copies M) (h₁ : ¬ ((ends M d).1 ∈ U ∧ (ends M d).2 ∈ U))
      (h₂ : ¬ ((ends M d).1 ∈ active ∧ (ends M d).2 ∈ U))
      (h₃ : ¬ ((ends M d).2 ∈ active ∧ (ends M d).1 ∈ U)) :
      ((role (ends M d).1).isCore = false ∧ (role (ends M d).2).isCore = false) ∨
        (role (ends M d).1).isLowCore (role (ends M d).2) = true := by
    simp only [← hU, hActive] at h₁ h₂ h₃
    exact retained_copy_roles _ _ h₁ h₂ h₃
  constructor
  · intro i
    refine paletteCopySubgraph_colourable_of_retained_colors M (S i) (P i) colour U active a
      hUA (hSize i) ?_ (hSmall (S i)) ?_ hProper ?_
    · intro v
      by_cases hv : v ∈ U
      · exact (hSmall (S i) v hv).trans (by have := hSize i; omega)
      · exact (hBlockSat i v (mem_compl.mpr hv)).le
    · intro v hv
      rw [paletteCopySubgraph_degreeInto_eq_row M (S i) role U hU]
      have hEq : (paletteCoreRow (ends M) role (S i) v).card =
          (paletteCoreRow (ends M) role (original i) v).card := (hSel i).rows v (hNonCore v hv)
      rw [hEq]
      exact hRow i v ((hActive v).mp hv)
    · intro d hd h₁ h₂ h₃
      rcases hProtected d h₁ h₂ h₃ with hBoth | hLow
      · have hParts := hd
        simp only [S, paletteSelectedCopies, mem_union] at hParts
        rcases hParts with h | h
        · exact (mem_filter.mp (mem_filter.mp h).1).2
        · have hIn := ((hSel i).in_block d h).1
          simp [hBoth.1, hBoth.2] at hIn
      · rw [(hSel i).no_low_core d hd] at hLow
        contradiction
  · rw [← hRemCard]
    refine paletteCopySubgraph_colourable_of_retained_colors M _ rem colour U active a
      hUA (by rw [hRemCard]; omega) ?_ (hSmall _) ?_ hProper ?_
    · intro v
      by_cases hv : v ∈ U
      · exact (hSmall _ v hv).trans (by rw [hRemCard]; omega)
      · have hv' := mem_compl.mpr hv
        have hAccounting := paletteCopySubgraph_degree_add_sum_complement M S hDisjoint v
        simp_rw [hBlockSat _ v hv', hSat v hv'] at hAccounting
        rw [hRemCard]
        omega
    · intro v hv
      have hv' : v ∈ Uᶜ := mem_compl.mpr fun h => disjoint_left.mp hUA h hv
      have hAccounting := paletteCopySubgraph_degreeInto_complement_lower M S hDisjoint U v
        (fun i => (P i).card) (fun i => (hBlockSat i v hv').le)
      have hOriginal := hRemRow v ((hActive v).mp hv)
      change 2*a + ∑ i, (P i).card < M.degreeInto U v at hOriginal
      omega
    · intro d hd h₁ h₂ h₃
      simp only [rem, mem_compl, mem_biUnion, mem_univ, true_and]
      rintro ⟨i, hi⟩
      have hOriginal : d ∈ original i := mem_filter.mpr ⟨mem_univ _, hi⟩
      rcases hProtected d h₁ h₂ h₃ with hBoth | hLow
      · have hRetained : d ∈ paletteExceptionalCopies (ends M) role (original i) :=
          mem_filter.mpr ⟨hOriginal, by simp [hBoth.1, hBoth.2]⟩
        have hIn : d ∈ S i := by
          simp only [S, paletteSelectedCopies, mem_union]
          exact Or.inl hRetained
        exact (mem_sdiff.mp hd).2 (mem_biUnion.mpr ⟨i, mem_univ _, hIn⟩)
      · rw [hOriginalLow i d hOriginal] at hLow
        contradiction

/-- Every core vertex outside the assigned block, including any
boundary vertex omitted from the block, has degree zero in the
selected subgraph. -/
theorem paletteCopySubgraph_degree_zero_outside_block
    (M : MultiGraph V) (role : V → PaletteVertexRole) (block : Finset V)
    (original available core : Finset (Copies M))
    (hSel : IsPaletteBlockSelection (ends M) role block original available core)
    (v : V) (hCore : (role v).isCore = true) (hOutside : v ∉ block) :
    (paletteCopySubgraph M (paletteSelectedCopies (ends M) role original core)).degree v = 0 := by
  rw [paletteCopySubgraph_degree]
  unfold paletteCopyDegree
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro d hd
  simp only [mem_filter] at hd
  obtain ⟨hParts, hInc⟩ := hd
  simp only [paletteSelectedCopies, mem_union] at hParts
  rcases hParts with hExceptional | hNew
  · have hNeither : (role (ends M d).1).isCore = false ∧
        (role (ends M d).2).isCore = false := by
      simpa using (mem_filter.mp hExceptional).2
    rcases hInc with hEnd | hEnd
    · simpa [hEnd, hCore] using hNeither.1
    · simpa [hEnd, hCore] using hNeither.2
  · have hBlock := (hSel.in_block d hNew).2
    rcases hInc with hEnd | hEnd
    · exact hOutside (hEnd ▸ hBlock.1 (hEnd.symm ▸ hCore))
    · exact hOutside (hEnd ▸ hBlock.2 (hEnd.symm ▸ hCore))

end OverfullWork.ChenShan
