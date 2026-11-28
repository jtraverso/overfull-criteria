module

public import OverfullWork.ChenShanPaletteCompletion
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset SimpleGraph MultiGraph.GeneralCopies
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Properties of the recolored matchings used after §5.1.4.
The mass bounds the degree sum on one side before recoloring. -/
structure PaletteMatchingBounds {G : MultiGraph V} {k : ℕ}
    (D : G.EdgeColoring k) (A B : Finset V) (mass : ℕ) : Prop where
  balanced : ∀ j, sideCount D A j = sideCount D B j
  covers : ∀ v ∈ (A ∪ B)ᶜ, ∀ j, (D.colourGraph j).degree v = 1
  core_bound : ∀ j, (sideCount D A j : ℝ) + (sideCount D B j : ℝ) ≤ 2*(mass : ℝ)/k + 4

omit [Fintype V] in
private theorem core_role_iff (role : V → PaletteVertexRole) (A B : Finset V)
    (hA : ∀ v, role v = .coreA ↔ v ∈ A) (hB : ∀ v, role v = .coreB ↔ v ∈ B) (v : V) :
    (role v).isCore = true ↔ v ∈ A ∪ B := by
  rw [mem_union, ← hA v, ← hB v]
  cases role v <;> decide

private theorem paletteCopySubgraph_degree_le (M : MultiGraph V) (T : Finset (Copies M)) (v : V) :
    (paletteCopySubgraph M T).degree v ≤ M.degree v := by
  unfold MultiGraph.degree
  exact sum_le_sum fun e _ => paletteCopySubgraph_mult_le M T e

/-- Recolor the selected blocks, proving (5.9) and retaining their
support off the boundary. The unselected copies are recolored as well. -/
theorem exists_palette_matchings_of_completed_selection
    {I : Type*} [Fintype I] {k : ℕ}
    (M : MultiGraph V) (A B boundaryVertices : Finset V)
    (role : V → PaletteVertexRole) (colour : Copies M → Fin k)
    (block : I → Finset V) (P : I → Finset (Fin k))
    (available core : I → Finset (Copies M)) (a : ℕ) (blockSize : I → ℕ)
    (hA : ∀ v, role v = .coreA ↔ v ∈ A) (hB : ∀ v, role v = .coreB ↔ v ∈ B)
    (hAB : Disjoint A B) (hEven : Even ((A ∪ B)ᶜ.card))
    (hProper : ∀ v, Set.InjOn colour {d | v ∈ d.1})
    (hCovered : ∀ v ∈ (A ∪ B)ᶜ, ∀ j, ∃ d, v ∈ d.1 ∧ colour d = j)
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, M.degree v = k)
    (hBalance : (∑ v ∈ A, M.degree v) = ∑ v ∈ B, M.degree v)
    (hCore : ∀ v ∈ A ∪ B, M.degree v ≤ a)
    (hPalettes : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hSize : ∀ i, 2*a < (P i).card)
    (hRemSize : 2*a + ∑ i, (P i).card < k)
    (hRemRow : ∀ v, (role v).preferredSign ≠ 0 →
      2*a + ∑ i, (P i).card < M.degreeInto (A ∪ B) v)
    (hBlockSize : ∀ i, (A ∩ block i).card ≤ blockSize i)
    (hAvoid : ∀ i d, d ∈ available i →
      ((ends M d).1 ∈ A ∪ B → (ends M d).1 ∉ boundaryVertices) ∧
      ((ends M d).2 ∈ A ∪ B → (ends M d).2 ∉ boundaryVertices)) :
    let original i := univ.filter (fun d => colour d ∈ P i)
    let S i := paletteSelectedCopies (ends M) role (original i) (core i)
    (∀ i, IsPaletteBlockSelection (ends M) role (block i) (original i) (available i) (core i)) →
    (∀ i d, d ∈ original i → (role (ends M d).1).isLowCore (role (ends M d).2) = false) →
    (∀ i v, (role v).preferredSign ≠ 0 → 2*a < (paletteCoreRow (ends M) role (original i) v).card) →
    Pairwise (fun i j => Disjoint (S i) (S j)) →
    (∀ i, ∃ D : (paletteCopySubgraph M (S i)).EdgeColoring (P i).card,
      PaletteMatchingBounds D A B (blockSize i*a) ∧
      ∀ v ∈ A ∪ B, v ∉ block i \ boundaryVertices → ∀ j, (D.colourGraph j).degree v = 0) ∧
    ∃ D : (paletteCopySubgraph M (univ \ univ.biUnion S)).EdgeColoring (k - ∑ i, (P i).card),
      PaletteMatchingBounds D A B (A.card*a) := by
  classical
  intro original S hSel hLow hRows hDisj
  have hRole := core_role_iff role A B hA hB
  have hTrimmed (i : I) :
      IsPaletteBlockSelection (ends M) role (block i \ boundaryVertices)
        (original i) (available i) (core i) := by
    refine { hSel i with in_block := ?_ }
    intro d hd
    obtain ⟨hAny, hFirst, hSecond⟩ := (hSel i).in_block d hd
    obtain ⟨hAvoidFirst, hAvoidSecond⟩ := hAvoid i d ((hSel i).available_copies hd)
    exact ⟨hAny, fun h => mem_sdiff.mpr ⟨hFirst h, hAvoidFirst ((hRole _).mp h)⟩,
      fun h => mem_sdiff.mpr ⟨hSecond h, hAvoidSecond ((hRole _).mp h)⟩⟩
  have hZero (i : I) (v : V) (hv : v ∈ A ∪ B) (hOut : v ∉ block i \ boundaryVertices) :
      (paletteCopySubgraph M (S i)).degree v = 0 :=
    paletteCopySubgraph_degree_zero_outside_block M role _ _ _ _ (hTrimmed i) v
      ((hRole v).mpr hv) hOut
  have hSatBal (i : I) := paletteCopySubgraph_saturated_and_balanced_of_selection M role A B
    (block i) (P i) colour (available i) (core i) hA hB hProper
    (fun v hv j _ => hCovered v hv j) (hSel i)
  have hMass (i : I) : (∑ v ∈ A, (paletteCopySubgraph M (S i)).degree v) ≤ blockSize i*a := by
    apply paletteCoreDegreeSum_le_of_supported _ A (block i) a (blockSize i) _ _ (hBlockSize i)
    · exact fun v hv hOut => hZero i v (mem_union_left _ hv) (hOut ∘ fun h => (mem_sdiff.mp h).1)
    · intro v hv
      exact (paletteCopySubgraph_degree_le M _ v).trans (hCore v (mem_union_left _ (mem_inter.mp hv).1))
  have hRemMass : (∑ v ∈ A, (paletteCopySubgraph M (univ \ univ.biUnion S)).degree v) ≤ A.card*a := by
    calc
      _ ≤ ∑ _v ∈ A, a := sum_le_sum fun v hv =>
        (paletteCopySubgraph_degree_le M _ v).trans (hCore v (mem_union_left _ hv))
      _ = _ := by simp
  obtain ⟨hC, hR⟩ := palette_partition_colourable_of_original_row_bounds M A B role colour block P
    available core a hA hB hProper hCovered hSat hCore hPalettes hSize hRemSize hRemRow
    hSel hLow hRows hDisj
  obtain ⟨hBlocks, D, hD⟩ := exists_balanced_palette_partition_recolorings M S A B k
    (fun i => (P i).card) (fun i => blockSize i*a) (A.card*a) hDisj hAB hEven
    (fun i => by have := hSize i; omega) (by omega) hSat hBalance
    (fun i => (hSatBal i).1) (fun i => (hSatBal i).2) hMass hRemMass hC hR
  refine ⟨fun i => ?_, D, hD.1, hD.2.1, hD.2.2⟩
  obtain ⟨D, hBal, hCov, hBound⟩ := hBlocks i
  refine ⟨D, ⟨hBal, hCov, hBound⟩, fun v hv hOut j => ?_⟩
  have hSum := sum_colour_degrees_at_vertex D v
  rw [hZero i v hv hOut] at hSum
  exact Nat.eq_zero_of_le_zero ((single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)).trans_eq hSum)

/-- Count all the color classes, including the remainder, that meet a
vertex. Since each color is a matching, its contribution is zero or one. -/
theorem palette_partition_total_colour_degrees
    {I : Type*} [Fintype I] (M : MultiGraph V) (S : I → Finset (Copies M))
    (hDisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (size : I → ℕ) (r : ℕ)
    (D : ∀ i, (paletteCopySubgraph M (S i)).EdgeColoring (size i))
    (R : (paletteCopySubgraph M (univ \ univ.biUnion S)).EdgeColoring r) (v : V) :
    (∑ j, (R.colourGraph j).degree v) + ∑ i, ∑ j, ((D i).colourGraph j).degree v = M.degree v := by
  rw [sum_colour_degrees_at_vertex R v]
  simp_rw [sum_colour_degrees_at_vertex (D _) v]
  exact paletteCopySubgraph_degree_add_sum_complement M S hDisjoint v

-- Match the copy-set operations in the abstract selection theorem.
noncomputable local instance (priority := high) {M : MultiGraph V} : DecidableEq (Copies M) := Classical.decEq _

/-- Chen–Shan §5.1.4, from the sampled bounds to the selected matching
families and the matching family of the remainder. Both stages use
the same indexed copies of the ambient residual multigraph. -/
theorem exists_palette_matchings_of_sampled_bounds
    {F C : Type*} [Fintype F] [Fintype C] {k : ℕ}
    (M : MultiGraph V) (A B boundaryVertices : Finset V)
    (role : V → PaletteVertexRole) (colour : Copies M → Fin k)
    (block : F ⊕ C → Finset V) (palette : F ⊕ C → Finset (Fin k))
    (source : V → Finset (Copies M)) (boundary : Finset (Copies M))
    (special : V → Bool) (c : V → ℝ)
    (β theta p₁ p₂ lambda₁ lambda₂ : ℝ) (k₁ a : ℕ) (blockSize : F ⊕ C → ℕ)
    (hA : ∀ v, role v = .coreA ↔ v ∈ A) (hB : ∀ v, role v = .coreB ↔ v ∈ B)
    (hAB : Disjoint A B) (hEven : Even ((A ∪ B)ᶜ.card))
    (hProper : ∀ v, Set.InjOn colour {d | v ∈ d.1})
    (hCovered : ∀ v ∈ (A ∪ B)ᶜ, ∀ j, ∃ d, v ∈ d.1 ∧ colour d = j)
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, M.degree v = k)
    (hBalance : (∑ v ∈ A, M.degree v) = ∑ v ∈ B, M.degree v)
    (hColoursBalanced : ∀ P : Finset (Fin k),
      paletteCopyCoreGap (ends M) role (univ.filter (fun d => colour d ∈ P)) = 0)
    (hCore : ∀ v ∈ A ∪ B, M.degree v ≤ a)
    (hβ : 0 ≤ β) (hβOne : β ≤ 1) (hThetaNonneg : 0 ≤ theta) (hTheta : theta ≤ 1)
    (hp₁ : 0 < p₁) (hOrder : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1)
    (hl₁ : 0 ≤ lambda₁) (hl₂ : 0 ≤ lambda₂) (hc : ∀ v, 0 ≤ c v)
    (hFineBlock : Pairwise (fun f g : F => Disjoint (block (.inl f)) (block (.inl g))))
    (hCoarseBlock : Pairwise (fun f g : C => Disjoint (block (.inr f)) (block (.inr g))))
    (hPalettes : Pairwise (fun f g => Disjoint (palette f) (palette g)))
    (hFineSize : ∀ f : F, (palette (.inl f)).card ≤ k₁)
    (hFineCost : ∀ v, (role v).preferredSign ≠ 0 → ((Fintype.card F*k₁:ℕ):ℝ) ≤ β*p₂*c v/400)
    (hCoarseBudget : (5/4:ℝ)*(Fintype.card F:ℝ)*lambda₁ ≤ p₂^2/1024)
    (hBlockSize : ∀ i, (A ∩ block i).card ≤ blockSize i)
    (hBoundaryCopies : ∀ d : Copies M,
      ((ends M d).1 ∈ boundaryVertices ∨ (ends M d).2 ∈ boundaryVertices) → d ∈ boundary)
    (hTotal : (∑ i, ((palette i).card:ℝ)) ≤ β*theta*k/400)
    (hActive : ∀ v, (role v).preferredSign ≠ 0 →
      theta*k ≤ c v ∧ c v = (M.degreeInto (A ∪ B) v : ℝ))
    (hSmall : ∀ i, 2*(a:ℝ) < (15/16:ℝ)*theta*(palette i).card)
    (hRemSmall : 2*(a:ℝ) < (399/400:ℝ)*theta*k) :
    let p : F ⊕ C → ℝ := Sum.elim (fun _ => p₁) (fun _ => p₂)
    let lambda : F ⊕ C → ℝ := Sum.elim (fun _ => lambda₁) (fun _ => lambda₂)
    let edgeEnds := ends M
    let original (b : F ⊕ C) := (univ : Finset (Copies M)).filter (fun d => colour d ∈ palette b)
    let E (side : Bool) := paletteSideCopies edgeEnds role univ side
    (∀ i, lambda i*k = ((palette i).card:ℝ)) →
    (∀ b, lambda b ≤ β*(p b)^2*theta/(2:ℝ)^18) →
    (∀ b d, d ∈ original b → (role (edgeEnds d).1).isLowCore (role (edgeEnds d).2) = false) →
    (∀ b v, (role v).preferredSign ≠ 0 →
      (15/16:ℝ)*lambda b*c v ≤ ((paletteCoreRow edgeEnds role (original b) v).card:ℝ) ∧
      ((paletteCoreRow edgeEnds role (original b) v).card:ℝ) ≤ 2*lambda b*c v) →
    (∀ b side, ((paletteSideCopies edgeEnds role (original b) side).card:ℝ) ≤
      (5/4:ℝ)*lambda b*(E side).card) →
    (∀ side, ((boundary ∩ E side).card:ℝ) ≤ p₁^2*((E side).card:ℝ)/512 ∧
      ((boundary ∩ E side).card:ℝ) ≤ p₂^2*((E side).card:ℝ)/1024) →
    (∀ b side,
      (paletteSideCopies edgeEnds role (original b) (!side)).card <
        (paletteSideCopies edgeEnds role (original b) side).card →
      let S := availableCorrectionCopies edgeEnds role (block b) univ side
      (13/8:ℝ)*lambda b*(E side).card ≤
        (64*lambda b/(p b)^2)*(internalCorrectionCopies edgeEnds role S).card +
        ∑ v ∈ univ.filter (fun v => (role v).isCore = false),
          min ((64*lambda b/(p b))*(paletteCoreRow edgeEnds role S v).card)
            (paletteExceptionalCap role c (lambda b) v)) →
    (∀ b v, (role v).preferredSign ≠ 0 →
      let S := availablePreferredCopies edgeEnds role (block b) univ source v
      (if special v then p b*c v/3 else β*p b*c v/8) ≤ (S.card:ℝ) ∧
      ((S ∩ boundary).card:ℝ) ≤ (if special v then p₁*c v/12 else β*p₁*c v/32)) →

    ∃ S : F ⊕ C → Finset (Copies M),
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (∀ i, ∃ D : (paletteCopySubgraph M (S i)).EdgeColoring (palette i).card,
        PaletteMatchingBounds D A B (blockSize i*a) ∧
        ∀ v ∈ A ∪ B, v ∉ block i \ boundaryVertices → ∀ j, (D.colourGraph j).degree v = 0) ∧
      ∃ D : (paletteCopySubgraph M (univ \ univ.biUnion S)).EdgeColoring
          (k - ∑ i, (palette i).card),
        PaletteMatchingBounds D A B (A.card*a) := by
  classical
  intro p lambda edgeEnds original E hRatio hLambda hLow hIncidence hCount hBoundary hInitial hPref
  have hWhole : paletteCopyCoreGap edgeEnds role (univ : Finset (Copies M)) = 0 := by
    simpa only [mem_univ, filter_true] using hColoursBalanced univ
  have hLabelProper (v : V) : Set.InjOn colour {d | (edgeEnds d).1 = v ∨ (edgeEnds d).2 = v} :=
    fun d hd e he h => hProper v ((incident_iff M d v).mp hd) ((incident_iff M e v).mp he) h
  obtain ⟨fine, coarse, hFine, hCoarse, hDisjoint, _⟩ :=
    exists_staged_palette_selections_of_sampled_bounds edgeEnds role colour block palette
      source boundary special c β theta p₁ p₂ lambda₁ lambda₂ k₁ hβ hβOne hTheta
      hp₁ hOrder hp₂ hl₁ hl₂ hc hFineBlock hCoarseBlock hPalettes hWhole hLabelProper hFineSize
      hFineCost hCoarseBudget hLambda (fun i => hColoursBalanced (palette i)) hLow
      hIncidence hCount hBoundary hInitial hPref
  let core : F ⊕ C → Finset (Copies M) := Sum.elim fine coarse
  let available : F ⊕ C → Finset (Copies M) := Sum.elim (fun _ => univ \ boundary)
    (fun _ => (univ \ boundary) \ univ.biUnion fine)
  have hSel (i : F ⊕ C) :
      IsPaletteBlockSelection edgeEnds role (block i) (original i) (available i) (core i) := by
    cases i with
    | inl f => exact hFine f
    | inr g => exact hCoarse g
  have hAvoid (i : F ⊕ C) (d : Copies M) (hd : d ∈ available i) :
      ((edgeEnds d).1 ∈ A ∪ B → (edgeEnds d).1 ∉ boundaryVertices) ∧
      ((edgeEnds d).2 ∈ A ∪ B → (edgeEnds d).2 ∉ boundaryVertices) := by
    have hn : d ∉ boundary := by
      cases i <;> simp only [available, Sum.elim_inl, Sum.elim_inr, mem_sdiff] at hd
      · exact hd.2
      · exact hd.1.2
    exact ⟨fun _ h => hn (hBoundaryCopies d (Or.inl h)), fun _ h => hn (hBoundaryCopies d (Or.inr h))⟩
  have hSize (i : F ⊕ C) : 2*a < (palette i).card := by
    have h := hSmall i
    have hMul := mul_le_mul_of_nonneg_right hTheta (Nat.cast_nonneg (α := ℝ) (palette i).card)
    exact_mod_cast (show 2*(a:ℝ) < ((palette i).card:ℝ) by linarith)
  have hSum : (∑ i, ((palette i).card:ℝ)) ≤ theta*k/400 := by
    have h := mul_le_mul_of_nonneg_right hβOne (mul_nonneg hThetaNonneg (Nat.cast_nonneg (α := ℝ) k))
    calc
      _ ≤ β*theta*k/400 := hTotal
      _ ≤ _ := by nlinarith
  have hRem : 2*(a:ℝ) + (∑ i, ((palette i).card:ℝ)) < theta*k := by
    linarith only [hSum, hRemSmall]
  have hRemSize : 2*a + ∑ i, (palette i).card < k := by
    have h := mul_le_mul_of_nonneg_right hTheta (Nat.cast_nonneg (α := ℝ) k)
    have hK : 2*(a:ℝ) + (∑ i, ((palette i).card:ℝ)) < (k:ℝ) :=
      hRem.trans_le (by simpa using h)
    exact_mod_cast hK
  have hRemRow (v : V) (hv : (role v).preferredSign ≠ 0) :
      2*a + ∑ i, (palette i).card < M.degreeInto (A ∪ B) v := by
    have h := hRem.trans_le (hActive v hv).1
    rw [(hActive v hv).2] at h
    exact_mod_cast h
  have hRows (i : F ⊕ C) (v : V) (hv : (role v).preferredSign ≠ 0) :
      2*a < (paletteCoreRow edgeEnds role (original i) v).card := by
    have hLambdaNonneg : 0 ≤ lambda i := by cases i <;> assumption
    have h := mul_le_mul_of_nonneg_left (hActive v hv).1 (show 0 ≤ (15/16:ℝ)*lambda i by positivity)
    have hLower : (15/16:ℝ)*theta*(palette i).card ≤ (15/16:ℝ)*lambda i*c v := by
      rw [← hRatio i]
      nlinarith only [h]
    exact_mod_cast (hSmall i).trans_le (hLower.trans (hIncidence i v hv).1)
  let S (i : F ⊕ C) := paletteSelectedCopies edgeEnds role (original i) (core i)
  refine ⟨S, hDisjoint, ?_⟩
  obtain ⟨hBlocks, hRest⟩ := exists_palette_matchings_of_completed_selection M A B boundaryVertices
    role colour block palette available core a blockSize hA hB hAB hEven hProper hCovered hSat
    hBalance hCore hPalettes hSize hRemSize hRemRow hBlockSize hAvoid hSel hLow hRows hDisjoint
  refine ⟨hBlocks, ?_⟩
  let remaining : Finset (Copies M) :=
    letI : DecidableEq (Copies M) := Sigma.instDecidableEqSigma
    univ \ univ.biUnion S
  have hEq : (univ \ univ.biUnion S) = remaining := by
    ext d
    simp [remaining]
  rw [hEq]
  exact hRest

end OverfullWork.ChenShan
