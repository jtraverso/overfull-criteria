module

public import OverfullWork.ChenShanPaletteAvailability
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V D K : Type*}

/-- Properness of the original coloring bounds each vertex's degree
in the union of the colors of a palette. -/
theorem paletteCopyDegree_filter_le_palette_card [Fintype D] [DecidableEq K]
    (ends : D → V × V) (colour : D → K)
    (hProper : ∀ v, Set.InjOn colour {d | (ends d).1 = v ∨ (ends d).2 = v})
    (palette : Finset K) (v : V) :
    paletteCopyDegree ends (univ.filter (fun d => colour d ∈ palette)) v ≤ palette.card := by
  classical
  let S := (univ.filter (fun d => colour d ∈ palette)).filter
    (fun d => (ends d).1 = v ∨ (ends d).2 = v)
  change S.card ≤ palette.card
  calc
    S.card = (S.image colour).card := (card_image_of_injOn
      (fun d hd e he h => hProper v (mem_filter.mp hd).2 (mem_filter.mp he).2 h)).symm
    _ ≤ palette.card := by
      apply card_le_card
      intro i hi
      obtain ⟨d,hd,rfl⟩ := mem_image.mp hi
      exact (mem_filter.mp (mem_filter.mp hd).1).2

private theorem exceptional_of_preferredSign_ne_zero (v : PaletteVertexRole) :
    v.preferredSign ≠ 0 → v.isCore = false := by
  cases v <;> decide

set_option maxHeartbeats 1200000 in
/-- Assemble the selection part of §5.1.4 from the sampled capacity
and preferred-edge estimates before deleting any copies. The coarse
availability follows from the actual fine selections and their budgets. -/
theorem exists_staged_palette_selections_of_sampled_bounds {F C : Type*}
    [Fintype F] [Fintype C] [Fintype D] [Fintype V] [DecidableEq K]
    (ends : D → V × V) (role : V → PaletteVertexRole) (colour : D → K)
    (block : F ⊕ C → Finset V) (palette : F ⊕ C → Finset K)
    (source : V → Finset D) (boundary : Finset D) (special : V → Bool) (c : V → ℝ)
    (β theta p₁ p₂ lambda₁ lambda₂ : ℝ) (k₁ : ℕ)
    (hβ : 0 ≤ β) (hβOne : β ≤ 1) (hTheta : theta ≤ 1)
    (hp₁ : 0 < p₁) (hOrder : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1)
    (hl₁ : 0 ≤ lambda₁) (hl₂ : 0 ≤ lambda₂) (hc : ∀ v, 0 ≤ c v)
    (hFineBlock : Pairwise (fun f g : F => Disjoint (block (.inl f)) (block (.inl g))))
    (hCoarseBlock : Pairwise (fun f g : C => Disjoint (block (.inr f)) (block (.inr g))))
    (hPalettes : Pairwise (fun f g => Disjoint (palette f) (palette g)))
    (hWhole : paletteCopyCoreGap ends role (univ : Finset D) = 0)
    (hProper : ∀ v, Set.InjOn colour {d | (ends d).1 = v ∨ (ends d).2 = v})
    (hFineSize : ∀ f : F, (palette (.inl f)).card ≤ k₁)
    (hFineCost : ∀ v, (role v).preferredSign ≠ 0 → ((Fintype.card F*k₁:ℕ):ℝ) ≤ β*p₂*c v/400)
    (hCoarseBudget : (5/4:ℝ)*(Fintype.card F:ℝ)*lambda₁ ≤ p₂^2/1024) :
    let p : F ⊕ C → ℝ := Sum.elim (fun _ => p₁) (fun _ => p₂)
    let lambda : F ⊕ C → ℝ := Sum.elim (fun _ => lambda₁) (fun _ => lambda₂)
    let original (b : F ⊕ C) := (univ : Finset D).filter (fun d => colour d ∈ palette b)
    let E (side : Bool) := paletteSideCopies ends role (univ : Finset D) side
    (∀ b, lambda b ≤ β*(p b)^2*theta/(2:ℝ)^18) →
    (∀ b, paletteCopyCoreGap ends role (original b) = 0) →
    (∀ b d, d ∈ original b → (role (ends d).1).isLowCore (role (ends d).2) = false) →
    (∀ b v, (role v).preferredSign ≠ 0 →
      (15/16:ℝ)*lambda b*c v ≤ ((paletteCoreRow ends role (original b) v).card:ℝ) ∧
      ((paletteCoreRow ends role (original b) v).card:ℝ) ≤ 2*lambda b*c v) →
    (∀ b side, ((paletteSideCopies ends role (original b) side).card:ℝ) ≤
      (5/4:ℝ)*lambda b*(E side).card) →
    (∀ side, ((boundary ∩ E side).card:ℝ) ≤ p₁^2*((E side).card:ℝ)/512 ∧
      ((boundary ∩ E side).card:ℝ) ≤ p₂^2*((E side).card:ℝ)/1024) →
    (∀ b side,
      (paletteSideCopies ends role (original b) (!side)).card <
        (paletteSideCopies ends role (original b) side).card →
      let S := availableCorrectionCopies ends role (block b) (univ : Finset D) side
      (13/8:ℝ)*lambda b*(E side).card ≤
        (64*lambda b/(p b)^2)*(internalCorrectionCopies ends role S).card +
        ∑ v ∈ univ.filter (fun v => (role v).isCore = false),
          min ((64*lambda b/(p b))*(paletteCoreRow ends role S v).card)
            (paletteExceptionalCap role c (lambda b) v)) →
    (∀ b v, (role v).preferredSign ≠ 0 →
      let S := availablePreferredCopies ends role (block b) (univ : Finset D) source v
      (if special v then p b*c v/3 else β*p b*c v/8) ≤ (S.card:ℝ) ∧
      ((S ∩ boundary).card:ℝ) ≤ (if special v then p₁*c v/12 else β*p₁*c v/32)) →
    ∃ (fine : F → Finset D) (coarse : C → Finset D),
      (∀ f, IsPaletteBlockSelection ends role (block (.inl f)) (original (.inl f))
        (univ \ boundary) (fine f)) ∧
      (∀ g, IsPaletteBlockSelection ends role (block (.inr g)) (original (.inr g))
        ((univ \ boundary) \ univ.biUnion fine) (coarse g)) ∧
      let selected (b : F ⊕ C) := paletteExceptionalCopies ends role (original b) ∪ Sum.elim fine coarse b
      Pairwise (fun f g => Disjoint (selected f) (selected g)) ∧
      paletteCopyCoreGap ends role ((univ : Finset D) \ univ.biUnion selected) = 0 := by
  classical
  intro p lambda original E hLambda hOld hLow hIncidence hCount hBoundary hInitial hPref
  have hp (b : F ⊕ C) : 0 < p b := by cases b; exact hp₁; exact hp₁.trans_le hOrder
  have hpOne (b : F ⊕ C) : p b ≤ 1 := by cases b; exact hOrder.trans hp₂; exact hp₂
  have hpLo (b : F ⊕ C) : p₁ ≤ p b := by cases b; exact le_rfl; exact hOrder
  have hLambdaNonneg (b : F ⊕ C) : 0 ≤ lambda b := by cases b; exact hl₁; exact hl₂
  have hInput (b : F ⊕ C) (used : Finset D)
      (hLoss : ∀ side : Bool, (((boundary ∪ used) ∩ E side).card:ℝ) ≤ (p b)^2*(E side).card/512)
      (hUsed : ∀ v, (role v).preferredSign ≠ 0 →
        (paletteCopyDegree ends used v:ℝ) ≤ β*p b*c v/400) :
      Nonempty (PaletteBlockSelectionInput ends role (block b) (original b)
        ((univ \ boundary) \ used)) := by
    have hAvailable : ((univ : Finset D) \ boundary) \ used = univ \ (boundary ∪ used) := by
      ext d
      simp
    apply paletteBlockSelectionInput_of_reserves ends role _ _ _ _ c β theta (p b) (lambda b)
      hβ hβOne hTheta (hp b) (hpOne b) (hLambdaNonneg b) (hLambda b) (hLow b) hc (hIncidence b)
    · intro v hv
      have hLossPref := preferred_inter_card_le_fine_degree ends role (block b) univ used source v
      exact availablePreferredCopies_retains_reserve ends role (block b) boundary used source v
        (special v) β p₁ (p b) (c v) hβ hβOne hp₁.le (hpLo b) (hc v)
        (hPref b v hv).1 (hPref b v hv).2
        ((show (((availablePreferredCopies ends role (block b) univ source v) ∩ used).card:ℝ)
          ≤ (paletteCopyDegree ends used v:ℝ) by exact_mod_cast hLossPref).trans (hUsed v hv))
    · rw [hAvailable]
      apply paletteCorrectionCapacity_after_deletions ends role (block b) (original b) _ (p b) (lambda b)
        (paletteExceptionalCap role c (lambda b)) (hp b) (hpOne b) (hLambdaNonneg b)
      exact fun side hs => ⟨hCount b side,hLoss side,hInitial b side hs⟩
  apply exists_staged_palette_selections ends role colour block palette boundary
    hFineBlock hCoarseBlock hPalettes hWhole hOld hLow
  · intro f
    simpa only [sdiff_empty] using hInput (.inl f) ∅ (fun side => by
      simpa only [union_empty, p, Sum.elim_inl] using (hBoundary side).1) (fun v _ => by
        simp only [paletteCopyDegree, filter_empty, card_empty, Nat.cast_zero]
        exact div_nonneg (mul_nonneg (mul_nonneg hβ hp₁.le) (hc v)) (by norm_num))
  · intro fine hFine g
    have hLoss := fine_selection_keeps_coarse_budget ends role (fun f => block (.inl f))
      (fun f => original (.inl f)) fine boundary (univ \ boundary) p₂ lambda₁ hFine hCoarseBudget
      (fun f => hCount (.inl f) true) (fun f => hCount (.inl f) false)
      (hBoundary true).2 (hBoundary false).2
    apply hInput (.inr g) (univ.biUnion fine)
    · intro side
      cases side
      · exact hLoss.2
      · exact hLoss.1
    · intro v hv
      have hV := fine_selection_exceptional_loss ends role (fun f => block (.inl f))
        (fun f => original (.inl f)) fine (univ \ boundary) k₁ v
        (exceptional_of_preferredSign_ne_zero _ hv) hFine (fun f =>
          (paletteCopyDegree_filter_le_palette_card ends colour hProper (palette (.inl f)) v).trans (hFineSize f))
      exact (by exact_mod_cast hV : (paletteCopyDegree ends (univ.biUnion fine) v:ℝ) ≤ _).trans
        (hFineCost v hv)

end OverfullWork.ChenShan
