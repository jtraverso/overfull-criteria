module

public import OverfullWork.KLOSPartitionAdjustment
public import OverfullWork.KLOSExpansionStability

@[expose] public section

/-! Kühn–Lo–Osthus–Staden, Lemma 4.12, with explicit scale inequalities. -/
namespace OverfullWork.KLOS

open SimpleGraph Finset PrunedCore RobustExpansion
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem adjust_bipartite_component (ρ ν τ : ℝ) (A B : Finset V)
    (hρ : 0 < ρ) (hρOne : ρ ≤ 1) (hn : 0 < Fintype.card V)
    (hν : 0 ≤ ν) (hνOne : ν ≤ 1) (hτ : 0 ≤ τ) (hτHalf : τ ≤ 1 / 2)
    (hBip : CloseToBipartite G ρ A B) (hExpand : ExpandsAcross G ν τ A B)
    (hDense : (Real.sqrt (3 * Real.sqrt ρ) + 3 * Real.sqrt ρ) *
      (Fintype.card V : ℝ) ≤ G.minDegree)
    (hDegree : ∀ v ∈ A ∪ B, 9 * (Real.sqrt ρ * (Fintype.card V : ℝ)) ≤ (G.degree v : ℝ))
    (hWindow : 2 * (Real.sqrt ρ * (Fintype.card V : ℝ)) ≤ τ * (A.card : ℝ))
    (hSurplus : 4 * (Real.sqrt ρ * (Fintype.card V : ℝ)) ≤ ν * ((A ∪ B).card : ℝ)) :
    ∃ A' B' : Finset V, A' ∪ B' = A ∪ B ∧
      CloseToBipartite G (3 * Real.sqrt ρ) A' B' ∧ ExpandsAcross G (ν / 2) (2 * τ) A' B' ∧
      (∀ v ∈ A', neighboursIn G A' v ≤ neighboursIn G B' v) ∧
      (∀ v ∈ B', neighboursIn G B' v ≤ neighboursIn G A' v) := by
  let U := A ∪ B
  let X := bipartitionExceptions G ρ A B
  let initial : V → Bool := fun v => decide (v ∈ A)
  have hInitial (b : Bool) : U ∩ assignmentPart initial b = if b then A else B := by
    ext v
    have hd : ¬ (v ∈ A ∧ v ∈ B) := fun h => Finset.disjoint_left.mp hBip.1 h.1 h.2
    cases b <;> simp [U, assignmentPart, initial]
    tauto
  have hSet (b : Bool) : (U \ X) ∩ assignmentPart initial b = (U ∩ assignmentPart initial b) \ X := by
    ext v
    simp only [mem_inter, mem_sdiff]
    tauto
  have hCore : ∀ v ∈ U, v ∉ X → neighboursIn G U v ≤
      2 * neighboursIn G ((U \ X) ∩ assignmentPart initial (!(initial v))) v := by
    intro v hv hFixed
    have hLe : neighboursIn G U v ≤ G.degree v := by
      unfold neighboursIn
      exact (card_filter_le _ _).trans_eq (card_neighborFinset_eq_degree G v)
    rw [hSet, hInitial]
    by_cases ha : v ∈ A
    · simpa [initial, ha] using hLe.trans
        (bipartitionExceptions_retained_degree G ρ A B hρ hn hBip v ha hFixed (hDegree v hv))
    · have hb := (mem_union.mp hv).resolve_left ha
      have hComm : bipartitionExceptions G ρ B A = X := by
        simp only [X, bipartitionExceptions, union_comm]
      have h := bipartitionExceptions_retained_degree G ρ B A hρ hn (closeToBipartite_comm G hBip)
        v hb (hComm.symm ▸ hFixed) (hDegree v hv)
      rw [hComm] at h
      simpa [initial, ha] using hLe.trans h
  obtain ⟨f, hFixed, hCross⟩ := exists_bipartition_with_cross_dominance G U X initial hCore
  let A' := U ∩ assignmentPart f true
  let B' := U ∩ assignmentPart f false
  have hUnion : A' ∪ B' = U := by
    ext v
    simp only [A', B', assignmentPart, mem_union, mem_inter, mem_filter, mem_univ, true_and]
    cases f v <;> simp
  have hDis : Disjoint A' B' := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have h₁ : f v = true := (mem_filter.mp (mem_inter.mp hv).2).2
    have h₂ : f v = false := (mem_filter.mp (mem_inter.mp hw).2).2
    simp [h₁] at h₂
  have hEach (b : Bool) :
      ((U ∩ assignmentPart initial b) \ (U ∩ assignmentPart f b)).card +
      ((U ∩ assignmentPart f b) \ (U ∩ assignmentPart initial b)).card ≤ X.card := by
    let P := U ∩ assignmentPart initial b
    let Q := U ∩ assignmentPart f b
    have hDis : Disjoint (P \ Q) (Q \ P) :=
      Finset.disjoint_left.mpr (fun _ h₁ h₂ => (mem_sdiff.mp h₁).2 (mem_sdiff.mp h₂).1)
    have hSub : (P \ Q) ∪ (Q \ P) ⊆ X := by
      intro v hv
      by_contra h
      have he : v ∈ P ↔ v ∈ Q := by simp [P, Q, assignmentPart, hFixed v h]
      rcases mem_union.mp hv with hv | hv
      · exact (mem_sdiff.mp hv).2 (he.mp (mem_sdiff.mp hv).1)
      · exact (mem_sdiff.mp hv).2 (he.mpr (mem_sdiff.mp hv).1)
    have hSize := card_le_card hSub
    rw [card_union_of_disjoint hDis] at hSize
    exact hSize
  have hEdit : ((A \ A').card : ℝ) + ((A' \ A).card : ℝ) +
      ((B \ B').card : ℝ) + ((B' \ B).card : ℝ) ≤ Real.sqrt ρ * (Fintype.card V : ℝ) := by
    have hA := hEach true
    have hB := hEach false
    rw [hInitial] at hA hB
    have hAR : ((A \ A').card : ℝ) + ((A' \ A).card : ℝ) ≤ X.card := by
      exact_mod_cast hA
    have hBR : ((B \ B').card : ℝ) + ((B' \ B).card : ℝ) ≤ X.card := by
      exact_mod_cast hB
    have hBudget := bipartitionExceptions_card G ρ A B hρ hn hBip
    linarith only [hAR, hBR, hBudget]
  have hClose := closeToBipartite_of_same_union_edit G ρ (Real.sqrt ρ) (3 * Real.sqrt ρ) A B A' B'
    hρ hn hBip hDis hUnion hEdit (by
      have h := Real.le_sqrt_self_iff.mpr hρOne
      linarith only [h, Real.sqrt_nonneg ρ]) (by
      have h : 2 * Real.sqrt ρ + Real.sqrt ρ = 3 * Real.sqrt ρ := by ring
      rw [add_assoc, h]
      exact hDense)
  refine ⟨A', B', hUnion, hClose,
    expandsAcross_of_small_edit G A B A' B' ν τ _ hν hνOne hτ hτHalf hExpand hEdit hWindow hSurplus,
    ?_, ?_⟩
  · intro v hv
    have hd : f v = true := (mem_filter.mp (mem_inter.mp hv).2).2
    simpa [A', B', hd] using hCross v (mem_inter.mp hv).1
  · intro v hv
    have hd : f v = false := (mem_filter.mp (mem_inter.mp hv).2).2
    simpa [A', B', hd] using hCross v (mem_inter.mp hv).1

/-- The bipartite case of the final adjustment in §4.5. Transport the
original bipartition to the edited part, then make every vertex favor
the opposite side. -/
theorem adjust_edited_bipartite_component (ρ ν τ γ : ℝ) (A B W : Finset V)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V)
    (hν : 0 ≤ ν) (hνOne : ν ≤ 1) (hτ : 0 ≤ τ) (hτQuarter : τ ≤ 1 / 4)
    (hOld : CloseToBipartite G ρ A B) (hExpand : ExpandsAcross G ν τ A B)
    (hScale : ρ ≤ γ) (hScaleOne : 3 * γ ≤ 1)
    (hEdit : ((((A ∪ B) \ W) ∪ (W \ (A ∪ B))).card : ℝ) ≤ γ * (Fintype.card V : ℝ))
    (hSize : (Real.sqrt (3 * γ) + 2 * Real.sqrt ρ + γ) * (Fintype.card V : ℝ) ≤ G.minDegree)
    (hWindow : 2 * (γ * (Fintype.card V : ℝ)) ≤ τ * (A.card : ℝ))
    (hSurplus : 4 * (γ * (Fintype.card V : ℝ)) ≤ ν * ((A ∪ B).card : ℝ))
    (hFinalSize : (Real.sqrt (3 * Real.sqrt (3 * γ)) + 3 * Real.sqrt (3 * γ)) *
      (Fintype.card V : ℝ) ≤ G.minDegree)
    (hFinalDegree : 9 * (Real.sqrt (3 * γ) * (Fintype.card V : ℝ)) ≤ G.minDegree)
    (hFinalWindow : 2 * (Real.sqrt (3 * γ) * (Fintype.card V : ℝ)) ≤
      (2 * τ) * ((G.minDegree : ℝ) - 2 * Real.sqrt (3 * γ) * (Fintype.card V : ℝ)))
    (hFinalSurplus : 4 * (Real.sqrt (3 * γ) * (Fintype.card V : ℝ)) ≤ (ν / 2) *
      (2 * ((G.minDegree : ℝ) - 2 * Real.sqrt (3 * γ) * (Fintype.card V : ℝ)))) :
    ∃ A' B' : Finset V, A' ∪ B' = W ∧
      CloseToBipartite G (3 * Real.sqrt (3 * γ)) A' B' ∧ ExpandsAcross G (ν / 4) (4 * τ) A' B' ∧
      (∀ v ∈ A', neighboursIn G A' v ≤ neighboursIn G B' v) ∧
      (∀ v ∈ B', neighboursIn G B' v ≤ neighboursIn G A' v) := by
  obtain ⟨C, E, hCE, hClose, hExpansion⟩ := exists_bipartite_component_of_small_edit G ρ ν τ γ A B W
    hρ hn hν hνOne hτ (by linarith only [hτQuarter]) hOld hExpand
    hScale hEdit hSize hWindow hSurplus
  have hγ : 0 < 3 * γ := by linarith only [hρ, hScale]
  obtain ⟨hC, hE⟩ := bipartite_sides_lower G (3 * γ) C E hγ hn hClose
  have hParts : ((C ∪ E).card : ℝ) = (C.card : ℝ) + (E.card : ℝ) := by
    rw [card_union_of_disjoint hClose.1, Nat.cast_add]
  have hBoth : 2 * ((G.minDegree : ℝ) - 2 * Real.sqrt (3 * γ) * (Fintype.card V : ℝ)) ≤
      ((C ∪ E).card : ℝ) := by linarith only [hParts, hC, hE]
  have hWin := hFinalWindow.trans (mul_le_mul_of_nonneg_left hC (by positivity))
  have hSur := hFinalSurplus.trans (mul_le_mul_of_nonneg_left hBoth (by positivity))
  have hDeg (v : V) (_ : v ∈ C ∪ E) :
      9 * (Real.sqrt (3 * γ) * (Fintype.card V : ℝ)) ≤ (G.degree v : ℝ) :=
    hFinalDegree.trans (by exact_mod_cast G.minDegree_le_degree v)
  obtain ⟨A', B', hUnion, hClose', hExpand', hA, hB⟩ :=
    adjust_bipartite_component G (3 * γ) (ν / 2) (2 * τ) C E
      hγ hScaleOne hn (by positivity) (by linarith only [hνOne]) (by positivity)
      (by linarith only [hτQuarter]) hClose hExpansion hFinalSize hDeg hWin hSur
  have hνEq : ν / 2 / 2 = ν / 4 := by ring
  have hτEq : 2 * (2 * τ) = 4 * τ := by ring
  rw [hνEq, hτEq] at hExpand'
  exact ⟨A', B', hUnion.trans hCE, hClose', hExpand', hA, hB⟩

end OverfullWork.KLOS
