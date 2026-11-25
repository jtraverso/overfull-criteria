module

public import OverfullWork.KLOSBipartitionAdjustment
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! The final adjustment in §4.5 of Kühn–Lo–Osthus–Staden. -/
namespace OverfullWork.KLOS

open Finset SimpleGraph PrunedCore RobustExpansion
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A robust partition satisfying (D1)–(D7). The fibers of the assignment
are the parts. The finite set of labels records which fibers are bipartite. -/
structure RobustPartition (D : ℕ) (r ν τ : ℝ) where
  labels : Finset (Finset V)
  assign : V → ↥labels
  bipartite : Finset ↥labels
  nonempty_part : ∀ i, (assignmentPart assign i).Nonempty
  ordinary : ∀ i ∉ bipartite, IsSparseComponent G r (assignmentPart assign i) ∧
    ExpandsInside G ν τ (assignmentPart assign i)
  bipartite_component : ∀ i ∈ bipartite, ∃ A B : Finset V, A ∪ B = assignmentPart assign i ∧
    CloseToBipartite G r A B ∧ ExpandsAcross G ν τ A B ∧
    (∀ v ∈ A, neighboursIn G A v ≤ neighboursIn G B v) ∧
    (∀ v ∈ B, neighboursIn G B v ≤ neighboursIn G A v)
  dominance : ∀ v j, neighboursIn G (assignmentPart assign j) v ≤
    neighboursIn G (assignmentPart assign (assign v)) v
  count : ((labels.card : ℝ) + (bipartite.card : ℝ)) * D ≤
    (1 + r ^ ((1 : ℝ) / 3)) * (Fintype.card V : ℝ)
  core : ∀ i, let W := assignmentPart assign i
    ((W.filter fun v => (neighboursIn G W v : ℝ) <
      (D : ℝ) - r * (Fintype.card V : ℝ)).card : ℝ) ≤ r * (Fintype.card V : ℝ)

/-- The fibers are a partition of the ambient vertex set, as in (D1). -/
theorem RobustPartition.cover {D : ℕ} {r ν τ : ℝ} (P : RobustPartition G D r ν τ) :
    (univ : Finset ↥P.labels).biUnion (assignmentPart P.assign) = (univ : Finset V) := by
  ext v
  simp only [mem_biUnion, mem_univ, true_and, iff_true]
  exact ⟨P.assign v, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩

theorem RobustPartition.disjoint_parts {D : ℕ} {r ν τ : ℝ} (P : RobustPartition G D r ν τ)
    {i j : ↥P.labels} (hij : i ≠ j) :
    Disjoint (assignmentPart P.assign i) (assignmentPart P.assign j) :=
  Finset.disjoint_left.mpr fun _ hi hj => hij ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)

/-- The within-part degree bound in (D4), in multiplicative form. -/
theorem RobustPartition.internal_degree {D : ℕ} {r ν τ : ℝ} (P : RobustPartition G D r ν τ)
    (hRegular : ∀ v, G.degree v = D) (v : V) :
    D ≤ P.labels.card * neighboursIn G (assignmentPart P.assign (P.assign v)) v := by
  simpa only [hRegular v, Fintype.card_coe] using
    degree_le_card_mul_of_part_dominance G P.assign v (P.dominance v)

/-- The two crossing degree bounds in (D5), in multiplicative form. -/
theorem RobustPartition.crossing_degree {D : ℕ} {r ν τ : ℝ} (P : RobustPartition G D r ν τ)
    (hRegular : ∀ v, G.degree v = D) (i : ↥P.labels) (hi : i ∈ P.bipartite) :
    ∃ A B : Finset V, A ∪ B = assignmentPart P.assign i ∧
      CloseToBipartite G r A B ∧ ExpandsAcross G ν τ A B ∧
      (∀ v ∈ A, D ≤ 2 * P.labels.card * neighboursIn G B v) ∧
      (∀ v ∈ B, D ≤ 2 * P.labels.card * neighboursIn G A v) := by
  obtain ⟨A, B, hUnion, hClose, hExpand, hA, hB⟩ := P.bipartite_component i hi
  have hDegrees (v : V) : neighboursIn G (A ∪ B) v = neighboursIn G A v + neighboursIn G B v := by
    rw [neighboursIn_eq_filter_card, neighboursIn_eq_filter_card, neighboursIn_eq_filter_card,
      filter_union, card_union_of_disjoint (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hClose.1)]
  have hBound (v : V) (hv : v ∈ A ∪ B) :
      D ≤ P.labels.card * (neighboursIn G A v + neighboursIn G B v) := by
    have hv' : v ∈ assignmentPart P.assign i := hUnion ▸ hv
    have hi' : P.assign v = i := (mem_filter.mp hv').2
    have h := P.internal_degree G hRegular v
    rwa [hi', ← hUnion, hDegrees] at h
  refine ⟨A, B, hUnion, hClose, hExpand, ?_, ?_⟩
  · intro v hv
    have h := (hBound v (mem_union_left _ hv)).trans
      (Nat.mul_le_mul_left P.labels.card (show neighboursIn G A v + neighboursIn G B v ≤
        2 * neighboursIn G B v by have := hA v hv; omega))
    simpa only [← Nat.mul_assoc, Nat.mul_comm P.labels.card 2] using h
  · intro v hv
    have h := (hBound v (mem_union_right _ hv)).trans
      (Nat.mul_le_mul_left P.labels.card (show neighboursIn G A v + neighboursIn G B v ≤
        2 * neighboursIn G A v by have := hB v hv; omega))
    simpa only [← Nat.mul_assoc, Nat.mul_comm P.labels.card 2] using h

/-- Sufficient inequalities for the two adjustments. The original boundary
error is `ρ`, the allowed move in Lemma 4.11 is `η`, and `r` is the final error. -/
structure AdjustmentScales (α ν τ r ρ η : ℝ) : Prop where
  initial_le_edit : ρ ≤ η
  part_budget : (2 / α) * Real.sqrt ρ ≤ η
  initial_degree : 4 * Real.sqrt ρ ≤ α
  transport_degree : Real.sqrt (3 * η) + 2 * Real.sqrt ρ + η ≤ α
  transport_window : 8 * η ≤ τ * α
  transport_surplus : 16 * η ≤ ν * α
  bipartite_error : 3 * η ≤ 1
  bipartite_degree : 9 * Real.sqrt (3 * η) ≤ α
  bipartite_window : 2 * Real.sqrt (3 * η) ≤ τ * α
  bipartite_surplus : 8 * Real.sqrt (3 * η) ≤ ν * α
  final_error : 3 * Real.sqrt (3 * η) ≤ r
  final_degree : 3 * Real.sqrt r ≤ α
  core_error : 2 * Real.sqrt ρ ≤ r
  count_slack : 2 * Real.sqrt ρ * (1 + r ^ ((1 : ℝ) / 3)) ≤ r ^ ((1 : ℝ) / 3) * α

/-- For each fixed expansion threshold and final error, every sufficiently
small original boundary error admits both adjustments. -/
theorem exists_adjustment_scales (α ν τ r : ℝ) (hα : 0 < α) (hν : 0 < ν) (hτ : 0 < τ)
    (hr : 0 < r) (hDegree : 3 * Real.sqrt r ≤ α) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ c →
      ∃ η : ℝ, η ≤ r ∧ AdjustmentScales α ν τ r ρ η := by
  let z := min (1 / 4 : ℝ) (min (α / 12) (min (τ * α / 24) (min (ν * α / 32) (r / 3))))
  have hz : 0 < z := lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))
  have hzOne : z ≤ 1 / 4 := min_le_left _ _
  have hzα : z ≤ α / 12 := (min_le_right _ _).trans (min_le_left _ _)
  have hzτ : z ≤ τ * α / 24 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hzν : z ≤ ν * α / 32 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hzr : z ≤ r / 3 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let η := z ^ 2 / 3
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηz : η ≤ z := by
    dsimp only [η]
    have h := mul_le_mul_of_nonneg_left hzOne hz.le
    nlinarith only [h, hz]
  have hRoot : Real.sqrt (3 * η) = z := by
    have h : 3 * η = z ^ 2 := by dsimp only [η]; ring
    rw [h, Real.sqrt_sq_eq_abs, abs_of_pos hz]
  let ε := r ^ ((1 : ℝ) / 3)
  have hε : 0 < ε := Real.rpow_pos_of_pos hr _
  let b := min (α * η / 2) (min (α / 4) (min (r / 2) (ε * α / (2 * (1 + ε)))))
  have hb : 0 < b := lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  refine ⟨min η (b ^ 2), lt_min hη (by positivity), ?_⟩
  intro ρ hρ hρb
  have hρη : ρ ≤ η := hρb.trans (min_le_left _ _)
  have hs : Real.sqrt ρ ≤ b := by
    have h := Real.sqrt_le_sqrt (hρb.trans (min_le_right _ _))
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos hb] at h
  have hPart : Real.sqrt ρ ≤ α * η / 2 := hs.trans (min_le_left _ _)
  have hαSmall : Real.sqrt ρ ≤ α / 4 := hs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrSmall : Real.sqrt ρ ≤ r / 2 := hs.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSlack : Real.sqrt ρ ≤ ε * α / (2 * (1 + ε)) := hs.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hPart' := mul_le_mul_of_nonneg_left hPart (by positivity : 0 ≤ 2 / α)
  have hCancel : (2 / α) * (α * η / 2) = η := by field_simp
  rw [hCancel] at hPart'
  have hSlack' := (le_div_iff₀ (by positivity : 0 < 2 * (1 + ε))).mp hSlack
  refine ⟨η, by linarith only [hηz, hzr, hr], ⟨hρη, hPart', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hDegree, ?_, ?_⟩⟩
  · linarith only [hαSmall]
  · rw [hRoot]
    linarith only [hαSmall, hzα, hηz, hα]
  · linarith only [hηz, hzτ, hz]
  · linarith only [hηz, hzν, hz]
  · linarith only [hηz, hzOne]
  · rw [hRoot]
    linarith only [hzα, hα]
  · rw [hRoot]
    linarith only [hzτ, hz]
  · rw [hRoot]
    linarith only [hzν, hz]
  · rw [hRoot]
    linarith only [hzr]
  · linarith only [hrSmall]
  · change 2 * Real.sqrt ρ * (1 + ε) ≤ ε * α
    linarith only [hSlack']

/-- Assemble (D1)–(D7) once a terminal partition and the numerical
inequalities for the adjustments are available. -/
theorem robustPartition_of_terminal {ρ α ν τ r η : ℝ} (P : SparsePartition G ρ)
    (D : ℕ) (hRegular : ∀ v, G.degree v = D) (hn : 0 < Fintype.card V)
    (hDense : α * (Fintype.card V : ℝ) ≤ D)
    (hα : 0 < α) (hρ : 0 < ρ) (hν : 0 ≤ ν) (hνOne : ν ≤ 1)
    (hτ : 0 ≤ τ) (hτQuarter : τ ≤ 1 / 4) (hηr : η ≤ r) (hrOne : r ≤ 1)
    (hScales : AdjustmentScales α ν τ r ρ η) (hTerminal : IsTerminal G P ν τ) :
    Nonempty (RobustPartition G D r (ν / 4) (4 * τ)) := by
  let n := (Fintype.card V : ℝ)
  have hnPos : 0 < n := by dsimp only [n]; exact_mod_cast hn
  have : Nonempty V := Fintype.card_pos_iff.mp hn
  have hMinNat : G.minDegree = D := by
    apply le_antisymm
    · obtain ⟨v⟩ := ‹Nonempty V›
      simpa only [hRegular] using G.minDegree_le_degree v
    · exact G.le_minDegree_of_forall_le_degree D fun v => (hRegular v).ge
  have hMin : (G.minDegree : ℝ) = D := by exact_mod_cast hMinNat
  have hScaleToDegree (x : ℝ) (hx : x ≤ α) : x * n ≤ (D : ℝ) :=
    (mul_le_mul_of_nonneg_right hx hnPos.le).trans hDense
  have hη : 0 < η := hρ.trans_le hScales.initial_le_edit
  have hρOne : ρ ≤ 1 := by linarith only [hScales.bipartite_error, hScales.initial_le_edit]
  have hρRoot : ρ ≤ Real.sqrt ρ := Real.le_sqrt_self_iff.mpr hρOne
  have hDominance := hScaleToDegree _ hScales.initial_degree
  have hPartLower : (α / 2) * n ≤ (G.minDegree : ℝ) - 2 * Real.sqrt ρ * n := by
    rw [hMin]
    have h := mul_le_mul_of_nonneg_right hScales.initial_degree hnPos.le
    change α * n ≤ (D : ℝ) at hDense
    linarith only [h, hDense]
  have hCount := weighted_part_count G P ∅ (empty_subset _) (by simp) hρ hn
  simp only [card_empty, Nat.cast_zero, add_zero] at hCount
  have hParts : (P.parts.card : ℝ) ≤ 2 / α := by
    have h := (mul_le_mul_of_nonneg_left hPartLower (Nat.cast_nonneg (α := ℝ) P.parts.card)).trans hCount
    rw [← mul_assoc] at h
    change (P.parts.card : ℝ) * (α / 2) * n ≤ n at h
    have h' := (mul_le_mul_iff_of_pos_right hnPos).mp (h.trans (by rw [one_mul] : n ≤ 1 * n))
    apply (le_div_iff₀ hα).mpr
    linarith only [h']
  have hMove := (mul_le_mul_of_nonneg_right hParts (Real.sqrt_nonneg ρ)).trans hScales.part_budget
  have hCut := (mul_le_mul_of_nonneg_left hρRoot (Nat.cast_nonneg (α := ℝ) P.parts.card)).trans hMove
  have hMoveDegree := hScaleToDegree (Real.sqrt η + 2 * Real.sqrt ρ)
    (by have h := Real.sqrt_le_sqrt (show η ≤ 3 * η by linarith only [hη])
        linarith only [h, hScales.transport_degree, hη])
  obtain ⟨f, hEdit, hSparse, hLocal, hCore⟩ :=
    adjust_sparsePartition G P D hRegular η hρ hn hMove hCut hMoveDegree hDominance
  let bip := (univ : Finset ↥P.parts).filter fun i => ¬ ExpandsInside G ν τ i.val
  have hBip (i : ↥P.parts) (hi : i ∈ bip) :
      ∃ A B, A ∪ B = i.val ∧ CloseToBipartite G ρ A B ∧ ExpandsAcross G ν τ A B := by
    exact (hTerminal i.val i.property).resolve_left (mem_filter.mp hi).2
  have hBudget (i : ↥P.parts) :
      ((i.val \ assignmentPart f i).card : ℝ) + ((assignmentPart f i \ i.val).card : ℝ) ≤ η * n := by
    have hd : Disjoint (i.val \ assignmentPart f i) (assignmentPart f i \ i.val) :=
      Finset.disjoint_left.mpr fun _ h₁ h₂ => (mem_sdiff.mp h₁).2 (mem_sdiff.mp h₂).1
    have hi := hEdit i
    dsimp only at hi
    rw [card_union_of_disjoint hd, Nat.cast_add] at hi
    exact hi
  have hBig (i : ↥P.parts) : α / 2 * n ≤ (i.val.card : ℝ) := by
    have h := sparseComponent_card_lower G ρ i.val hρ hn (P.sparse i.val i.property)
    have hs : 0 ≤ Real.sqrt ρ * n := by positivity
    change (G.minDegree : ℝ) - Real.sqrt ρ * n ≤ (i.val.card : ℝ) at h
    linarith only [hPartLower, h, hs]
  have hFinalR := hScaleToDegree _ hScales.final_degree
  have hFinalSize : (Real.sqrt (3 * Real.sqrt (3 * η)) + 3 * Real.sqrt (3 * η)) * n ≤
      (D : ℝ) := by
    have hRoot := Real.sqrt_le_sqrt hScales.final_error
    have hRRoot := Real.le_sqrt_self_iff.mpr hrOne
    have hNumerical : Real.sqrt (3 * Real.sqrt (3 * η)) + 3 * Real.sqrt (3 * η) ≤ α := by
      linarith only [hScales.final_degree, hRoot, hRRoot, hScales.final_error, Real.sqrt_nonneg r]
    exact hScaleToDegree _ hNumerical
  refine ⟨⟨P.parts, f, bip, ?_, ?_, ?_, hLocal, ?_, ?_⟩⟩
  · intro i
    apply card_pos.mp
    exact_mod_cast ((mul_pos (Real.sqrt_pos.mpr hη) hnPos).trans_le (hSparse i).1)
  · intro i hi
    have hi' : ExpandsInside G ν τ i.val := by
      by_contra h
      exact hi (mem_filter.mpr ⟨mem_univ _, h⟩)
    have hWindow : 4 * (η * n) ≤ τ * (i.val.card : ℝ) := by
      have h₁ := mul_le_mul_of_nonneg_right hScales.transport_window hnPos.le
      have h₂ := mul_le_mul_of_nonneg_left (hBig i) hτ
      nlinarith only [h₁, h₂]
    have hSurplus : 8 * (η * n) ≤ ν * (i.val.card : ℝ) := by
      have h₁ := mul_le_mul_of_nonneg_right hScales.transport_surplus hnPos.le
      have h₂ := mul_le_mul_of_nonneg_left (hBig i) hν
      nlinarith only [h₁, h₂]
    refine ⟨sparseComponent_relax G _ η r hη hn hηr ?_ (hSparse i), ?_⟩
    · rw [hMin]
      exact hScaleToDegree _ (by linarith only [hScales.final_degree, Real.sqrt_nonneg r])
    · apply expandsInside_mono G _ (show ν / 4 ≤ ν / 2 by linarith only [hν])
        (show 2 * τ ≤ 4 * τ by linarith only [hτ])
      exact expandsInside_of_small_edit G i.val (assignmentPart f i) ν τ _
        hν hνOne hτ (by linarith only [hτQuarter]) hi' (hBudget i) hWindow hSurplus
  · intro i hi
    obtain ⟨A, B, hAB, hClose, hExpand⟩ := hBip i hi
    have hALower := (bipartite_sides_lower G ρ A B hρ hn hClose).1
    have hWindow : 2 * (η * n) ≤ τ * (A.card : ℝ) := by
      have h₁ := mul_le_mul_of_nonneg_right hScales.transport_window hnPos.le
      have h₂ := mul_le_mul_of_nonneg_left (hPartLower.trans hALower) hτ
      nlinarith only [h₁, h₂, mul_nonneg (mul_nonneg hτ hα.le) hnPos.le]
    have hSurplus : 4 * (η * n) ≤ ν * ((A ∪ B).card : ℝ) := by
      rw [hAB]
      have h₁ := mul_le_mul_of_nonneg_right hScales.transport_surplus hnPos.le
      have h₂ := mul_le_mul_of_nonneg_left (hBig i) hν
      nlinarith only [h₁, h₂, mul_nonneg (mul_nonneg hν hα.le) hnPos.le]
    have hFinalLower : α / 2 * n ≤ (G.minDegree : ℝ) - 2 * Real.sqrt (3 * η) * n := by
      rw [hMin]
      have h := mul_le_mul_of_nonneg_right hScales.bipartite_degree hnPos.le
      have hRoot : 0 ≤ Real.sqrt (3 * η) * n := by positivity
      change α * n ≤ (D : ℝ) at hDense
      linarith only [h, hRoot, hDense]
    have hFinalWindow : 2 * (Real.sqrt (3 * η) * n) ≤
        (2 * τ) * ((G.minDegree : ℝ) - 2 * Real.sqrt (3 * η) * n) := by
      have h₁ := mul_le_mul_of_nonneg_right hScales.bipartite_window hnPos.le
      have h₂ := mul_le_mul_of_nonneg_left hFinalLower (by positivity : 0 ≤ 2 * τ)
      nlinarith only [h₁, h₂]
    have hFinalSurplus : 4 * (Real.sqrt (3 * η) * n) ≤ (ν / 2) *
        (2 * ((G.minDegree : ℝ) - 2 * Real.sqrt (3 * η) * n)) := by
      have h₁ := mul_le_mul_of_nonneg_right hScales.bipartite_surplus hnPos.le
      have h₂ := mul_le_mul_of_nonneg_left hFinalLower hν
      nlinarith only [h₁, h₂]
    obtain ⟨A', B', hAB', hClose', hExpand', hA, hB⟩ :=
      adjust_edited_bipartite_component G ρ ν τ η A B (assignmentPart f i)
        hρ hn hν hνOne hτ hτQuarter hClose hExpand hScales.initial_le_edit hScales.bipartite_error
        (by rw [hAB]; exact hEdit i) (hMin.symm ▸ hScaleToDegree _ hScales.transport_degree)
        hWindow hSurplus (hMin.symm ▸ hFinalSize)
        (by rw [hMin]; simpa only [mul_assoc] using hScaleToDegree _ hScales.bipartite_degree) hFinalWindow hFinalSurplus
    exact ⟨A', B', hAB', closeToBipartite_relax G A' B' _ r (by positivity) hn
      hScales.final_error (hMin.symm ▸ hFinalR) hClose', hExpand', hA, hB⟩
  · let tagged := bip.image Subtype.val
    have hSub : tagged ⊆ P.parts := by
      intro U hU
      obtain ⟨i, _, rfl⟩ := mem_image.mp hU
      exact i.property
    have hTagged (U : Finset V) (hU : U ∈ tagged) : NearlyBipartite G ρ U := by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hU
      obtain ⟨A, B, hAB, hClose, _⟩ := hBip i hi
      exact ⟨A, B, hAB, hClose⟩
    have hCard : tagged.card = bip.card := card_image_of_injective _ Subtype.val_injective
    have h := weighted_part_count_le G P tagged hSub hTagged hρ hn α (r ^ ((1 : ℝ) / 3))
      (Real.rpow_nonneg (hη.le.trans hηr) _) (hMin.symm ▸ hDense) hScales.count_slack
    rwa [hCard, hMin] at h
  · intro i
    have hSub : (assignmentPart f i).filter (fun v => (neighboursIn G (assignmentPart f i) v : ℝ) <
        (D : ℝ) - r * n) ⊆ (assignmentPart f i).filter (fun v =>
        (neighboursIn G (assignmentPart f i) v : ℝ) < (D : ℝ) - 2 * Real.sqrt ρ * n) := by
      intro v hv
      obtain ⟨hv, hLow⟩ := mem_filter.mp hv
      have h := mul_le_mul_of_nonneg_right hScales.core_error hnPos.le
      exact mem_filter.mpr ⟨hv, by linarith only [h, hLow]⟩
    refine (show (↑(_ : ℕ) : ℝ) ≤ ↑(_ : ℕ) by exact_mod_cast card_le_card hSub).trans ?_
    exact (hCore i).trans (mul_le_mul_of_nonneg_right hηr hnPos.le)

/-- Enlarging the small-set cutoff preserves a robust partition. -/
def RobustPartition.mono_window {D : ℕ} {r ν τ τ' : ℝ}
    (P : RobustPartition G D r ν τ) (hτ : τ ≤ τ') : RobustPartition G D r ν τ' where
  labels := P.labels
  assign := P.assign
  bipartite := P.bipartite
  nonempty_part := P.nonempty_part
  ordinary i hi :=
    ⟨(P.ordinary i hi).1, expandsInside_mono G _ le_rfl hτ (P.ordinary i hi).2⟩
  bipartite_component i hi := by
    obtain ⟨A, B, hAB, hClose, hExpand, hA, hB⟩ := P.bipartite_component i hi
    exact ⟨A, B, hAB, hClose, expandsAcross_mono G A B le_rfl hτ hExpand, hA, hB⟩
  dominance := P.dominance
  count := P.count
  core := P.core

universe u

/-- Kühn–Lo–Osthus–Staden, Theorem 3.1. We use a real-valued extension
of the paper's function on `(0,1)`. Positivity on that interval suffices:
a finite common cutoff handles the values of the function at all possible
terminal stages. -/
theorem exists_robustPartition_regular (α τ : ℝ) (f : ℝ → ℝ)
    (hα : 0 < α) (hτ : 0 < τ)
    (hf : ∀ x : ℝ, 0 < x → x < 1 → 0 < f x) :
    ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
        (D : ℕ), n₀ ≤ Fintype.card W → (∀ v, H.degree v = D) →
        α * (Fintype.card W : ℝ) ≤ D →
        ∃ r ν : ℝ, 1 / (n₀ : ℝ) ≤ r ∧ r ≤ ν ∧ ν ≤ τ ∧ r ≤ f ν ∧
          1 / (n₀ : ℝ) ≤ f r ∧ Nonempty (RobustPartition H D r ν τ) := by
  by_cases hαOne : α ≤ 1
  swap
  · refine ⟨1, by norm_num, ?_⟩
    intro W _ _ H _ D hn hRegular hDense
    have hPos : 0 < Fintype.card W := hn
    have hnR : (0 : ℝ) < Fintype.card W := by exact_mod_cast hPos
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hPos
    have hD : D ≤ Fintype.card W := by
      rw [← hRegular v, ← card_neighborFinset_eq_degree]
      exact card_le_univ _
    have hDR : (D : ℝ) ≤ Fintype.card W := by exact_mod_cast hD
    have hLt := mul_lt_mul_of_pos_right (lt_of_not_ge hαOne) hnR
    rw [one_mul] at hLt
    exact (not_le_of_gt hLt (hDense.trans hDR)).elim
  let t := min (τ / 4) (1 / 8)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htτ : 4 * t ≤ τ := by have h : t ≤ τ / 4 := min_le_left _ _; linarith only [h]
  have htCap : t ≤ 1 / 8 := min_le_right _ _
  let seed := (t * α / 4) ^ 2
  have hSeedRoot : Real.sqrt seed = t * α / 4 := Real.sqrt_sq (by positivity)
  have hSeedOne : seed ≤ 1 := by
    have hmul := mul_le_mul htCap hαOne hα.le (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hb : t * α / 4 ≤ 1 := by nlinarith only [hmul]
    dsimp only [seed]
    exact pow_le_one₀ (by positivity) hb
  let finalError (x : ℝ) := min ((α / 3) ^ 2) (min (x / 4) (min (f (x / 4)) (1 / 2)))
  have hError (x : ℝ) (hx : 0 < x) (hxt : x ≤ t) :
      0 < finalError x ∧ finalError x ≤ x / 4 ∧ finalError x ≤ f (x / 4) ∧
        finalError x ≤ 1 ∧ 3 * Real.sqrt (finalError x) ≤ α := by
    have hxFour : 0 < x / 4 := by positivity
    have hxOne : x / 4 < 1 := by linarith only [hxt, htCap]
    have hp : 0 < finalError x := lt_min (by positivity)
      (lt_min hxFour (lt_min (hf (x / 4) hxFour hxOne) (by norm_num)))
    have hν : finalError x ≤ x / 4 := (min_le_right _ _).trans (min_le_left _ _)
    have hF : finalError x ≤ f (x / 4) := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    have hOne : finalError x ≤ 1 / 2 := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
    have hSq : finalError x ≤ (α / 3) ^ 2 := min_le_left _ _
    have hRoot := Real.sqrt_le_sqrt hSq
    rw [Real.sqrt_sq (by positivity : 0 ≤ α / 3)] at hRoot
    exact ⟨hp, hν, hF, by linarith only [hOne], by linarith only [hRoot]⟩
  let Q (ρ x : ℝ) := 0 < x ∧ x ≤ t ∧
    ∃ η, η ≤ finalError x ∧ AdjustmentScales α x t (finalError x) ρ η
  have hPick (x : ℝ) (hx : 0 < x) (hxt : x ≤ t) :
      ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ c → Q ρ x := by
    have he := hError x hx hxt
    obtain ⟨c, hc, hChoice⟩ := exists_adjustment_scales α x t (finalError x)
      hα hx ht he.1 he.2.2.2.2
    exact ⟨c, hc, fun ρ hρ hle => ⟨hx, hxt, hChoice ρ hρ hle⟩⟩
  obtain ⟨B, ρ, ν, hρ, hQ, hTerminal⟩ := exists_regular_prepartition_with.{u}
    α t seed Q hPick hα hαOne ht (by linarith only [htCap]) (by dsimp only [seed]; positivity)
    hSeedOne (by rw [hSeedRoot]; ring_nf; exact le_rfl)
  have hCutoff (i : Fin B) : ∃ N : ℕ, 1 / finalError (ν i) ≤ N ∧ 1 / f (finalError (ν i)) ≤ N := by
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / finalError (ν i)) (1 / f (finalError (ν i))))
    exact ⟨N, (le_max_left _ _).trans hN.le, (le_max_right _ _).trans hN.le⟩
  choose cutoff hCutoff using hCutoff
  let n₀ : ℕ := max 1 ((univ : Finset (Fin B)).sup cutoff)
  have hn₀ : 0 < n₀ := Nat.zero_lt_one.trans_le (le_max_left _ _)
  have hn₀R : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  refine ⟨n₀, hn₀, ?_⟩
  intro W _ _ H _ D hn hRegular hDense
  have hnPos := hn₀.trans_le hn
  obtain ⟨i, hi, P, hTerm⟩ := hTerminal H D hnPos hRegular hDense
  obtain ⟨hν, hνt, η, hηr, hScales⟩ := hQ i hi
  rcases hError (ν i) hν hνt with ⟨hr, hrν, hrf, hrOne, _⟩
  have hντ : ν i / 4 ≤ τ := by linarith only [hνt, htτ, hτ]
  have hrBelow : finalError (ν i) < 1 := by linarith only [hrν, hνt, htCap]
  have hfr := hf _ hr hrBelow
  have hNatBound : cutoff ⟨i, hi⟩ ≤ n₀ :=
    (Finset.le_sup (f := cutoff) (mem_univ (⟨i, hi⟩ : Fin B))).trans (le_max_right _ _)
  have hBound : (cutoff ⟨i, hi⟩ : ℝ) ≤ n₀ := by exact_mod_cast hNatBound
  have hInv (x : ℝ) (hx : 0 < x) (h : 1 / x ≤ (cutoff ⟨i, hi⟩ : ℝ)) :
      1 / (n₀ : ℝ) ≤ x :=
    (div_le_iff₀ hn₀R).mpr (by
      rw [mul_comm]
      exact (div_le_iff₀ hx).mp (h.trans hBound))
  have hνOne : ν i ≤ 1 := by linarith only [hνt, htCap]
  obtain ⟨partition⟩ := robustPartition_of_terminal H P D hRegular hnPos hDense
    hα (hρ i).1 hν.le hνOne ht.le (by linarith only [htCap]) hηr hrOne hScales hTerm
  exact ⟨finalError (ν i), ν i / 4,
    hInv _ hr (hCutoff ⟨i, hi⟩).1, hrν, hντ, hrf, hInv _ hfr (hCutoff ⟨i, hi⟩).2,
    ⟨partition.mono_window H htτ⟩⟩

end OverfullWork.KLOS
