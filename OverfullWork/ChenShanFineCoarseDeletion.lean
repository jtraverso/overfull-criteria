module

public import OverfullWork.ChenShanPaletteCapacity
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

/-- From (5.4), the fine correction edges for one palette use at
most (5/4) λ₁ |Eσ| copies on side σ. Taking the union with the
boundary brings the total to at most p₂² |Eσ| / 512. -/
theorem fine_and_boundary_deletion_budget {F D : Type*} [Fintype F]
    (E boundary : Finset D) (correction preferred : F → Finset D)
    (p₂ lambda₁ : ℝ)
    (hPreferred : ∀ i, Disjoint (preferred i) E)
    (hCorrection : ∀ i, ((correction i ∩ E).card:ℝ) ≤ (5/4:ℝ)*lambda₁*E.card)
    (hBoundary : ((boundary ∩ E).card:ℝ) ≤ p₂^2*(E.card:ℝ)/1024)
    (hPalette : (5/4:ℝ)*(Fintype.card F:ℝ)*lambda₁ ≤ p₂^2/1024) :
    (((boundary ∪ (univ : Finset F).biUnion fun i => correction i ∪ preferred i) ∩ E).card:ℝ) ≤
      p₂^2*(E.card:ℝ)/512 := by
  classical
  let T := (univ : Finset F).biUnion (fun i => correction i ∩ E)
  have hSet :
      (boundary ∪ (univ : Finset F).biUnion fun i => correction i ∪ preferred i) ∩ E =
        (boundary ∩ E) ∪ T := by
    ext e
    simp only [T, mem_inter, mem_union, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨hb | ⟨i, hi | hi⟩, he⟩
      · exact Or.inl ⟨hb,he⟩
      · exact Or.inr ⟨i,hi,he⟩
      · exact (disjoint_left.mp (hPreferred i) hi he).elim
    · rintro (⟨hb,he⟩ | ⟨i,hi,he⟩)
      · exact ⟨Or.inl hb,he⟩
      · exact ⟨Or.inr ⟨i,Or.inl hi⟩,he⟩
  rw [hSet]
  have hUnion : (((boundary ∩ E) ∪ T).card:ℝ) ≤ ((boundary ∩ E).card:ℝ) + T.card := by
    exact_mod_cast card_union_le (boundary ∩ E) T
  have hT : (T.card:ℝ) ≤ ∑ i, ((correction i ∩ E).card:ℝ) := by
    exact_mod_cast (card_biUnion_le (s := (univ : Finset F)) (t := fun i => correction i ∩ E))
  have hSum : (∑ i, ((correction i ∩ E).card:ℝ)) ≤
      (Fintype.card F:ℝ)*((5/4:ℝ)*lambda₁*E.card) := by
    simpa only [sum_const, card_univ, nsmul_eq_mul] using
      (sum_le_sum (s := (univ : Finset F)) (fun i _ => hCorrection i))
  have hBudget := mul_le_mul_of_nonneg_right hPalette (Nat.cast_nonneg (α := ℝ) E.card)
  nlinarith only [hUnion,hT,hSum,hBudget,hBoundary]

/-- A side can only lose correction copies when its imbalance is
positive. This converts an upper bound on eI,σ to the per-palette
hypothesis of the deletion budget. -/
theorem correction_side_count_le_palette_count {D : Type*}
    (selected E : Finset D) (e eOther : ℕ) (bound : ℝ)
    (hBound : (e:ℝ) ≤ bound)
    (hSelected : (selected ∩ E).card ≤ e-eOther) :
    ((selected ∩ E).card:ℝ) ≤ bound := by
  have h := hSelected.trans (Nat.sub_le e eOther)
  exact le_trans (by exact_mod_cast h) hBound

/-- The preferred-edge budgets after deleting the boundary and the fine
selections, for both types of exceptional vertex in §5.1.4. Counts are
expressed as original counts minus their corresponding losses. -/
theorem coarse_preferred_edges_after_deletions
    (β p₁ p₂ c ordinary special ordinaryBoundary specialBoundary fine : ℝ)
    (hβ : 0 ≤ β) (hβOne : β ≤ 1)
    (hp₁ : 0 ≤ p₁) (hp : p₁ ≤ p₂) (hc : 0 ≤ c)
    (hOrd : β*p₂*c/8 ≤ ordinary) (hSpec : p₂*c/3 ≤ special)
    (hOrdBoundary : ordinaryBoundary ≤ β*p₁*c/32)
    (hSpecBoundary : specialBoundary ≤ p₁*c/12)
    (hFine : fine ≤ β*p₂*c/400) :
    β*p₂*c/16 ≤ ordinary-ordinaryBoundary-fine ∧
      β*p₂*c/16 ≤ special-specialBoundary-fine := by
  have hP := mul_le_mul_of_nonneg_right hp hc
  have hPB := mul_le_mul_of_nonneg_left hP hβ
  have hPC : 0 ≤ p₂*c := mul_nonneg (hp₁.trans hp) hc
  have hBC : 0 ≤ β*(p₂*c) := mul_nonneg hβ hPC
  have hβC := mul_le_mul_of_nonneg_right hβOne hPC
  constructor <;> nlinarith only [hP,hPB,hPC,hBC,hβC,hOrd,hSpec,hOrdBoundary,hSpecBoundary,hFine]


private theorem card_sub_sdiff_eq_inter {D : Type*} (S K : Finset D) :
    (S.card:ℝ)-((S \ K).card:ℝ) = ((S ∩ K).card:ℝ) := by
  have h := card_sdiff_add_card_inter S K
  exact sub_eq_of_eq_add (by exact_mod_cast (h.symm.trans (Nat.add_comm _ _)))

private theorem disjoint_internal_rows {D Z : Type*} (internal : Finset D)
    (Z₀ : Finset Z) (rows : Z → Finset D)
    (h : ∀ z ∈ Z₀, Disjoint internal (rows z)) :
    Disjoint internal (Z₀.biUnion rows) := by
  refine disjoint_left.mpr (fun e he hg => ?_)
  obtain ⟨z,hz,heZ⟩ := mem_biUnion.mp hg
  exact disjoint_left.mp (h z hz) he heZ

/-- Removing actual copies charges each deleted edge at most once,
even when it contributes to the degree budget at a core endpoint. -/
theorem capacity_copy_deletion_loss {D Z : Type*}
    (E removed internal : Finset D) (Z₀ : Finset Z) (rows : Z → Finset D)
    (hi : internal ⊆ E) (hr : ∀ z ∈ Z₀, rows z ⊆ E)
    (hInternal : ∀ z ∈ Z₀, Disjoint internal (rows z))
    (hRows : (↑Z₀ : Set Z).PairwiseDisjoint rows) :
    (internal.card:ℝ)-((internal \ removed).card:ℝ) +
      (∑ z ∈ Z₀, (((rows z).card:ℝ)-(((rows z) \ removed).card:ℝ))) ≤
        ((removed ∩ E).card:ℝ) := by
  let R := Z₀.biUnion (fun z => rows z ∩ removed)
  have hD : Disjoint (internal ∩ removed) R := by
    apply disjoint_internal_rows
    intro z hz
    exact (hInternal z hz).mono inter_subset_left inter_subset_left
  have hCount : R.card = ∑ z ∈ Z₀, ((rows z) ∩ removed).card :=
    card_biUnion (fun x hx y hy hxy => (hRows hx hy hxy).mono inter_subset_left inter_subset_left)
  have hSubset : (internal ∩ removed) ∪ R ⊆ removed ∩ E := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_inter.mpr ⟨(mem_inter.mp he).2,hi (mem_inter.mp he).1⟩
    · obtain ⟨z,hz,heZ⟩ := mem_biUnion.mp he
      exact mem_inter.mpr ⟨(mem_inter.mp heZ).2,hr z hz (mem_inter.mp heZ).1⟩
  simp_rw [card_sub_sdiff_eq_inter]
  have h := card_le_card hSubset
  rw [card_union_of_disjoint hD,hCount] at h
  exact_mod_cast h

/-- The coarse capacity bound in §5.1.4 after deleting boundary copies
and copies used by the fine selections. The internal set and the
exceptional rows are the edge-copy sets witnessed in the block. -/
theorem coarse_capacity_after_fine_and_boundary {F D Z : Type*} [Fintype F]
    (E boundary internal : Finset D) (Z₀ : Finset Z)
    (rows : Z → Finset D) (correction preferred : F → Finset D)
    (p₂ lambda₁ lambda₂ : ℝ) (cap : Z → ℝ)
    (hp : 0 < p₂) (hpOne : p₂ ≤ 1) (hLambda₂ : 0 ≤ lambda₂)
    (hPreferred : ∀ i, Disjoint (preferred i) E)
    (hCorrection : ∀ i, ((correction i ∩ E).card:ℝ) ≤ (5/4:ℝ)*lambda₁*E.card)
    (hBoundary : ((boundary ∩ E).card:ℝ) ≤ p₂^2*(E.card:ℝ)/1024)
    (hPalette : (5/4:ℝ)*(Fintype.card F:ℝ)*lambda₁ ≤ p₂^2/1024)
    (hi : internal ⊆ E) (hr : ∀ z ∈ Z₀, rows z ⊆ E)
    (hInternal : ∀ z ∈ Z₀, Disjoint internal (rows z))
    (hRows : (↑Z₀ : Set Z).PairwiseDisjoint rows)
    (hBefore : (13/8:ℝ)*lambda₂*E.card ≤ (64*lambda₂/p₂^2)*internal.card +
      (∑ z ∈ Z₀, min ((64*lambda₂/p₂)*(rows z).card) (cap z))) :
    let removed := boundary ∪ (univ : Finset F).biUnion (fun i => correction i ∪ preferred i)
    (3/2:ℝ)*lambda₂*E.card ≤
      (64*lambda₂/p₂^2)*((internal \ removed).card:ℝ) +
      (∑ z ∈ Z₀, min ((64*lambda₂/p₂)*((rows z \ removed).card:ℝ)) (cap z)) := by
  intro removed
  have hLoss := capacity_copy_deletion_loss E removed internal Z₀ rows hi hr hInternal hRows
  have hBudget := fine_and_boundary_deletion_budget E boundary correction preferred p₂ lambda₁
    hPreferred hCorrection hBoundary hPalette
  exact palette_capacity_retains_three_halves Z₀ internal.card (internal \ removed).card
    p₂ lambda₂ E.card (fun z => (rows z).card) (fun z => (rows z \ removed).card)
    cap hp hpOne hLambda₂ (fun z _ => by exact_mod_cast card_le_card (sdiff_subset (s := rows z)))
    (hLoss.trans hBudget) hBefore

/-- A capacity bound measured in edge copies yields a correction set
of the exact requested size with the individual exceptional caps. -/
theorem exists_capped_correction_copies {D Z : Type*} (internal : Finset D)
    (Z₀ : Finset Z) (rows : Z → Finset D) (cap : Z → ℕ) (request : ℕ)
    (hInternal : ∀ z ∈ Z₀, Disjoint internal (rows z))
    (hRows : (↑Z₀ : Set Z).PairwiseDisjoint rows)
    (hCount : request ≤ internal.card + ∑ z ∈ Z₀, min (rows z).card (cap z)) :
    ∃ selected : Finset D, selected ⊆ internal ∪ Z₀.biUnion rows ∧
      selected.card = request ∧ ∀ z ∈ Z₀, (selected ∩ rows z).card ≤ cap z := by
  classical
  have existsRow (z : Z) : ∃ R ⊆ rows z, R.card = min (rows z).card (cap z) :=
    exists_subset_card_eq (min_le_left _ _)
  choose R hR hCard using existsRow
  let T := internal ∪ Z₀.biUnion R
  have hT : T.card = internal.card + ∑ z ∈ Z₀, min (rows z).card (cap z) := by
    dsimp only [T]
    rw [card_union_of_disjoint (disjoint_internal_rows _ _ _
      (fun z hz => disjoint_of_subset_right (hR z) (hInternal z hz))),
      card_biUnion (fun x hx y hy hxy => (hRows hx hy hxy).mono (hR x) (hR y))]
    simp only [hCard]
  obtain ⟨selected,hS,hSize⟩ := exists_subset_card_eq (hCount.trans_eq hT.symm)
  refine ⟨selected,hS.trans ?_,hSize,?_⟩
  · intro e he
    rcases mem_union.mp he with h | h
    · exact mem_union.mpr (Or.inl h)
    · obtain ⟨z,hz,he⟩ := mem_biUnion.mp h
      exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨z,hz,hR z he⟩))
  · intro z hz
    have hSub : selected ∩ rows z ⊆ R z := by
      intro e he
      obtain ⟨heS,heZ⟩ := mem_inter.mp he
      rcases mem_union.mp (hS heS) with heI | heRows
      · exact (disjoint_left.mp (hInternal z hz) heI heZ).elim
      · obtain ⟨y,hy,heY⟩ := mem_biUnion.mp heRows
        by_cases H : y = z
        · exact H ▸ heY
        · exact (disjoint_left.mp (hRows hy hz H) (hR y heY) heZ).elim
    exact (card_le_card hSub).trans ((hCard z).trans_le (min_le_right _ _))


/-- A fine block loses only copies meeting the boundary. -/
theorem fine_capacity_after_boundary {D Z : Type*}
    (E boundary internal : Finset D) (Z₀ : Finset Z) (rows : Z → Finset D)
    (p lambda : ℝ) (cap : Z → ℝ)
    (hp : 0 < p) (hpOne : p ≤ 1) (hLambda : 0 ≤ lambda)
    (hBoundary : ((boundary ∩ E).card:ℝ) ≤ p^2*(E.card:ℝ)/512)
    (hi : internal ⊆ E) (hr : ∀ z ∈ Z₀, rows z ⊆ E)
    (hInternal : ∀ z ∈ Z₀, Disjoint internal (rows z))
    (hRows : (↑Z₀ : Set Z).PairwiseDisjoint rows)
    (hBefore : (13/8:ℝ)*lambda*E.card ≤ (64*lambda/p^2)*internal.card +
      (∑ z ∈ Z₀, min ((64*lambda/p)*(rows z).card) (cap z))) :
    (3/2:ℝ)*lambda*E.card ≤
      (64*lambda/p^2)*((internal \ boundary).card:ℝ) +
      (∑ z ∈ Z₀, min ((64*lambda/p)*((rows z \ boundary).card:ℝ)) (cap z)) :=
  palette_capacity_retains_three_halves Z₀ internal.card (internal \ boundary).card
    p lambda E.card (fun z => (rows z).card) (fun z => (rows z \ boundary).card)
    cap hp hpOne hLambda (fun z _ => by exact_mod_cast card_le_card (sdiff_subset (s := rows z)))
    ((capacity_copy_deletion_loss E boundary internal Z₀ rows hi hr hInternal hRows).trans hBoundary)
    hBefore

/-- Equation (5.4) makes the positive imbalance fit within the surviving
capacity. The selected copies respect each exceptional vertex's cap. -/
theorem exists_correction_copies_of_palette_bound {D Z : Type*}
    (E internal : Finset D) (Z₀ : Finset Z) (rows : Z → Finset D) (cap : Z → ℕ)
    (p lambda : ℝ) (e eOther : ℕ)
    (hp : 0 < p) (hpOne : p ≤ 1) (hLambda : 0 ≤ lambda)
    (hScale : 64*lambda ≤ p^2)
    (hPalette : (e:ℝ) ≤ (5/4:ℝ)*lambda*E.card)
    (hInternal : ∀ z ∈ Z₀, Disjoint internal (rows z))
    (hRows : (↑Z₀ : Set Z).PairwiseDisjoint rows)
    (hCapacity : (3/2:ℝ)*lambda*E.card ≤ (64*lambda/p^2)*internal.card +
      (∑ z ∈ Z₀, min ((64*lambda/p)*(rows z).card) (cap z))) :
    ∃ selected : Finset D, selected ⊆ internal ∪ Z₀.biUnion rows ∧
      selected.card = e-eOther ∧ ∀ z ∈ Z₀, (selected ∩ rows z).card ≤ cap z := by
  have h₂ : 64*lambda/p^2 ≤ 1 := (div_le_one (by positivity)).mpr hScale
  have h₁ : 64*lambda/p ≤ 1 := by
    apply (div_le_one hp).mpr
    have h := mul_le_mul_of_nonneg_left hpOne hp.le
    nlinarith only [hScale,h]
  have hCard : (64*lambda/p^2)*(internal.card:ℝ) +
      (∑ z ∈ Z₀, min ((64*lambda/p)*((rows z).card:ℝ)) (cap z)) ≤
        ((internal.card + ∑ z ∈ Z₀, min (rows z).card (cap z):ℕ):ℝ) := by
    push_cast
    refine add_le_add (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg (α := ℝ) internal.card)) (sum_le_sum ?_)
    intro z _
    exact min_le_min (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg (α := ℝ) (rows z).card)) le_rfl
  have hReq : ((e-eOther:ℕ):ℝ) ≤ (e:ℝ) := by exact_mod_cast Nat.sub_le e eOther
  have hOrder : (5/4:ℝ)*lambda*E.card ≤ (3/2:ℝ)*lambda*E.card := by
    have h := mul_nonneg hLambda (Nat.cast_nonneg (α := ℝ) E.card)
    linarith only [h]
  apply exists_capped_correction_copies internal Z₀ rows cap (e-eOther) hInternal hRows
  exact_mod_cast hReq.trans (hPalette.trans (hOrder.trans (hCapacity.trans hCard)))


/-- The preferred-edge reserve is at least the number of incidences
still needed under the upper bound in (5.3) and the palette size in (5.2). -/
theorem palette_request_le_preferred_reserve
    (β p theta lambda c : ℝ) (r : ℕ)
    (hβ : 0 ≤ β) (hp : 0 ≤ p) (hpOne : p ≤ 1)
    (hThetaOne : theta ≤ 1) (hc : 0 ≤ c)
    (hPalette : lambda ≤ β*p^2*theta/(2:ℝ)^18) (hRequest : (r:ℝ) ≤ 2*lambda*c) :
    (r:ℝ) ≤ β*p*c/16 := by
  have hpSq : p^2 ≤ p := by
    nlinarith only [mul_le_mul_of_nonneg_left hpOne hp]
  have h₁ : β*p^2*theta ≤ β*p^2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hThetaOne
      (mul_nonneg hβ (sq_nonneg p))
  have h₂ := mul_le_mul_of_nonneg_left hpSq hβ
  have h₃ : 0 ≤ β*p := mul_nonneg hβ hp
  have hLambdaScale : 2*lambda ≤ β*p/16 := by
    norm_num at hPalette
    linarith only [hPalette,h₁,h₂,h₃]
  have h := mul_le_mul_of_nonneg_right hLambdaScale hc
  exact hRequest.trans (by linarith only [h])

/-- Complete one exceptional row to its palette degree using
preferred copies disjoint from the correction copies. -/
theorem exists_preferred_copies_completing_row {D : Type*}
    (correction preferred : Finset D) (r : ℕ)
    (hDisj : Disjoint correction preferred)
    (hCorrection : correction.card ≤ r) (hPreferred : r ≤ preferred.card) :
    ∃ P ⊆ preferred, Disjoint correction P ∧ (correction ∪ P).card = r := by
  classical
  obtain ⟨P,hP,hCard⟩ := exists_subset_card_eq ((Nat.sub_le r correction.card).trans hPreferred)
  have h := disjoint_of_subset_right hP hDisj
  refine ⟨P,hP,h,?_⟩
  rw [card_union_of_disjoint h,hCard]
  omega

/-- The degree-sum calculation of (5.8). The two internal counts and
the four exceptional-to-core counts are those of the original
balanced palette. -/
theorem palette_preferred_degree_imbalance
    (internalA internalB preferredA preferredB oppositeA oppositeB : ℤ)
    (hBalance : 2*internalA+preferredA+oppositeB = 2*internalB+preferredB+oppositeA) :
    (preferredA+oppositeA)-(preferredB+oppositeB) =
      2*((internalB+oppositeA)-(internalA+oppositeB)) := by
  linarith only [hBalance]


/-- Each fine palette uses at most k₁ copies in an exceptional row.
The union therefore costs at most q k₁ copies from any such row. -/
theorem fine_exceptional_row_loss {F D : Type*} [Fintype F]
    (S : Finset D) (fine : F → Finset D) (k₁ : ℕ)
    (hRow : ∀ f, ((fine f) ∩ S).card ≤ k₁) :
    (((univ : Finset F).biUnion fine) ∩ S).card ≤ Fintype.card F*k₁ := by
  have hSet : ((univ : Finset F).biUnion fine) ∩ S =
      (univ : Finset F).biUnion (fun f => fine f ∩ S) := by
    ext e
    simp only [mem_inter, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨⟨f,hf⟩,he⟩
      exact ⟨f,hf,he⟩
    · rintro ⟨f,hf,he⟩
      exact ⟨⟨f,hf⟩,he⟩
  rw [hSet]
  calc
    _ ≤ ∑ f, (fine f ∩ S).card := card_biUnion_le
    _ ≤ ∑ _f : F, k₁ := sum_le_sum (fun f _ => hRow f)
    _ = _ := by simp

/-- A bound on the number of deleted copies in each of two stages
gives a lower bound on the surviving preferred copies. -/
theorem preferred_copies_after_two_deletions {D : Type*}
    (S boundary fine : Finset D) (lower boundaryBudget fineBudget : ℝ)
    (hBefore : lower ≤ (S.card:ℝ))
    (hBoundary : ((S ∩ boundary).card:ℝ) ≤ boundaryBudget)
    (hFine : ((S ∩ fine).card:ℝ) ≤ fineBudget) :
    lower-boundaryBudget-fineBudget ≤ (((S \ boundary) \ fine).card:ℝ) := by
  have hb := card_sub_sdiff_eq_inter S boundary
  have hf := card_sub_sdiff_eq_inter (S \ boundary) fine
  have hSub : (((S \ boundary) ∩ fine).card:ℝ) ≤ ((S ∩ fine).card:ℝ) := by
    exact_mod_cast card_le_card (inter_subset_inter sdiff_subset Subset.rfl)
  linarith only [hb,hf,hSub,hBefore,hBoundary,hFine]

end OverfullWork.ChenShan
