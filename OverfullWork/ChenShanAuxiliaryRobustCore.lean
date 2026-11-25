module

public import OverfullWork.KLOSPartitionAdjustment

@[expose] public section

/-! The expansion argument for the auxiliary core in Chen–Shan, Lemma 3.23. -/
namespace OverfullWork.ChenShan

open SimpleGraph Finset KLOS PrunedCore RobustExpansion
open scoped Classical

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The block calculation in Lemma 3.23. Any block meeting a test set
in at least `3νn` vertices contributes itself and its adjacent blocks
to the robust neighborhood. The hypothesis on missed neighbors allows
for the vertex itself and one deleted edge. -/
theorem auxiliary_expands_of_blocks (f : V → I) (R : I → I → Prop)
    (hBoundary : ∀ A : Finset I, A.Nonempty → A ≠ univ →
      ∃ i ∈ A, ∃ j ∉ A, R i j)
    (L ν τ : ℝ) (hντ : ν ≤ τ)
    (hThreshold : 1 ≤ ν * (Fintype.card V : ℝ))
    (hFind : (Fintype.card I : ℝ) * (3 * (ν * (Fintype.card V : ℝ))) <
      τ * (Fintype.card V : ℝ))
    (hSurplus : (Fintype.card I : ℝ) * (3 * (ν * (Fintype.card V : ℝ))) +
      ν * (Fintype.card V : ℝ) ≤ L)
    (hSize : ∀ i, L ≤ ((assignmentPart f i).card : ℝ))
    (hLocal : ∀ i j, i = j ∨ R i j →
      ∀ v ∈ assignmentPart f j, ∀ T ⊆ assignmentPart f i,
        T.card ≤ neighboursIn G T v + 2) :
    ExpandsInside G ν τ univ := by
  intro S _ hSLo hSHi
  let n := (Fintype.card V : ℝ)
  let t := ν * n
  let B := assignmentPart f
  let good := (univ : Finset I).filter (fun i => 3 * t ≤ ((S ∩ B i).card : ℝ))
  let U := good.biUnion B
  let N := robustNeighbourhoodIn G ν univ S
  have hn : 0 ≤ n := by positivity
  have hGood (i : I) : i ∈ good ↔ 3 * t ≤ ((S ∩ B i).card : ℝ) := by simp [good]
  have hMem (v : V) : v ∈ B (f v) := mem_filter.mpr ⟨mem_univ _, rfl⟩
  have hSmall : (S.card : ℝ) ≤ (U.card : ℝ) + (Fintype.card I : ℝ) * (3 * t) := by
    let rest := goodᶜ.biUnion fun i => S ∩ B i
    have hSub : S \ U ⊆ rest := by
      intro v hv
      obtain ⟨hS, hU⟩ := mem_sdiff.mp hv
      have hfg : f v ∉ good := fun hh => hU (mem_biUnion.mpr ⟨f v, hh, hMem v⟩)
      exact mem_biUnion.mpr ⟨f v, mem_compl.mpr hfg, mem_inter.mpr ⟨hS, hMem v⟩⟩
    have hRest : (rest.card : ℝ) ≤ (Fintype.card I : ℝ) * (3 * t) := by
      have hFirst : (rest.card : ℝ) ≤ ∑ i ∈ goodᶜ, ((S ∩ B i).card : ℝ) := by
        exact_mod_cast (card_biUnion_le (s := goodᶜ) (t := fun i => S ∩ B i))
      calc
        _ ≤ _ := hFirst
        _ ≤ ∑ _ ∈ goodᶜ, 3 * t := sum_le_sum fun i hi =>
          le_of_lt (lt_of_not_ge (fun hh => (mem_compl.mp hi) ((hGood i).mpr hh)))
        _ = (goodᶜ.card : ℝ) * (3 * t) := by simp
        _ ≤ _ := by
          have hle : (goodᶜ.card : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast card_le_univ _
          exact mul_le_mul_of_nonneg_right hle (by linarith only [hThreshold])
    have hDifference : (S.card : ℝ) ≤ ((S \ U).card : ℝ) + U.card := by
      exact_mod_cast (card_le_card_sdiff_add_card (s := S) (t := U))
    have hRestSub : (((S \ U).card : ℕ) : ℝ) ≤ rest.card := by exact_mod_cast card_le_card hSub
    linarith only [hDifference, hRestSub, hRest]
  have hHasGood : good.Nonempty := by
    by_contra h
    have hEmpty : good = ∅ := not_nonempty_iff_eq_empty.mp h
    have hU : U = ∅ := by simp [U, hEmpty]
    rw [hU, card_empty, Nat.cast_zero] at hSmall
    rw [card_univ] at hSLo
    change τ * n ≤ (S.card : ℝ) at hSLo
    change (Fintype.card I : ℝ) * (3 * t) < τ * n at hFind
    linarith only [hSmall, hSLo, hFind]
  have hBlock (i : I) (hi : i ∈ good) (j : I) (hij : i = j ∨ R i j) : B j ⊆ N := by
    intro v hv
    have hNear := hLocal i j hij v hv (S ∩ B i) inter_subset_right
    have hNearR : ((S ∩ B i).card : ℝ) ≤ (neighboursIn G (S ∩ B i) v : ℝ) + 2 := by
      exact_mod_cast hNear
    have hMono : (neighboursIn G (S ∩ B i) v : ℝ) ≤ neighboursIn G S v := by
      exact_mod_cast neighboursIn_mono G inter_subset_left v
    have hThreshold' : t ≤ (neighboursIn G S v : ℝ) := by
      have hCount := (hGood i).mp hi
      change 1 ≤ t at hThreshold
      linarith only [hCount, hNearR, hMono, hThreshold]
    exact mem_filter.mpr ⟨mem_univ _, by simpa only [card_univ] using hThreshold'⟩
  have hInside : U ⊆ N := by
    intro v hv
    obtain ⟨i, hi, hv⟩ := mem_biUnion.mp hv
    exact hBlock i hi i (Or.inl rfl) hv
  change (S.card : ℝ) + ν * (univ : Finset V).card ≤ N.card
  rw [card_univ]
  by_cases hAll : good = univ
  · have hAllN : N = univ := by
      apply eq_univ_of_forall
      intro v
      have hfv : f v ∈ good := hAll.symm ▸ mem_univ _
      exact hBlock (f v) hfv (f v) (Or.inl rfl) (hMem v)
    rw [card_univ] at hSHi
    rw [hAllN, card_univ]
    have hτn := mul_le_mul_of_nonneg_right hντ hn
    nlinarith only [hτn, hSHi]
  · obtain ⟨i, hi, j, hj, hij⟩ := hBoundary good hHasGood hAll
    have hDis : Disjoint U (B j) := by
      apply Finset.disjoint_left.mpr
      intro v hv hu
      obtain ⟨k, hk, hv⟩ := mem_biUnion.mp hv
      have hk' : f v = k := (mem_filter.mp hv).2
      have hj' : f v = j := (mem_filter.mp hu).2
      exact hj (hk'.symm.trans hj' ▸ hk)
    have hUnion : U ∪ B j ⊆ N := union_subset hInside (hBlock i hi j (Or.inr hij))
    have hCountNat := card_le_card hUnion
    rw [card_union_of_disjoint hDis] at hCountNat
    have hCount : (U.card : ℝ) + ((B j).card : ℝ) ≤ N.card := by exact_mod_cast hCountNat
    change (Fintype.card I : ℝ) * (3 * t) + t ≤ L at hSurplus
    change (S.card : ℝ) + t ≤ N.card
    linarith only [hCount, hSmall, hSize j, hSurplus]

omit [Fintype I] in
private theorem walk_leaves_blocks (J : SimpleGraph I) (A : Finset I)
    {x y : I} (p : J.Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ i ∈ A, ∃ j ∉ A, J.Adj i j := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y hAdj p ih =>
    by_cases hz : z ∈ A
    · exact ih hz hy
    · exact ⟨x, hx, z, hz, hAdj⟩

/-- A connected block graph supplies the boundary step of the expansion
argument. Between adjacent blocks the base graph contains every pair,
and within a block it contains every distinct pair. -/
theorem auxiliary_expands_after_one_deletion (Base : SimpleGraph V) [DecidableRel Base.Adj]
    (J : SimpleGraph I) (hConnected : J.Preconnected) (f : V → I)
    (L ν τ : ℝ) (hντ : ν ≤ τ)
    (hThreshold : 1 ≤ ν * (Fintype.card V : ℝ))
    (hFind : (Fintype.card I : ℝ) * (3 * (ν * (Fintype.card V : ℝ))) <
      τ * (Fintype.card V : ℝ))
    (hSurplus : (Fintype.card I : ℝ) * (3 * (ν * (Fintype.card V : ℝ))) +
      ν * (Fintype.card V : ℝ) ≤ L)
    (hSize : ∀ i, L ≤ ((assignmentPart f i).card : ℝ))
    (hBase : ∀ v w, (f w = f v ∨ J.Adj (f w) (f v)) → v ≠ w → Base.Adj v w)
    (hDelete : ∀ v, ((univ : Finset V).filter (fun w => Base.Adj v w ∧ ¬ G.Adj v w)).card ≤ 1) :
    ExpandsInside G ν τ univ := by
  refine auxiliary_expands_of_blocks G f J.Adj ?_ L ν τ hντ hThreshold hFind hSurplus hSize ?_
  · intro A hNonempty hProper
    obtain ⟨x, hx⟩ := hNonempty
    have hNot : ¬ ∀ y : I, y ∈ A := fun h => hProper (eq_univ_of_forall h)
    obtain ⟨y, hy⟩ := not_forall.mp hNot
    obtain ⟨p⟩ := hConnected x y
    exact walk_leaves_blocks J A p hx hy
  · intro i j hij v hv T hT
    let lost := (univ : Finset V).filter (fun w => Base.Adj v w ∧ ¬ G.Adj v w)
    let kept := T.filter (fun w => G.Adj v w)
    have hCover : T ⊆ kept ∪ insert v lost := by
      intro w hw
      by_cases hg : G.Adj v w
      · exact mem_union_left _ (mem_filter.mpr ⟨hw, hg⟩)
      · by_cases he : v = w
        · exact mem_union_right _ (mem_insert.mpr (Or.inl he.symm))
        · have hi : f w = i := (mem_filter.mp (hT hw)).2
          have hj : f v = j := (mem_filter.mp hv).2
          have hf : f w = f v ∨ J.Adj (f w) (f v) := by simpa only [hi, hj] using hij
          exact mem_union_right _ (mem_insert.mpr (Or.inr
            (mem_filter.mpr ⟨mem_univ _, hBase v w hf he, hg⟩)))
    have hCount := (card_le_card hCover).trans (card_union_le kept (insert v lost))
    have hInsert := card_insert_le v lost
    have hl : lost.card ≤ 1 := hDelete v
    have hk : kept.card = neighboursIn G T v := (neighboursIn_eq_filter_card G T v).symm
    omega


/-- The two numerical bounds in the block proof hold simultaneously for
all sufficiently large orders. -/
theorem exists_auxiliary_block_parameters (m : ℕ) (hm : 0 < m) (τ : ℝ) (hτ : 0 < τ) :
    ∃ ν : ℝ, 0 < ν ∧ ν ≤ τ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      1 ≤ ν * (n : ℝ) ∧
        (m : ℝ) * (3 * (ν * (n : ℝ))) < τ * (n : ℝ) ∧
        (m : ℝ) * (3 * (ν * (n : ℝ))) + ν * (n : ℝ) ≤ (n : ℝ) / (2 * (m : ℝ)) := by
  let a : ℝ := m
  have ha : 1 ≤ a := by
    change (1 : ℝ) ≤ (m : ℝ)
    exact_mod_cast hm
  let ν : ℝ := min (τ / (6 * a)) (1 / (16 * a ^ 2))
  have hν : 0 < ν := lt_min (by positivity) (by positivity)
  have ha6 : 0 < 6 * a := by positivity
  have ha16 : 0 < 16 * a ^ 2 := by positivity
  have hFirst : ν * (6 * a) ≤ τ :=
    (le_div_iff₀ ha6).mp (min_le_left _ _)
  have hSecond : ν * (16 * a ^ 2) ≤ 1 :=
    (le_div_iff₀ ha16).mp (min_le_right _ _)
  have hντ : ν ≤ τ := by
    calc
      ν = ν * 1 := by ring
      _ ≤ ν * (6 * a) := mul_le_mul_of_nonneg_left (by linarith) hν.le
      _ ≤ τ := hFirst
  refine ⟨ν, hν, hντ, ⌈1 / ν⌉₊, ?_⟩
  intro n hn
  let b : ℝ := n
  have hb : 1 / ν ≤ b :=
    (Nat.le_ceil (1 / ν)).trans (by
      change (↑⌈1 / ν⌉₊ : ℝ) ≤ (n : ℝ)
      exact_mod_cast hn)
  have hThreshold : 1 ≤ ν * b := by
    simpa only [mul_comm] using (div_le_iff₀ hν).mp hb
  have hbPos : 0 < b := (by positivity : 0 < 1 / ν).trans_le hb
  have hSmall : a * (3 * ν) < τ := by linarith only [hFirst, hτ]
  have hDenom : 0 < 2 * a := by positivity
  have hBudget : (3 * a + 1) * (2 * a) ≤ 16 * a ^ 2 := by
    have h := mul_nonneg (show 0 ≤ 2 * a by positivity) (show 0 ≤ 5 * a - 1 by linarith)
    nlinarith only [h]
  have hCoeff : ν * ((3 * a + 1) * (2 * a)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hBudget hν.le).trans hSecond
  change 1 ≤ ν * b ∧ a * (3 * (ν * b)) < τ * b ∧
    a * (3 * (ν * b)) + ν * b ≤ b / (2 * a)
  refine ⟨hThreshold, ?_, (le_div_iff₀ hDenom).mpr ?_⟩
  · convert mul_lt_mul_of_pos_right hSmall hbPos using 1 <;> ring
  · convert mul_le_mul_of_nonneg_right hCoeff hbPos.le using 1
    · ring
    · rw [one_mul]

end OverfullWork.ChenShan
