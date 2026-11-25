module

public import OverfullWork.KLOSRobustComponents

@[expose] public section

/-! The refinement and stopping argument of Kühn–Lo–Osthus–Staden,
§4.5. A step increases the potential even if it only marks a part. -/
namespace OverfullWork.KLOS

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure SparsePartition (ρ : ℝ) where
  parts : Finset (Finset V)
  cover : parts.biUnion id = univ
  disjoint : ∀ X ∈ parts, ∀ Y ∈ parts, X ≠ Y → Disjoint X Y
  sparse : ∀ X ∈ parts, IsSparseComponent G ρ X

def NearlyBipartite (ρ : ℝ) (U : Finset V) : Prop :=
  ∃ A B : Finset V, A ∪ B = U ∧ CloseToBipartite G ρ A B

noncomputable def markedParts {ρ : ℝ} (P : SparsePartition G ρ) : Finset (Finset V) :=
  P.parts.filter (NearlyBipartite G ρ)

noncomputable def refinementPotential {ρ : ℝ} (P : SparsePartition G ρ) : ℕ :=
  2 * P.parts.card + (markedParts G P).card

def IsTerminal {ρ : ℝ} (P : SparsePartition G ρ) (ν τ : ℝ) : Prop :=
  ∀ U ∈ P.parts, ExpandsInside G ν τ U ∨
    ∃ A B : Finset V, A ∪ B = U ∧ CloseToBipartite G ρ A B ∧ ExpandsAcross G ν τ A B

private theorem nonempty_of_sparse {ρ : ℝ} (hρ : 0 < ρ) (hn : 0 < Fintype.card V)
    {X : Finset V} (hX : IsSparseComponent G ρ X) : X.Nonempty := by
  apply card_pos.mp
  exact_mod_cast ((mul_pos (Real.sqrt_pos.mpr hρ)
    (by exact_mod_cast hn : (0 : ℝ) < Fintype.card V)).trans_le hX.1)

private theorem replacePart {ρ ρ' : ℝ} (P : SparsePartition G ρ)
    (hρ' : 0 < ρ') (hn : 0 < Fintype.card V)
    (hKeep : ∀ X ∈ P.parts, IsSparseComponent G ρ' X)
    {U X Y : Finset V} (hU : U ∈ P.parts) (hXY : Disjoint X Y)
    (hUnion : X ∪ Y = U) (hX : IsSparseComponent G ρ' X) (hY : IsSparseComponent G ρ' Y) :
    ∃ Q : SparsePartition G ρ', Q.parts = insert X (insert Y (P.parts.erase U)) ∧
      Q.parts.card = P.parts.card + 1 := by
  have hx := nonempty_of_sparse G hρ' hn hX
  have hy := nonempty_of_sparse G hρ' hn hY
  have hxU : X ⊆ U := hUnion ▸ subset_union_left
  have hyU : Y ⊆ U := hUnion ▸ subset_union_right
  have fresh (Z : Finset V) (hZ : Z ⊆ U) (hne : Z.Nonempty) : Z ∉ P.parts.erase U := by
    intro hm
    obtain ⟨hzu, hz⟩ := mem_erase.mp hm
    have hd := (P.disjoint Z hz U hU hzu).mono_right hZ
    obtain ⟨z, hz⟩ := hne
    exact Finset.disjoint_left.mp hd hz hz
  have hne : X ≠ Y := by
    intro h
    obtain ⟨x, hxmem⟩ := hx
    exact Finset.disjoint_left.mp hXY hxmem (h ▸ hxmem)
  have hCover : (insert X (insert Y (P.parts.erase U))).biUnion id = univ := by
    ext v
    simp only [mem_biUnion, mem_insert, mem_erase, id_eq, mem_univ, iff_true]
    have hv : v ∈ P.parts.biUnion id := by rw [P.cover]; exact mem_univ v
    obtain ⟨Z, hz, hvz⟩ := mem_biUnion.mp hv
    by_cases he : Z = U
    · simp only [id_eq, he, ← hUnion, mem_union] at hvz
      rcases hvz with hvx | hvy
      · exact ⟨X, Or.inl rfl, hvx⟩
      · exact ⟨Y, Or.inr (Or.inl rfl), hvy⟩
    · exact ⟨Z, Or.inr (Or.inr ⟨he, hz⟩), hvz⟩
  have hDisj : ∀ A ∈ insert X (insert Y (P.parts.erase U)),
      ∀ B ∈ insert X (insert Y (P.parts.erase U)), A ≠ B → Disjoint A B := by
    intro A hA B hB hab
    have aux (Z : Finset V) (hz : Z ∈ P.parts.erase U) : Disjoint U Z :=
      P.disjoint U hU Z (mem_erase.mp hz).2 (Ne.symm (mem_erase.mp hz).1)
    simp only [mem_insert] at hA hB
    rcases hA with rfl | rfl | hA <;> rcases hB with rfl | rfl | hB
    · exact (hab rfl).elim
    · exact hXY
    · exact (aux _ hB).mono_left hxU
    · exact hXY.symm
    · exact (hab rfl).elim
    · exact (aux _ hB).mono_left hyU
    · exact ((aux _ hA).mono_left hxU).symm
    · exact ((aux _ hA).mono_left hyU).symm
    · exact P.disjoint _ (mem_erase.mp hA).2 _ (mem_erase.mp hB).2 hab
  refine ⟨⟨_, hCover, hDisj, ?_⟩, rfl, ?_⟩
  · intro Z hz
    simp only [mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · exact hX
    · exact hY
    · exact hKeep _ (mem_erase.mp hz).2
  · rw [card_insert_of_notMem (by simp [hne, fresh X hxU hx]),
      card_insert_of_notMem (fresh Y hyU hy), card_erase_of_mem hU]
    have hp := card_pos.mpr ⟨U, hU⟩
    omega

private theorem potential_lt_of_replace {ρ ρ' : ℝ}
    (P : SparsePartition G ρ) (Q : SparsePartition G ρ') {U X Y : Finset V}
    (hQ : Q.parts = insert X (insert Y (P.parts.erase U)))
    (hCard : Q.parts.card = P.parts.card + 1)
    (hMark : ∀ Z, NearlyBipartite G ρ Z → NearlyBipartite G ρ' Z) :
    refinementPotential G P < refinementPotential G Q := by
  have hSub : (markedParts G P).erase U ⊆ markedParts G Q := by
    intro Z hz
    obtain ⟨hne, hm⟩ := mem_erase.mp hz
    obtain ⟨hp, hb⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨by rw [hQ]; simp [hne, hp], hMark _ hb⟩
  have hh := card_le_card hSub
  have he : (markedParts G P).card ≤ ((markedParts G P).erase U).card + 1 := by
    by_cases h : U ∈ markedParts G P
    · have hp := card_pos.mpr ⟨U, h⟩
      rw [card_erase_of_mem h]
      omega
    · rw [erase_eq_of_notMem h]
      omega
  unfold refinementPotential
  omega

/-- One application of the two splitting lemmas, with their parameters
supplied by the caller. -/
theorem terminal_or_refine {ρ ρ' ν τ : ℝ} (P : SparsePartition G ρ)
    (hρ' : 0 < ρ') (hn : 0 < Fintype.card V)
    (hKeep : ∀ X ∈ P.parts, IsSparseComponent G ρ' X)
    (hMark : ∀ X, NearlyBipartite G ρ X → NearlyBipartite G ρ' X)
    (hOrd : ∀ U ∈ P.parts, ¬ ExpandsInside G ν τ U →
      (∃ X Y : Finset V, Disjoint X Y ∧ X ∪ Y = U ∧
        IsSparseComponent G ρ' X ∧ IsSparseComponent G ρ' Y) ∨ NearlyBipartite G ρ' U)
    (hBip : ∀ A B : Finset V, CloseToBipartite G ρ A B → ¬ ExpandsAcross G ν τ A B →
      ∃ X Y : Finset V, Disjoint X Y ∧ X ∪ Y = A ∪ B ∧
        IsSparseComponent G ρ' X ∧ IsSparseComponent G ρ' Y) :
    IsTerminal G P ν τ ∨ ∃ Q : SparsePartition G ρ',
      refinementPotential G P < refinementPotential G Q := by
  by_cases hT : IsTerminal G P ν τ
  · exact Or.inl hT
  right
  unfold IsTerminal at hT
  push Not at hT
  obtain ⟨U, hU, hNotOrd, hNotBip⟩ := hT
  have split (X Y : Finset V) (hd : Disjoint X Y) (hu : X ∪ Y = U)
      (hx : IsSparseComponent G ρ' X) (hy : IsSparseComponent G ρ' Y) :
      ∃ Q : SparsePartition G ρ', refinementPotential G P < refinementPotential G Q := by
    obtain ⟨Q, hQ, hc⟩ := replacePart G P hρ' hn hKeep hU hd hu hx hy
    exact ⟨Q, potential_lt_of_replace G P Q hQ hc hMark⟩
  by_cases hm : NearlyBipartite G ρ U
  · obtain ⟨A, B, hab, hClose⟩ := hm
    obtain ⟨X, Y, hd, hu, hx, hy⟩ := hBip A B hClose (hNotBip A B hab hClose)
    exact split X Y hd (hu.trans hab) hx hy
  · rcases hOrd U hU hNotOrd with ⟨X, Y, hd, hu, hx, hy⟩ | hNew
    · exact split X Y hd hu hx hy
    · let Q : SparsePartition G ρ' := ⟨P.parts, P.cover, P.disjoint, hKeep⟩
      have hSub : insert U (markedParts G P) ⊆ markedParts G Q := by
        intro Z hz
        rcases mem_insert.mp hz with rfl | hz
        · exact mem_filter.mpr ⟨hU, hNew⟩
        · exact mem_filter.mpr ⟨(mem_filter.mp hz).1, hMark _ (mem_filter.mp hz).2⟩
      have hFresh : U ∉ markedParts G P := fun h => hm (mem_filter.mp h).2
      have hh := card_le_card hSub
      rw [card_insert_of_notMem hFresh] at hh
      refine ⟨Q, ?_⟩
      unfold refinementPotential
      change 2 * P.parts.card + (markedParts G P).card < 2 * P.parts.card + (markedParts G Q).card
      omega

/-- The component size lower bound gives a uniform bound for the potential. -/
theorem potential_bound {ρ : ℝ} (P : SparsePartition G ρ) (m : ℕ)
    (hm : ∀ X ∈ P.parts, Fintype.card V ≤ m * X.card) (hn : 0 < Fintype.card V) :
    refinementPotential G P ≤ 3 * m := by
  have hsum : ∑ X ∈ P.parts, X.card = Fintype.card V := by
    calc
      _ = (P.parts.biUnion id).card := (card_biUnion (s := P.parts) (t := id) P.disjoint).symm
      _ = _ := by rw [P.cover, card_univ]
  have h : P.parts.card * Fintype.card V ≤ m * Fintype.card V := by
    calc
      _ = ∑ _ ∈ P.parts, Fintype.card V := by simp
      _ ≤ ∑ X ∈ P.parts, m * X.card := sum_le_sum hm
      _ = _ := by rw [← mul_sum, hsum]
  have hh := Nat.le_of_mul_le_mul_right h hn
  have hMarked := card_le_card (filter_subset (NearlyBipartite G ρ) P.parts)
  unfold refinementPotential markedParts
  omega

/-- The weighted count in (4.13). A part tagged bipartite is counted twice;
its two sides each have size at least `minDegree - 2 * √ρ * n`. -/
theorem weighted_part_count {ρ : ℝ} (P : SparsePartition G ρ)
    (bipartite : Finset (Finset V)) (hSub : bipartite ⊆ P.parts)
    (hBip : ∀ U ∈ bipartite, NearlyBipartite G ρ U)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V) :
    ((P.parts.card : ℝ) + (bipartite.card : ℝ)) *
        ((G.minDegree : ℝ) - 2 * Real.sqrt ρ * (Fintype.card V : ℝ)) ≤
      (Fintype.card V : ℝ) := by
  let n := (Fintype.card V : ℝ)
  let lower := (G.minDegree : ℝ) - 2 * Real.sqrt ρ * n
  have hsum : ∑ U ∈ P.parts, (U.card : ℝ) = n := by
    have hNat : ∑ U ∈ P.parts, U.card = Fintype.card V := by
      calc
        _ = (P.parts.biUnion id).card := (card_biUnion (s := P.parts) (t := id) P.disjoint).symm
        _ = _ := by rw [P.cover, card_univ]
    dsimp only [n]
    exact_mod_cast hNat
  have hOrd (U : Finset V) (hU : U ∈ P.parts) : lower ≤ (U.card : ℝ) := by
    have h := sparseComponent_card_lower G ρ U hρ hn (P.sparse U hU)
    have hCost : 0 ≤ Real.sqrt ρ * n := by positivity
    change (G.minDegree : ℝ) - Real.sqrt ρ * n ≤ (U.card : ℝ) at h
    dsimp only [lower]
    linarith only [h, hCost]
  have hDouble (U : Finset V) (hU : U ∈ bipartite) : 2 * lower ≤ (U.card : ℝ) := by
    obtain ⟨A, B, hab, hClose⟩ := hBip U hU
    obtain ⟨ha, hb⟩ := bipartite_sides_lower G ρ A B hρ hn hClose
    have hSize : (U.card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
      rw [← hab, card_union_of_disjoint hClose.1, Nat.cast_add]
    change lower ≤ (A.card : ℝ) at ha
    change lower ≤ (B.card : ℝ) at hb
    linarith only [ha, hb, hSize]
  have h₁ : ((P.parts \ bipartite).card : ℝ) * lower ≤
      ∑ U ∈ P.parts \ bipartite, (U.card : ℝ) := by
    calc
      _ = ∑ _ ∈ P.parts \ bipartite, lower := by simp
      _ ≤ _ := sum_le_sum fun U hU => hOrd U (mem_sdiff.mp hU).1
  have h₂ : (bipartite.card : ℝ) * (2 * lower) ≤ ∑ U ∈ bipartite, (U.card : ℝ) := by
    calc
      _ = ∑ _ ∈ bipartite, 2 * lower := by simp
      _ ≤ _ := sum_le_sum hDouble
  have hCard : (((P.parts \ bipartite).card : ℕ) : ℝ) + (bipartite.card : ℝ) =
      (P.parts.card : ℝ) := by
    exact_mod_cast card_sdiff_add_card_eq_card hSub
  have hSplit : (∑ U ∈ P.parts \ bipartite, (U.card : ℝ)) +
      (∑ U ∈ bipartite, (U.card : ℝ)) = n := by
    rw [sum_sdiff hSub, hsum]
  change ((P.parts.card : ℝ) + (bipartite.card : ℝ)) * lower ≤ n
  nlinarith only [h₁, h₂, hSplit, congrArg (fun x : ℝ => x * lower) hCard]

/-- The weighted component-count bound in (D6), with explicit slack. -/
theorem weighted_part_count_le {ρ : ℝ} (P : SparsePartition G ρ)
    (bipartite : Finset (Finset V)) (hSub : bipartite ⊆ P.parts)
    (hBip : ∀ U ∈ bipartite, NearlyBipartite G ρ U)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V)
    (α ε : ℝ) (hε : 0 ≤ ε) (hDense : α * (Fintype.card V : ℝ) ≤ G.minDegree)
    (hSlack : 2 * Real.sqrt ρ * (1 + ε) ≤ ε * α) :
    ((P.parts.card : ℝ) + (bipartite.card : ℝ)) * (G.minDegree : ℝ) ≤
      (1 + ε) * (Fintype.card V : ℝ) := by
  let n := (Fintype.card V : ℝ)
  let m := (P.parts.card : ℝ) + (bipartite.card : ℝ)
  have hn₀ : 0 ≤ n := by positivity
  have hm₀ : 0 ≤ m := by positivity
  have hSlack' := mul_le_mul_of_nonneg_right hSlack hn₀
  have hDense' := mul_le_mul_of_nonneg_left hDense hε
  have h : (G.minDegree : ℝ) ≤ ((G.minDegree : ℝ) - 2 * Real.sqrt ρ * n) * (1 + ε) := by
    change α * n ≤ (G.minDegree : ℝ) at hDense
    nlinarith only [hSlack', hDense']
  have hCount := weighted_part_count G P bipartite hSub hBip hρ hn
  change m * ((G.minDegree : ℝ) - 2 * Real.sqrt ρ * n) ≤ n at hCount
  calc
    m * (G.minDegree : ℝ) ≤ m * (((G.minDegree : ℝ) - 2 * Real.sqrt ρ * n) * (1 + ε)) :=
      mul_le_mul_of_nonneg_left h hm₀
    _ = (1 + ε) * (m * ((G.minDegree : ℝ) - 2 * Real.sqrt ρ * n)) := by ring
    _ ≤ (1 + ε) * n := mul_le_mul_of_nonneg_left hCount (by positivity)

/-- Finite iteration up to the potential bound. The schedule can assign
different errors and expansion thresholds to successive refinements. -/
theorem exists_terminal_on_schedule (ρ ν : ℕ → ℝ) (τ : ℝ) (B : ℕ)
    (start : SparsePartition G (ρ 0)) (hStart : 0 < refinementPotential G start)
    (hBound : ∀ i ≤ B, ∀ P : SparsePartition G (ρ i), refinementPotential G P ≤ B)
    (hStep : ∀ i < B, ∀ P : SparsePartition G (ρ i),
      IsTerminal G P (ν i) τ ∨ ∃ Q : SparsePartition G (ρ (i + 1)),
        refinementPotential G P < refinementPotential G Q) :
    ∃ i < B, ∃ P : SparsePartition G (ρ i), IsTerminal G P (ν i) τ := by
  by_contra! hNo
  have hRun : ∀ i ≤ B, ∃ P : SparsePartition G (ρ i), i < refinementPotential G P := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨start, hStart⟩
    | succ i ih =>
      intro hi
      have hi' : i < B := by omega
      obtain ⟨P, hp⟩ := ih (by omega)
      rcases hStep i hi' P with hT | ⟨Q, hq⟩
      · exact (hNo i hi' P hT).elim
      · exact ⟨Q, by omega⟩
  obtain ⟨P, hp⟩ := hRun B le_rfl
  exact (not_lt_of_ge (hBound B le_rfl P)) hp

universe u

private def RefinementAt (α τ ρ ν ρ' : ℝ) : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (D : ℕ), 0 < Fintype.card W → (∀ v, H.degree v = D) →
    α * (Fintype.card W : ℝ) ≤ D → ∀ P : SparsePartition H ρ,
    IsTerminal H P ν τ ∨ ∃ Q : SparsePartition H ρ',
      refinementPotential H P < refinementPotential H Q

private theorem exists_refinement_input (α τ ρ' : ℝ) (Q : ℝ → ℝ → Prop)
    (hPick : ∀ ν : ℝ, 0 < ν → ν ≤ τ → ∃ c : ℝ, 0 < c ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ c → Q ρ ν)
    (hα : 0 < α) (hαOne : α ≤ 1) (hτ : 0 < τ) (hτOne : τ ≤ 1)
    (hρ' : 0 < ρ') (hρ'One : ρ' ≤ 1) (hScale : 4 * Real.sqrt ρ' ≤ τ * α) :
    ∃ ρ ν : ℝ, 0 < ρ ∧ ρ ≤ ρ' ∧ Q ρ ν ∧ RefinementAt.{u} α τ ρ ν ρ' := by
  obtain ⟨a, ha, hOrd⟩ := exists_nonexpanding_split_scale.{u} α τ ρ' hα hτ hτOne hρ' hρ'One hScale
  obtain ⟨b, hb, hBip⟩ := exists_bipartite_split_scale.{u} α τ ρ' hα hαOne hτ hτOne hρ' hScale
  let ν := min τ (min a b)
  have hν : 0 < ν := lt_min hτ (lt_min ha hb)
  obtain ⟨c, hc, hQ⟩ := hPick ν hν (min_le_left _ _)
  let ρ := min ρ' (min c (min ν ((α * ν / 2) ^ 2)))
  have hρ : 0 < ρ := lt_min hρ' (lt_min hc (lt_min hν (by positivity)))
  have hMono : ρ ≤ ρ' := min_le_left _ _
  have hCut : ρ ≤ c := (min_le_right _ _).trans (min_le_left _ _)
  have hρν : ρ ≤ ν := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hρb : ρ ≤ (α * ν / 2) ^ 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ρ, ν, hρ, hMono, hQ ρ hρ hCut, ?_⟩
  intro W _ _ H _ D hn hReg hDense P
  have : Nonempty W := Fintype.card_pos_iff.mp hn
  have hMin : D ≤ H.minDegree := H.le_minDegree_of_forall_le_degree D (fun v => (hReg v).ge)
  have hThree : 3 * Real.sqrt ρ' * (Fintype.card W : ℝ) ≤ H.minDegree := by
    have hτα : τ * α ≤ α := by simpa using mul_le_mul_of_nonneg_right hτOne hα.le
    have hs : 3 * Real.sqrt ρ' ≤ α := by linarith only [hScale, hτα, Real.sqrt_nonneg ρ']
    exact (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)).trans
      (hDense.trans (by exact_mod_cast hMin))
  refine terminal_or_refine H P hρ' hn ?_ ?_ ?_ ?_
  · intro X hX
    have hTwo : 2 * Real.sqrt ρ' * (Fintype.card W : ℝ) ≤ H.minDegree := by
      have hs := mul_nonneg (Real.sqrt_nonneg ρ') (Nat.cast_nonneg (α := ℝ) (Fintype.card W))
      linarith only [hs, hThree]
    exact sparseComponent_relax H X ρ ρ' hρ hn hMono hTwo (P.sparse X hX)
  · rintro X ⟨A, B, hX, hClose⟩
    exact ⟨A, B, hX, closeToBipartite_relax H A B ρ ρ' hρ hn hMono hThree hClose⟩
  · intro X hX hNot
    exact hOrd ν ρ ((min_le_right _ _).trans (min_le_left _ _)) hρ hρν H D X hn hReg hDense (P.sparse X hX) hNot
  · intro A B hClose hNot
    exact hBip ν ρ ((min_le_right _ _).trans (min_le_right _ _)) hρ hρb hν H D A B hn hReg hDense hClose hNot

private theorem exists_refinement_schedule (α τ r : ℝ) (B : ℕ) (Q : ℝ → ℝ → Prop)
    (hPick : ∀ ν : ℝ, 0 < ν → ν ≤ τ → ∃ c : ℝ, 0 < c ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ c → Q ρ ν)
    (hα : 0 < α) (hαOne : α ≤ 1) (hτ : 0 < τ) (hτOne : τ ≤ 1)
    (hr : 0 < r) (hrOne : r ≤ 1) (hScale : 4 * Real.sqrt r ≤ τ * α) :
    ∃ ρ ν : ℕ → ℝ, (∀ i, 0 < ρ i ∧ ρ i ≤ r) ∧
      ∀ i < B, Q (ρ i) (ν i) ∧ RefinementAt.{u} α τ (ρ i) (ν i) (ρ (i + 1)) := by
  induction B with
  | zero =>
    exact ⟨fun _ => r, fun _ => r, fun _ => ⟨hr, le_rfl⟩, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ B ih =>
    obtain ⟨ρ, ν, hρ, hStep⟩ := ih
    obtain ⟨ρ₀, ν₀, hp, hMono, hQ, hRoot⟩ := exists_refinement_input.{u} α τ (ρ 0) Q hPick
      hα hαOne hτ hτOne (hρ 0).1 ((hρ 0).2.trans hrOne) (by
        have h := Real.sqrt_le_sqrt (hρ 0).2
        linarith only [h, hScale])
    refine ⟨(fun i => Nat.casesOn i ρ₀ ρ), (fun i => Nat.casesOn i ν₀ ν), ?_, ?_⟩
    · intro i
      cases i with
      | zero => exact ⟨hp, hMono.trans (hρ 0).2⟩
      | succ i => exact hρ i
    · intro i hi
      cases i with
      | zero => exact ⟨hQ, hRoot⟩
      | succ i => exact hStep i (by omega)

/-- The finite, graph-independent schedule from §4.5. At each stage one can
impose any further condition that holds for all sufficiently small input
errors at the expansion threshold of that stage. -/
theorem exists_regular_prepartition_with (α τ r : ℝ) (Q : ℝ → ℝ → Prop)
    (hPick : ∀ ν : ℝ, 0 < ν → ν ≤ τ → ∃ c : ℝ, 0 < c ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ c → Q ρ ν)
    (hα : 0 < α) (hαOne : α ≤ 1) (hτ : 0 < τ) (hτOne : τ ≤ 1)
    (hr : 0 < r) (hrOne : r ≤ 1) (hScale : 4 * Real.sqrt r ≤ τ * α) :
    ∃ B : ℕ, ∃ ρ ν : ℕ → ℝ, (∀ i, 0 < ρ i ∧ ρ i ≤ r) ∧
      (∀ i < B, Q (ρ i) (ν i)) ∧ ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
        (D : ℕ), 0 < Fintype.card W → (∀ v, H.degree v = D) →
        α * (Fintype.card W : ℝ) ≤ D →
        ∃ i < B, ∃ P : SparsePartition H (ρ i), IsTerminal H P (ν i) τ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / α)
  have hmα : 2 ≤ (m : ℝ) * α := (div_lt_iff₀ hα).mp hm |>.le
  obtain ⟨ρ, ν, hρ, hSchedule⟩ := exists_refinement_schedule.{u} α τ r (3 * m) Q hPick
    hα hαOne hτ hτOne hr hrOne hScale
  refine ⟨3 * m, ρ, ν, hρ, fun i hi => (hSchedule i hi).1, ?_⟩
  intro W _ _ H _ D hn hRegular hDense
  let n := (Fintype.card W : ℝ)
  have hnR : (0 : ℝ) ≤ n := by positivity
  have : Nonempty W := Fintype.card_pos_iff.mp hn
  have hMin : (D : ℝ) ≤ H.minDegree := by
    exact_mod_cast H.le_minDegree_of_forall_le_degree D (fun v => (hRegular v).ge)
  let start : SparsePartition H (ρ 0) := {
    parts := {univ}
    cover := by simp
    disjoint := by simp
    sparse := by
      intro X hX
      have hX' : X = univ := mem_singleton.mp hX
      subst X
      have hRoot : Real.sqrt (ρ 0) ≤ 1 := by
        simpa using Real.sqrt_le_sqrt ((hρ 0).2.trans hrOne)
      refine ⟨?_, ?_⟩
      · rw [card_univ]
        simpa using mul_le_mul_of_nonneg_right hRoot hnR
      · have hCut : OddCutDeficit.cutEdges H univ = 0 := by
          simp [OddCutDeficit.cutEdges, OddCutDeficit.crossingEdges]
        rw [hCut, Nat.cast_zero]
        exact mul_nonneg (hρ 0).1.le (sq_nonneg _) }
  refine exists_terminal_on_schedule H ρ ν τ (3 * m) start ?_ ?_ ?_
  · change 0 < 2 * ({(univ : Finset W)} : Finset (Finset W)).card + (markedParts H start).card
    simp
  · intro i _ P
    apply potential_bound H P m _ hn
    intro X hX
    have hCore := sparseComponent_card_lower H (ρ i) X (hρ i).1 hn (P.sparse X hX)
    have hRoot : Real.sqrt (ρ i) ≤ α / 2 := by
      have h := Real.sqrt_le_sqrt (hρ i).2
      have hτα : τ * α ≤ α := by simpa using mul_le_mul_of_nonneg_right hτOne hα.le
      linarith only [h, hτα, hScale, hα]
    have hLow : α / 2 * n ≤ (X.card : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hRoot hnR
      linarith only [hCore, hMin, hDense, h]
    have hs := mul_le_mul_of_nonneg_right hmα hnR
    have ht := mul_le_mul_of_nonneg_left hLow (Nat.cast_nonneg (α := ℝ) m)
    exact_mod_cast (show (Fintype.card W : ℝ) ≤ (m : ℝ) * (X.card : ℝ) by linarith only [hs, ht])
  · intro i hi P
    exact (hSchedule i hi).2 H D hn hRegular hDense P

/-- The initial terminal partition, with no further restrictions on the
graph-independent schedule. -/
theorem exists_regular_prepartition (α τ r : ℝ)
    (hα : 0 < α) (hαOne : α ≤ 1) (hτ : 0 < τ) (hτOne : τ ≤ 1)
    (hr : 0 < r) (hrOne : r ≤ 1) (hScale : 4 * Real.sqrt r ≤ τ * α) :
    ∃ B : ℕ, ∃ ρ ν : ℕ → ℝ, (∀ i, 0 < ρ i ∧ ρ i ≤ r) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
        (D : ℕ), 0 < Fintype.card W → (∀ v, H.degree v = D) →
        α * (Fintype.card W : ℝ) ≤ D →
        ∃ i < B, ∃ P : SparsePartition H (ρ i), IsTerminal H P (ν i) τ := by
  obtain ⟨B, ρ, ν, hρ, _, hTerminal⟩ := exists_regular_prepartition_with.{u}
    α τ r (fun _ _ => True) (fun _ _ _ => ⟨1, by norm_num, fun _ _ _ => trivial⟩)
    hα hαOne hτ hτOne hr hrOne hScale
  exact ⟨B, ρ, ν, hρ, hTerminal⟩

end OverfullWork.KLOS
