module

public import OverfullWork.KuhnOsthusCodegreeCount
public import OverfullWork.OsthusStadenCoreException
public import OverfullWork.KuhnOsthusPhysicalSuccessorPairs
public import OverfullWork.OsthusStadenSliceRegularity
public import OverfullWork.SuperregularMergeReserve

@[expose] public section


/-! The vertex and arc deletion estimates in Kühn–Osthus
Proposition 4.3 and Lemma 7.5(iv). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem density_after_arc_deletion (G H : Digraph V) (hHG : H ≤ G)
    (X Y : Finset V) (k : ℕ) (δ : ℝ)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hPay : (k:ℝ) ≤ δ*(X.card:ℝ))
    (hLoss : ∀ y ∈ Y, inDegree H y ≤ k) :
    |density (G \ H) X Y-density G X Y| ≤ δ := by
  have hPart : (incidences (G \ H) X Y:ℝ)+incidences H X Y=incidences G X Y := by
    exact_mod_cast DirectedArcSelection.incidence_partition G H hHG X Y
  have hLost : (incidences H X Y:ℝ) ≤ (Y.card:ℝ)*k := by
    have hN : ∀ y ∈ Y, inNeighbours H X y ≤ k := by
      intro y hy
      exact (card_le_card (filter_subset_filter _ (subset_univ _))).trans (hLoss y hy)
    rw [mul_comm]
    exact_mod_cast incidences_le_of_neighbour_bound H X Y k hN
  have hx : (0:ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hy : (0:ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hDen := mul_pos hx hy
  have hLost' : |density H X Y| ≤ δ := by
    unfold density
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hDen.le)]
    apply (div_le_iff₀ hDen).mpr
    have h := mul_le_mul_of_nonneg_right hPay hy.le
    nlinarith only [hLost,h]
  have hEq : density (G \ H) X Y + density H X Y = density G X Y := by
    unfold density
    rw [←add_div,hPart]
  rwa [show density (G \ H) X Y-density G X Y = -(density H X Y) by linarith only [hEq],abs_neg]

/-- A two-sided rectangular density estimate survives vertex and arc
deletion. The budget is paid on the smallest tested source rectangle. -/
theorem uniform_on_pair_remainder (G H : Digraph V) (hHG : H ≤ G)
    (U W A B : Finset V) (hA : A ⊆ U) (hB : B ⊆ W)
    (hAnon : A.Nonempty) (hBnon : B.Nonempty)
    (ε η δ : ℝ) (k : ℕ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hScaleA : (U.card:ℝ)*ε ≤ (A.card:ℝ)*η)
    (hScaleB : (W.card:ℝ)*ε ≤ (B.card:ℝ)*η)
    (hTol : 2*(ε+δ) ≤ η) (hBudget : (k:ℝ) ≤ δ*((A.card:ℝ)*η)) (hδ : 0 ≤ δ)
    (hLoss : ∀ y ∈ W, inDegree H y ≤ k) (hG : IsUniform G ε U W) :
    IsUniform (G \ H) η A B ∧ |density (G \ H) A B-density G U W| < ε+δ := by
  have ha : (0:ℝ) < A.card := by exact_mod_cast hAnon.card_pos
  have hb : (0:ℝ) < B.card := by exact_mod_cast hBnon.card_pos
  have hClose (X Y : Finset V) (hX : X ⊆ A) (hY : Y ⊆ B)
      (hx : (A.card:ℝ)*η ≤ (X.card:ℝ)) (hy : (B.card:ℝ)*η ≤ (Y.card:ℝ)) :
      |density (G \ H) X Y-density G U W| < ε+δ := by
    have hx' : X.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos ha hη).trans_le hx)
    have hy' : Y.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos hb hη).trans_le hy)
    have h := hG X (hX.trans hA) Y (hY.trans hB) (hScaleA.trans hx) (hScaleB.trans hy)
    have hK := hBudget.trans (mul_le_mul_of_nonneg_left hx hδ)
    have hLoss' := density_after_arc_deletion G H hHG X Y k δ hx' hy' hK (fun y hy => hLoss y (hB (hY hy)))
    calc
      _ = |(density G X Y-density G U W)+(density (G \ H) X Y-density G X Y)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ < _ := add_lt_add_of_lt_of_le h hLoss'
  have hWhole := hClose A B (subset_refl _) (subset_refl _)
    (mul_le_of_le_one_right ha.le hη1) (mul_le_of_le_one_right hb.le hη1)
  refine ⟨?_,hWhole⟩
  intro X hX Y hY hx hy
  have hSub := hClose X Y hX hY hx hy
  calc
    _ = |(density (G \ H) X Y-density G U W)-(density (G \ H) A B-density G U W)| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ < (ε+δ)+(ε+δ) := add_lt_add hSub hWhole
    _ ≤ _ := by linarith only [hTol]

private theorem profile_as_filter (A : Finset V) (p : V → Prop) :
    profileCount A (univ.filter p) = ((A.filter p).card:ℝ) := by
  have he : A ∩ univ.filter p = A.filter p := by ext v; simp
  rw [profileCount,he]

private theorem profile_filter_subset (p q : V → Prop) (h : ∀ x, p x → q x) :
    univ.filter p ⊆ univ.filter q := by
  intro x hx
  exact mem_filter.mpr ⟨mem_univ _,h x (mem_filter.mp hx).2⟩

omit [Fintype V] in
private theorem profile_degree_of_pair_remainder
    (S T Q Q' : Finset V) (hST : T ⊆ S) (hQ : Q' ⊆ Q) (k : ℕ) (d ε η : ℝ)
    (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hRef : |profileCount S Q-d*(S.card:ℝ)| ≤ ε*(S.card:ℝ))
    (hDelete : profileCount T Q ≤ profileCount T Q'+k)
    (hPay : ε*(S.card:ℝ)+((S \ T).card:ℝ)+k ≤ η*(T.card:ℝ)) :
    |profileCount T Q'-d*(T.card:ℝ)| ≤ η*(T.card:ℝ) := by
  have hDecomp : (T.card:ℝ)+((S \ T).card:ℝ) = S.card := by
    rw [add_comm,←Nat.cast_add,card_sdiff_add_card_eq_card hST]
  have hMon : profileCount T Q' ≤ profileCount S Q := by
    unfold profileCount
    exact_mod_cast card_le_card (inter_subset_inter hST hQ)
  have hClip := exceptional_overlap_loss Q S T
  rw [inter_eq_right.mpr hST] at hClip
  have hScale := mul_le_mul_of_nonneg_right hd1 (Nat.cast_nonneg (S \ T).card : (0:ℝ) ≤ _)
  have hSmall := mul_nonneg hd (Nat.cast_nonneg (S \ T).card : (0:ℝ) ≤ _)
  have hIdentity := congrArg (fun x : ℝ => d*x) hDecomp
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨hl,hu⟩ := abs_le.mp hRef
  exact abs_le.mpr ⟨by linarith only [hl,hClip,hDelete,hPay,hIdentity,hSmall],
    by linarith only [hu,hMon,hPay,hIdentity,hScale,hk]⟩

/-- Superregularity on the original pair implies centred
superregularity on a remainder that meets the stated budgets. -/
theorem IsSuperregularPair.on_pair_remainder (G H : Digraph V) (hHG : H ≤ G)
    (U W A B : Finset V) (hA : A ⊆ U) (hB : B ⊆ W)
    (hAnon : A.Nonempty) (hBnon : B.Nonempty)
    (d ε η δ : ℝ) (k : ℕ) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hδ : 0 ≤ δ)
    (hScaleA : (U.card:ℝ)*ε ≤ (A.card:ℝ)*η)
    (hScaleB : (W.card:ℝ)*ε ≤ (B.card:ℝ)*η)
    (hTol : 2*(ε+δ) ≤ η) (hBudget : (k:ℝ) ≤ δ*((A.card:ℝ)*η))
    (hPayA : ε*(U.card:ℝ)+((U \ A).card:ℝ)+k ≤ η*(A.card:ℝ))
    (hPayB : ε*(W.card:ℝ)+((W \ B).card:ℝ)+k ≤ η*(B.card:ℝ))
    (hLossOut : ∀ x ∈ U, outDegree H x ≤ k)
    (hLossIn : ∀ y ∈ W, inDegree H y ≤ k)
    (hG : IsSuperregularPair G ε d U W) :
    IsSuperregularPair (G \ H) η d A B := by
  obtain ⟨hUniform,hClose⟩ := uniform_on_pair_remainder G H hHG U W A B hA hB hAnon hBnon
    ε η δ k hη hη1 hScaleA hScaleB hTol hBudget hδ hLossIn hG.1
  refine ⟨hUniform,?_,?_,?_⟩
  · calc
      _ = |(density (G \ H) A B-density G U W)+(density G U W-d)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ η := by linarith only [hClose,hG.2.1,hTol,hδ]
  · intro x hx
    apply profile_degree_of_pair_remainder W B (outProfile G x) (outProfile (G \ H) x)
      hB _ k d ε η hd hd1 (hG.2.2.1 x (hA hx)) _ hPayB
    · exact profile_filter_subset _ _ (fun _ h => h.1)
    · simp only [outProfile,profile_as_filter]
      have hPart : (incidences (G \ H) {x} B:ℝ)+incidences H {x} B=incidences G {x} B := by
        exact_mod_cast DirectedArcSelection.incidence_partition G H hHG {x} B
      simp only [incidences_eq_sum_outTo,sum_singleton,outTo] at hPart
      have hLost : ((B.filter (H.Adj x)).card:ℝ) ≤ k := by
        exact_mod_cast (card_le_card (filter_subset_filter _ (subset_univ B))).trans (hLossOut x (hA hx))
      linarith only [hPart,hLost]
  · intro y hy
    apply profile_degree_of_pair_remainder U A (inProfile G y) (inProfile (G \ H) y)
      hA _ k d ε η hd hd1 (hG.2.2.2 y (hB hy)) _ hPayA
    · exact profile_filter_subset _ _ (fun _ h => h.1)
    · simp only [inProfile,profile_as_filter]
      have hPart : (incidences (G \ H) A {y}:ℝ)+incidences H A {y}=incidences G A {y} := by
        exact_mod_cast DirectedArcSelection.incidence_partition G H hHG A {y}
      simp only [incidences,sum_singleton,inNeighbours] at hPart
      have hLost : ((A.filter (fun x => H.Adj x y)).card:ℝ) ≤ k := by
        exact_mod_cast (card_le_card (filter_subset_filter _ (subset_univ A))).trans (hLossIn y (hB hy))
      linarith only [hPart,hLost]

/-- Lemma 7.5(iv) with explicit scales. First refine both sides
uniformly, then account for the arcs already used by earlier factors. -/
theorem IsSuperregularPair.on_residual_style_cells (G H : Digraph V) (hHG : H ≤ G)
    (U W A B : Finset V) (hA : A ⊆ U) (hB : B ⊆ W)
    (hAnon : A.Nonempty) (hBal : A.card = B.card)
    (K k : ℕ) (d ε η δ : ℝ) (hK : 0 < K) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hε : 0 ≤ ε) (hη : 0 < η) (hη1 : η ≤ 1) (hδ : 0 ≤ δ) (hFloor : 2*ε ≤ d)
    (hSizeA : U.card = K*A.card) (hSizeB : W.card = K*B.card)
    (hRefA : UniformProfileCell (inProfile G) U A K ε)
    (hRefB : UniformProfileCell (outProfile G) W B K ε)
    (hTol : 2*(max 2 (K:ℝ)*ε+δ) ≤ η)
    (hBudget : (k:ℝ) ≤ δ*((A.card:ℝ)*η))
    (hLossOut : ∀ x ∈ U, outDegree H x ≤ k)
    (hLossIn : ∀ y ∈ W, inDegree H y ≤ k)
    (hG : IsSuperregularPair G ε d U W) :
    IsSuperregularPair (G \ H) η d A B := by
  let a := max 2 (K:ℝ)*ε
  have ha : a ≤ η := by
    change 2*(a+δ) ≤ η at hTol
    linarith only [hTol,hδ,hη]
  have hTwo : 2*ε ≤ a := mul_le_mul_of_nonneg_right (le_max_left _ _) hε
  have hKε : (K:ℝ)*ε ≤ a := mul_le_mul_of_nonneg_right (le_max_right _ _) hε
  have hScale (S T : Finset V) (hSize : S.card = K*T.card) :
      (S.card:ℝ)*ε ≤ (T.card:ℝ)*a := by
    rw [hSize,Nat.cast_mul]
    have h := mul_le_mul_of_nonneg_right hKε (Nat.cast_nonneg T.card)
    nlinarith only [h]
  have hBase := IsSuperregularPair.on_profile_cells G hG hA hB hSizeA hSizeB hK hK
    hRefA hRefB hε (by linarith only [hFloor]) (max_le hTwo (by linarith only [hTwo]))
    (ha.trans hη1) (hScale U A hSizeA) (hScale W B hSizeB)
  have hBnon : B.Nonempty := by
    apply card_pos.mp
    rw [←hBal]
    exact hAnon.card_pos
  have hSmall : a+δ ≤ η := by
    change 2*(a+δ) ≤ η at hTol
    linarith only [hTol,hη]
  have hPayA : a*(A.card:ℝ)+((A \ A).card:ℝ)+k ≤ η*(A.card:ℝ) := by
    have hDecr := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (Nat.cast_nonneg A.card) hη1) hδ
    have h := mul_le_mul_of_nonneg_right hSmall (Nat.cast_nonneg A.card)
    simp [sdiff_self]
    linarith only [hBudget,hDecr,h]
  have hPayB : a*(B.card:ℝ)+((B \ B).card:ℝ)+k ≤ η*(B.card:ℝ) := by
    simpa only [sdiff_self,card_empty,←hBal] using hPayA
  exact IsSuperregularPair.on_pair_remainder G H hHG A B A B (subset_refl _) (subset_refl _)
    hAnon hBnon d a η δ k hd hd1 hη hη1 hδ
    (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg A.card))
    (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg B.card)) hTol hBudget hPayA hPayB
    (fun x hx => hLossOut x (hA hx)) (fun y hy => hLossIn y (hB hy)) hBase

/-- Restrict the residual pair to the vertices still available
after adding the exceptional sequence and its correcting chords. -/
theorem IsSuperregularPair.on_free_subcells (G : Digraph V)
    (U W A B : Finset V) (hA : A ⊆ U) (hB : B ⊆ W)
    (hAnon : A.Nonempty) (hBnon : B.Nonempty)
    (d ε η : ℝ) (hd : 0 ≤ d) (hd1 : d ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hTol : 2*ε ≤ η)
    (hLeft : (U.card:ℝ)*ε+((U \ A).card:ℝ) ≤ (A.card:ℝ)*η)
    (hRight : (W.card:ℝ)*ε+((W \ B).card:ℝ) ≤ (B.card:ℝ)*η)
    (hG : IsSuperregularPair G ε d U W) :
    IsSuperregularPair G η d A B := by
  have hLeft' : (U.card:ℝ)*ε ≤ (A.card:ℝ)*η :=
    (le_add_of_nonneg_right (Nat.cast_nonneg (U \ A).card)).trans hLeft
  have hRight' : (W.card:ℝ)*ε ≤ (B.card:ℝ)*η :=
    (le_add_of_nonneg_right (Nat.cast_nonneg (W \ B).card)).trans hRight
  have h := IsSuperregularPair.on_pair_remainder G ⊥ bot_le U W A B hA hB hAnon hBnon
    d ε η 0 0 hd hd1 hη hη1 le_rfl hLeft' hRight' (by simpa using hTol)
    (by simp) (by simpa [mul_comm] using hLeft) (by simpa [mul_comm] using hRight)
    (by intro x _; simp [outDegree,Digraph.bot_adj])
    (by intro y _; simp [inDegree,inNeighbours,Digraph.bot_adj]) hG
  simpa only [sdiff_bot] using h

/-- Centred superregularity gives the physical degree and rectangle
bounds needed both for Hall and for the successor matching replacements. -/
theorem IsSuperregularPair.physical_lower_bounds (G : Digraph V) (A B : Finset V)
    (d ε : ℝ) (hG : IsSuperregularPair G ε d A B) :
    (∀ x ∈ A, (d-ε)*(B.card:ℝ) ≤ (((B.filter (G.Adj x)).card):ℝ)) ∧
    (∀ y ∈ B, (d-ε)*(A.card:ℝ) ≤ (inNeighbours G A y:ℝ)) ∧
    ∀ X ⊆ A, ∀ Y ⊆ B, (A.card:ℝ)*ε ≤ (X.card:ℝ) → (B.card:ℝ)*ε ≤ (Y.card:ℝ) →
      (d-2*ε)*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences G X Y:ℝ) := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have h := (abs_le.mp (hG.2.2.1 x hx)).1
    simp only [outProfile,profile_as_filter] at h
    linarith only [h]
  · intro y hy
    have h := (abs_le.mp (hG.2.2.2 y hy)).1
    simp only [inProfile,profile_as_filter] at h
    change _ ≤ ((A.filter (fun x => G.Adj x y)).card:ℝ)
    linarith only [h]
  · intro X hX Y hY hx hy
    rcases X.eq_empty_or_nonempty with rfl | hXpos
    · simp
    rcases Y.eq_empty_or_nonempty with rfl | hYpos
    · simp
    have hDensity : d-ε ≤ density G A B := by
      linarith only [(abs_le.mp hG.2.1).1]
    have h := uniform_incidences_lower G hG.1 hDensity hX hY hx hy hXpos hYpos
    simpa only [sub_sub,←two_mul] using h.le

/-- A centred superregular pair gives the perfect matching used to
fill the free sides between consecutive clusters in Lemma 7.6. -/
theorem IsSuperregularPair.exists_perfect_matching (G : Digraph V) (A B : Finset V)
    (d ε : ℝ) (r : ℕ) (hGap : 2*ε < d) (hr : 0 < r) (hBal : A.card = B.card)
    (hCut : (A.card:ℝ)*ε ≤ (r:ℝ)) (hDegree : (r:ℝ) ≤ (d-ε)*(A.card:ℝ))
    (hG : IsSuperregularPair G ε d A B) :
    ∃ f : A ≃ B, ∀ a : A, G.Adj a (f a) := by
  obtain ⟨hOut,hIn,hRect⟩ := IsSuperregularPair.physical_lower_bounds G A B d ε hG
  apply exists_matching_on_of_rectangle_threshold G A B r hBal
  · intro x hx
    have h := hOut x hx
    rw [←hBal] at h
    exact_mod_cast hDegree.trans h
  · intro y hy
    exact_mod_cast hDegree.trans (hIn y hy)
  · intro X hX Y hY hx hy
    have hx' : (r:ℝ) ≤ X.card := by exact_mod_cast hx
    have hy' : (r:ℝ) ≤ Y.card := by exact_mod_cast hy
    have hCutB : (B.card:ℝ)*ε ≤ (r:ℝ) := by rwa [←hBal]
    have hLower := hRect X hX Y hY (hCut.trans hx') (hCutB.trans hy')
    have hr' : (0:ℝ) < r := by exact_mod_cast hr
    have hPos := mul_pos (mul_pos (sub_pos.mpr hGap) (hr'.trans_le hx')) (hr'.trans_le hy')
    exact_mod_cast hPos.trans_le hLower

/-- A superregular pair whose individual density parameter is at
least the common density floor. Different pairs may have different
density parameters. -/
def IsLowerSuperregularPair (G : Digraph V) (ε d : ℝ) (A B : Finset V) : Prop :=
  ∃ density, d ≤ density ∧ density ≤ 1 ∧ IsSuperregularPair G ε density A B

theorem IsLowerSuperregularPair.physical_lower_bounds (G : Digraph V) (A B : Finset V)
    (d ε : ℝ) (h : IsLowerSuperregularPair G ε d A B) :
    (∀ x ∈ A, (d-ε)*(B.card:ℝ) ≤ (((B.filter (G.Adj x)).card):ℝ)) ∧
    (∀ y ∈ B, (d-ε)*(A.card:ℝ) ≤ (inNeighbours G A y:ℝ)) ∧
    ∀ X ⊆ A, ∀ Y ⊆ B, (A.card:ℝ)*ε ≤ (X.card:ℝ) → (B.card:ℝ)*ε ≤ (Y.card:ℝ) →
      (d-2*ε)*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences G X Y:ℝ) := by
  obtain ⟨c,hc,_,hcPair⟩ := h
  obtain ⟨ho,hi,hr⟩ := IsSuperregularPair.physical_lower_bounds G A B c ε hcPair
  refine ⟨?_,?_,?_⟩
  · intro x hx
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hc _) (Nat.cast_nonneg _)).trans (ho x hx)
  · intro y hy
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hc _) (Nat.cast_nonneg _)).trans (hi y hy)
  · intro X hX Y hY hx hy
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (sub_le_sub_right hc _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans (hr X hX Y hY hx hy)

end OverfullWork.DirectedRobustExpansion
