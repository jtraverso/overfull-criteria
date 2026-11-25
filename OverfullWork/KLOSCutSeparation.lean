module

public import OverfullWork.KLOSRobustPartition

@[expose] public section

/-! The one-copy claim in the proof of Kühn–Lo–Osthus–Staden,
Theorem 5.1, for an arbitrary cut of small crossing degree. -/

namespace OverfullWork.KLOS

open Finset SimpleGraph PrunedCore RobustExpansion OddCutDeficit
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem inter_compl_card_add (U X : Finset V) :
    (U ∩ X).card + (U ∩ Xᶜ).card = U.card := by
  classical
  have h : U ∩ Xᶜ = U \ X := by ext v; simp
  rw [h, add_comm]
  exact card_sdiff_add_card_inter U X

private theorem neighboursIn_inter_compl_add (U X : Finset V) (v : V) :
    neighboursIn G (U ∩ X) v + neighboursIn G (U ∩ Xᶜ) v = neighboursIn G U v := by
  simp only [neighboursIn_eq_filter_card, ← filter_inter]
  exact inter_compl_card_add (U.filter (G.Adj v)) X

private theorem inter_card_lower (U X : Finset V) (v : V) {c L : ℝ}
    (hDegree : L ≤ (neighboursIn G U v : ℝ))
    (hAcross : (neighboursIn G Xᶜ v : ℝ) ≤ c) :
    L - c ≤ ((U ∩ X).card : ℝ) := by
  have hNear : (neighboursIn G (U ∩ X) v : ℝ) ≤ ((U ∩ X).card : ℝ) := by
    exact_mod_cast neighboursIn_le_card G (U ∩ X) v
  have hFar : (neighboursIn G (U ∩ Xᶜ) v : ℝ) ≤ (neighboursIn G Xᶜ v : ℝ) := by
    exact_mod_cast neighboursIn_mono G inter_subset_right v
  have hSum : (neighboursIn G (U ∩ X) v : ℝ) + (neighboursIn G (U ∩ Xᶜ) v : ℝ) =
      (neighboursIn G U v : ℝ) := by exact_mod_cast neighboursIn_inter_compl_add G U X v
  linarith only [hDegree, hAcross, hNear, hFar, hSum]

private theorem robustNeighbourhoodIn_inter_subset (U A X : Finset V) (ν c : ℝ)
    (hAcross : ∀ v ∉ X, (neighboursIn G X v : ℝ) ≤ c)
    (hThreshold : c < ν * (U.card : ℝ)) :
    robustNeighbourhoodIn G ν U (A ∩ X) ⊆ U ∩ X := by
  intro v hv
  obtain ⟨hvU, hvN⟩ := mem_filter.mp hv
  refine mem_inter.mpr ⟨hvU, ?_⟩
  by_contra h
  have hMono : (neighboursIn G (A ∩ X) v : ℝ) ≤ (neighboursIn G X v : ℝ) := by
    exact_mod_cast neighboursIn_mono G inter_subset_right v
  exact (not_lt_of_ge ((hvN.trans hMono).trans (hAcross v h))) hThreshold

/-- Every part of a robust partition lies on one side of a cut whose
maximum crossing degree is below the expansion threshold. The additional
inequalities put both intersections inside the expansion test window
whenever a part meets both sides of the cut. -/
theorem RobustPartition.part_subset_cut_side {D : ℕ} {r ν τ : ℝ}
    (P : RobustPartition G D r ν τ) (hRegular : ∀ v, G.degree v = D)
    (hn : 0 < Fintype.card V) (hr : 0 < r) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (X : Finset V) (c L : ℝ)
    (hCross : ∀ v ∈ X, (neighboursIn G Xᶜ v : ℝ) ≤ c)
    (hCross' : ∀ v ∉ X, (neighboursIn G X v : ℝ) ≤ c)
    (hDegree : 2 * (P.labels.card : ℝ) * L ≤ D)
    (hGap : c < L) (hWindow : τ * (Fintype.card V : ℝ) ≤ L - c)
    (hThreshold : c < ν * ((D : ℝ) - 2 * Real.sqrt r * (Fintype.card V : ℝ)))
    (hBalance : r * (Fintype.card V : ℝ) <
      2 * ν * ((D : ℝ) - 2 * Real.sqrt r * (Fintype.card V : ℝ)))
    (i : ↥P.labels) :
    assignmentPart P.assign i ⊆ X ∨ assignmentPart P.assign i ⊆ Xᶜ := by
  let U := assignmentPart P.assign i
  let n := (Fintype.card V : ℝ)
  have : Nonempty V := Fintype.card_pos_iff.mp hn
  have hMin : (D : ℝ) ≤ G.minDegree := by
    exact_mod_cast G.le_minDegree_of_forall_le_degree D fun v => (hRegular v).ge
  have hCardPos : (0 : ℝ) < P.labels.card := by
    exact_mod_cast card_pos.mpr ⟨i.val, i.property⟩
  have hTwoPos : 0 < (2 : ℝ) * P.labels.card := by positivity
  have hLocal (v : V) (hv : v ∈ U) : L ≤ (neighboursIn G U v : ℝ) := by
    have hi : P.assign v = i := (mem_filter.mp hv).2
    have hNat := P.internal_degree G hRegular v
    rw [hi] at hNat
    have h : (D : ℝ) ≤ (P.labels.card : ℝ) * neighboursIn G U v := by exact_mod_cast hNat
    apply (mul_le_mul_iff_of_pos_left hTwoPos).mp
    have hnn : (0 : ℝ) ≤ P.labels.card * (neighboursIn G U v : ℝ) := by positivity
    nlinarith only [hDegree, h, hnn]
  have hSides (U₀ : Finset V) (hX : L - c ≤ ((U₀ ∩ X).card : ℝ))
      (hX' : L - c ≤ ((U₀ ∩ Xᶜ).card : ℝ)) :
      τ * (U₀.card : ℝ) ≤ ((U₀ ∩ X).card : ℝ) ∧
      ((U₀ ∩ X).card : ℝ) ≤ (1 - τ) * (U₀.card : ℝ) ∧
      τ * (U₀.card : ℝ) ≤ ((U₀ ∩ Xᶜ).card : ℝ) ∧
      ((U₀ ∩ Xᶜ).card : ℝ) ≤ (1 - τ) * (U₀.card : ℝ) := by
    have hCard : (U₀.card : ℝ) ≤ n := by dsimp only [n]; exact_mod_cast card_le_univ U₀
    have hBudget := (mul_le_mul_of_nonneg_left hCard hτ).trans hWindow
    have hSum : ((U₀ ∩ X).card : ℝ) + ((U₀ ∩ Xᶜ).card : ℝ) = U₀.card := by
      exact_mod_cast inter_compl_card_add U₀ X
    refine ⟨hBudget.trans hX, ?_, hBudget.trans hX', ?_⟩ <;>
      rw [sub_mul, one_mul] <;> linarith only [hSum, hBudget, hX, hX']
  have hCrossCompl (v : V) (hv : v ∈ Xᶜ) :
      (neighboursIn G (Xᶜ)ᶜ v : ℝ) ≤ c := by simpa using hCross' v (mem_compl.mp hv)
  have hCrossCompl' (v : V) (hv : v ∉ Xᶜ) : (neighboursIn G Xᶜ v : ℝ) ≤ c :=
    hCross v (by simpa using hv)
  by_contra! h
  obtain ⟨vX, hvU, hvNot⟩ := not_subset.mp h.2
  obtain ⟨vY, hyU, hyNot⟩ := not_subset.mp h.1
  have hvX : vX ∈ X := by simpa using hvNot
  have hyY : vY ∈ Xᶜ := mem_compl.mpr hyNot
  have hThresholdFor (hSize : (D : ℝ) - 2 * Real.sqrt r * n ≤ U.card) :
      c < ν * (U.card : ℝ) :=
    hThreshold.trans_le (mul_le_mul_of_nonneg_left hSize hν.le)
  by_cases hi : i ∈ P.bipartite
  · obtain ⟨A, B, hAB, hClose, hExpand, hA, hB⟩ := P.crossing_degree G hRegular i hi
    have hAB' : A ∪ B = U := hAB
    have hLowerA (v : V) (hv : v ∈ A) : L ≤ (neighboursIn G B v : ℝ) :=
      (mul_le_mul_iff_of_pos_left hTwoPos).mp (hDegree.trans (by exact_mod_cast hA v hv))
    have hLowerB (v : V) (hv : v ∈ B) : L ≤ (neighboursIn G A v : ℝ) :=
      (mul_le_mul_iff_of_pos_left hTwoPos).mp (hDegree.trans (by exact_mod_cast hB v hv))
    have hALarge (Y : Finset V) (v : V) (hv : v ∈ U) (hvY : v ∈ Y)
        (hCut : ∀ w ∈ Y, (neighboursIn G Yᶜ w : ℝ) ≤ c) :
        L - c ≤ ((A ∩ Y).card : ℝ) := by
      rw [← hAB'] at hv
      rcases mem_union.mp hv with ha | hb
      · have hS := inter_card_lower G B Y v (hLowerA v ha) (hCut v hvY)
        have hp : (0 : ℝ) < (B ∩ Y).card := (sub_pos.mpr hGap).trans_le hS
        obtain ⟨w, hw⟩ := card_pos.mp (by exact_mod_cast hp)
        exact inter_card_lower G A Y w (hLowerB w (mem_inter.mp hw).1) (hCut w (mem_inter.mp hw).2)
      · exact inter_card_lower G A Y v (hLowerB v hb) (hCut v hvY)
    obtain ⟨hl, hu, hl', hu'⟩ :=
      hSides A (hALarge X vX hvU hvX hCross) (hALarge Xᶜ vY hyU hyY hCrossCompl)
    have hA_size := (bipartite_sides_lower G r A B hr hn hClose).1
    have hAsub : A ⊆ U := hAB' ▸ subset_union_left
    have hSize : (D : ℝ) - 2 * Real.sqrt r * n ≤ U.card := by
      have hh : (A.card : ℝ) ≤ U.card := by exact_mod_cast card_le_card hAsub
      linarith only [hA_size, hh, hMin]
    have hTh : c < ν * ((A ∪ B).card : ℝ) := hAB'.symm ▸ hThresholdFor hSize
    have hTest (Y : Finset V) (hCut : ∀ w ∉ Y, (neighboursIn G Y w : ℝ) ≤ c)
        (hL : τ * (A.card : ℝ) ≤ ((A ∩ Y).card : ℝ))
        (hH : ((A ∩ Y).card : ℝ) ≤ (1 - τ) * (A.card : ℝ)) :
        ((A ∩ Y).card : ℝ) + ν * ((A ∪ B).card : ℝ) ≤ ((B ∩ Y).card : ℝ) := by
      apply (hExpand (A ∩ Y) inter_subset_left hL hH).trans
      have hN := robustNeighbourhoodIn_inter_subset G (A ∪ B) A Y ν c hCut hTh
      have hSub : robustNeighbourhoodIn G ν (A ∪ B) (A ∩ Y) ∩ B ⊆ B ∩ Y := by
        intro w hw
        exact mem_inter.mpr ⟨(mem_inter.mp hw).2, (mem_inter.mp (hN (mem_inter.mp hw).1)).2⟩
      exact_mod_cast card_le_card hSub
    have hX := hTest X hCross' hl hu
    have hY := hTest Xᶜ hCrossCompl' hl' hu'
    have hSum (Z : Finset V) : ((Z ∩ X).card : ℝ) + ((Z ∩ Xᶜ).card : ℝ) = Z.card := by
      exact_mod_cast inter_compl_card_add Z X
    have hBal := (abs_le.mp hClose.2.2.2.1).1
    have hPay := mul_le_mul_of_nonneg_left hSize (by positivity : 0 ≤ 2 * ν)
    rw [hAB'] at hX hY
    linarith only [hX, hY, hSum A, hSum B, hBal, hPay, hBalance]
  · obtain ⟨hSparse, hExpand⟩ := P.ordinary i hi
    have hSize' := sparseComponent_card_lower G r U hr hn hSparse
    have hRoot : 0 ≤ Real.sqrt r * n := by positivity
    have hSize : (D : ℝ) - 2 * Real.sqrt r * n ≤ U.card := by
      linarith only [hSize', hRoot, hMin]
    obtain ⟨hl, hu, _, _⟩ := hSides U
      (inter_card_lower G U X vX (hLocal vX hvU) (hCross vX hvX))
      (inter_card_lower G U Xᶜ vY (hLocal vY hyU) (hCrossCompl vY hyY))
    have hNeighbour := robustNeighbourhoodIn_inter_subset G U U X ν c hCross' (hThresholdFor hSize)
    have hCard : ((robustNeighbourhoodIn G ν U (U ∩ X)).card : ℝ) ≤ ((U ∩ X).card : ℝ) := by
      exact_mod_cast card_le_card hNeighbour
    have hp : (0 : ℝ) < U.card := by exact_mod_cast card_pos.mpr ⟨vX, hvU⟩
    linarith only [hExpand (U ∩ X) inter_subset_left hl hu, hCard, mul_pos hν hp]

/-- The numeric form of the one-side claim. The density is measured
relative to the ambient graph, including both copies when applied to
the regularization. -/
theorem RobustPartition.part_subset_cut_side_of_density {D : ℕ} {r ν τ : ℝ}
    (P : RobustPartition G D r ν τ) (hRegular : ∀ v, G.degree v = D)
    (hn : 0 < Fintype.card V) (hr : 0 < r) (hrOne : r ≤ 1) (hν : 0 < ν)
    (α : ℝ) (hα : 0 < α) (hDense : α * (Fintype.card V : ℝ) ≤ D)
    (hRoot : 2 * Real.sqrt r ≤ α / 2) (hError : r ≤ ν * α / 2)
    (hτ : 0 ≤ τ) (hWindow : τ ≤ α ^ 2 / 8) (X : Finset V) (c : ℝ)
    (hSmall : c ≤ α ^ 2 * (Fintype.card V : ℝ) / 8)
    (hThreshold : c ≤ ν * α * (Fintype.card V : ℝ) / 4)
    (hCross : ∀ v ∈ X, (neighboursIn G Xᶜ v : ℝ) ≤ c)
    (hCross' : ∀ v ∉ X, (neighboursIn G X v : ℝ) ≤ c)
    (i : ↥P.labels) :
    assignmentPart P.assign i ⊆ X ∨ assignmentPart P.assign i ⊆ Xᶜ := by
  let n := (Fintype.card V : ℝ)
  let L := α ^ 2 * n / 4
  have hnPos : 0 < n := by dsimp only [n]; exact_mod_cast hn
  have hPow : r ^ ((1 : ℝ) / 3) ≤ 1 := Real.rpow_le_one hr.le hrOne (by norm_num)
  have hCount := P.count
  have hParts : (P.labels.card : ℝ) * α ≤ 2 := by
    apply (mul_le_mul_iff_of_pos_right hnPos).mp
    have h₁ := mul_le_mul_of_nonneg_left hDense (Nat.cast_nonneg (α := ℝ) P.labels.card)
    have h₂ := mul_nonneg (Nat.cast_nonneg (α := ℝ) P.bipartite.card) (Nat.cast_nonneg (α := ℝ) D)
    have h₃ := mul_le_mul_of_nonneg_right hPow hnPos.le
    change (P.labels.card : ℝ) * (α * n) ≤ (P.labels.card : ℝ) * D at h₁
    change ((P.labels.card : ℝ) + (P.bipartite.card : ℝ)) * D ≤
      (1 + r ^ ((1 : ℝ) / 3)) * n at hCount
    nlinarith only [h₁, h₂, h₃, hCount]
  have hDegree : 2 * (P.labels.card : ℝ) * L ≤ D := by
    have h₁ := mul_le_mul_of_nonneg_right hParts (by positivity : 0 ≤ α * n / 2)
    change α * n ≤ (D : ℝ) at hDense
    dsimp only [L]
    nlinarith only [h₁, hDense]
  have hSize : α * n / 2 ≤ (D : ℝ) - 2 * Real.sqrt r * n := by
    have h := mul_le_mul_of_nonneg_right hRoot hnPos.le
    change α * n ≤ (D : ℝ) at hDense
    linarith only [hDense, h]
  have hSize' := mul_le_mul_of_nonneg_left hSize hν.le
  have hPos : 0 < ν * α * n := by positivity
  have hSquare : 0 < α ^ 2 * n := by positivity
  change c ≤ α ^ 2 * n / 8 at hSmall
  change c ≤ ν * α * n / 4 at hThreshold
  refine P.part_subset_cut_side G hRegular hn hr hν hτ X c L hCross hCross' hDegree ?_ ?_ ?_ ?_ i
  · dsimp only [L]; linarith only [hSmall, hSquare]
  · have h := mul_le_mul_of_nonneg_right hWindow hnPos.le
    change τ * n ≤ L - c
    dsimp only [L]
    nlinarith only [h, hSmall]
  · change c < ν * ((D : ℝ) - 2 * Real.sqrt r * n)
    nlinarith only [hSize', hPos, hThreshold]
  · have h := mul_le_mul_of_nonneg_right hError hnPos.le
    change r * n < 2 * ν * ((D : ℝ) - 2 * Real.sqrt r * n)
    nlinarith only [hSize', hPos, h]

/-- One of the two sides carries at most half the weighted component
count. A bipartite label contributes two to this count. -/
theorem RobustPartition.exists_cut_side_count_le {D : ℕ} {r ν τ : ℝ}
    (P : RobustPartition G D r ν τ) (X : Finset V)
    (hInside : ∀ i : ↥P.labels, assignmentPart P.assign i ⊆ X ∨
      assignmentPart P.assign i ⊆ Xᶜ) :
    ∃ Y : Finset V, (Y = X ∨ Y = Xᶜ) ∧
      let J := (univ : Finset ↥P.labels).filter (fun i => assignmentPart P.assign i ⊆ Y)
      ((J.card : ℝ) + ((J ∩ P.bipartite).card : ℝ)) * D ≤
        (1 + r ^ ((1 : ℝ) / 3)) * (Fintype.card V : ℝ) / 2 := by
  let J (Y : Finset V) := (univ : Finset ↥P.labels).filter (fun i => assignmentPart P.assign i ⊆ Y)
  have hCompl : (J X)ᶜ = J Xᶜ := by
    ext i
    simp only [J, mem_compl, mem_filter, mem_univ, true_and]
    constructor
    · exact (hInside i).resolve_left
    · intro hy hx
      obtain ⟨v, hv⟩ := P.nonempty_part i
      exact (mem_compl.mp (hy hv)) (hx hv)
  have hOne : (J X).card + (J Xᶜ).card = P.labels.card := by
    rw [← hCompl, card_compl, Fintype.card_coe]
    have h : (J X).card ≤ P.labels.card := by simpa using card_le_univ (J X)
    omega
  have hTwo : (J X ∩ P.bipartite).card + (J Xᶜ ∩ P.bipartite).card = P.bipartite.card := by
    simpa only [← hCompl, inter_comm (J X), inter_comm ((J X)ᶜ)] using
      inter_compl_card_add P.bipartite (J X)
  have hOneR : ((J X).card : ℝ) + ((J Xᶜ).card : ℝ) = P.labels.card := by exact_mod_cast hOne
  have hTwoR : ((J X ∩ P.bipartite).card : ℝ) + ((J Xᶜ ∩ P.bipartite).card : ℝ) =
      P.bipartite.card := by exact_mod_cast hTwo
  let cost (Y : Finset V) := ((J Y).card + (J Y ∩ P.bipartite).card : ℝ) * D
  have hTotal : cost X + cost Xᶜ ≤ (1 + r ^ ((1 : ℝ) / 3)) * (Fintype.card V : ℝ) := by
    dsimp only [cost]
    have h := congrArg (fun x : ℝ => x * D) (show
      ((J X).card : ℝ) + ((J Xᶜ).card : ℝ) + (((J X ∩ P.bipartite).card : ℝ) +
        ((J Xᶜ ∩ P.bipartite).card : ℝ)) = (P.labels.card : ℝ) + P.bipartite.card by
      rw [hOneR, hTwoR])
    nlinarith only [h, P.count]
  by_cases hX : cost X ≤ cost Xᶜ
  · refine ⟨X, Or.inl rfl, ?_⟩
    change cost X ≤ _
    linarith only [hX, hTotal]
  · refine ⟨Xᶜ, Or.inr rfl, ?_⟩
    change cost Xᶜ ≤ _
    linarith only [le_of_not_ge hX, hTotal]

end OverfullWork.KLOS
