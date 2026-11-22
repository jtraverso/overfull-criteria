module

public import OverfullWork.OsthusStadenNestedRefinement

@[expose] public section


/-! The three successive refinements of the primary cells in Osthus–Staden §5.3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u v

/-- Refine a primary cell into s cells, each into p cells, and then
divide each p-cell into two halves. -/
structure PrimaryNestedRefinement {V : Type u} {J : Type v}
    (profiles : J → Finset V) (P : Finset V) (s p m : ℕ)
    (ε₁ ε₂ ε₃ : ℝ) where
  first : UniformRefinementOf (I := Fin s) profiles P (p*(2*m)) ε₁
  second : ∀ i, UniformRefinementOf (I := Fin p) profiles (first.cells i) (2*m) ε₂
  halves : ∀ i j, UniformRefinementOf (I := Fin 2) profiles ((second i).cells j) m ε₃

/-- The single size threshold covers all three levels of the base refinement. -/
theorem exists_primary_nested_refinement (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (s p : ℕ) (hs : 0 < s) (hp : 0 < p) :
    ∃ N : ℕ, ∀ {V : Type u} {J : Type v} [Fintype J]
      (profiles : J → Finset V) (P : Finset V) (m : ℕ),
      N ≤ m → P.card = s*(p*(2*m)) → (Fintype.card J:ℝ) ≤ C*(m:ℝ) →
      Nonempty (PrimaryNestedRefinement profiles P s p m ε ε ε) := by
  obtain ⟨N₁,hFirst⟩ := exists_ambient_uniform_refinement.{u,v} C ε hC hε s hs
  obtain ⟨N₂,hSecond⟩ := exists_ambient_uniform_refinement.{u,v} C ε hC hε p hp
  obtain ⟨N₃,hHalves⟩ := exists_ambient_uniform_refinement.{u,v} C ε hC hε 2 (by decide)
  refine ⟨max N₁ (max N₂ N₃),?_⟩
  intro V J _ profiles P m hN hCard hProfile
  have h₂ : m ≤ 2*m := by omega
  have hp₂ : 2*m ≤ p*(2*m) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (2*m) (show 1 ≤ p from hp)
  have hFirstSize : m ≤ P.card := by
    rw [hCard]
    exact (h₂.trans hp₂).trans (by
      simpa only [one_mul] using Nat.mul_le_mul_right (p*(2*m)) (show 1 ≤ s from hs))
  have hProfiles {Q : Finset V} (hQ : m ≤ Q.card) : (Fintype.card J:ℝ) ≤ C*(Q.card:ℝ) :=
    hProfile.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hQ) hC.le)
  obtain ⟨R⟩ := hFirst profiles P (p*(2*m)) (((le_max_left _ _).trans hN).trans hFirstSize)
    hCard (hProfiles hFirstSize)
  have hS (i : Fin s) : Nonempty (UniformRefinementOf (I := Fin p) profiles (R.cells i) (2*m) ε) := by
    have h : m ≤ (R.cells i).card := by rw [R.size i]; exact h₂.trans hp₂
    exact hSecond profiles (R.cells i) (2*m)
      ((((le_max_left _ _).trans (le_max_right _ _)).trans hN).trans h) (R.size i) (hProfiles h)
  let S (i : Fin s) := Classical.choice (hS i)
  have hT (i : Fin s) (j : Fin p) :
      Nonempty (UniformRefinementOf (I := Fin 2) profiles ((S i).cells j) m ε) := by
    have h : m ≤ ((S i).cells j).card := by rw [(S i).size j]; exact h₂
    exact hHalves profiles ((S i).cells j) m
      ((((le_max_right _ _).trans (le_max_right _ _)).trans hN).trans h)
      ((S i).size j) (hProfiles h)
  let T (i : Fin s) (j : Fin p) := Classical.choice (hT i j)
  exact ⟨⟨R,S,T⟩⟩

/-- Explicit sufficient margins for adapting an ℓ-refinement when the
parent has changed by at most D vertices in either direction. -/
structure RefinementAdaptationBounds (ℓ m₀ m D : ℕ) (ε ε' : ℝ) : Prop where
  growth : 0 ≤ ε ∧ ε ≤ ε'
  floor : ε*((ℓ*m₀:ℕ):ℝ)+(D:ℝ) ≤ ε'*((ℓ*m:ℕ):ℝ)
  error : ((D+(m₀-m):ℕ):ℝ)+(1+ε)*(D:ℝ)/(ℓ:ℝ) ≤
    (ε'-ε)*(ε'*((ℓ*m:ℕ):ℝ)/(ℓ:ℝ))

/-- In relative units, a parent loss and a cell-size loss at most
`τ²/16` pay for the adaptation from tolerance `ε` to `τ`. -/
theorem RefinementAdaptationBounds.of_small_changes
    {ℓ m₀ m D : ℕ} {ε τ : ℝ}
    (hℓ : 0 < ℓ) (hm : m ≤ m₀) (hε : 0 ≤ ε) (hSmall : ε ≤ τ/4)
    (hτ : 0 < τ) (hτ₁ : τ ≤ 1)
    (hD : (D:ℝ) ≤ (τ^2/16)*(m:ℝ)) (hSize : ((m₀-m:ℕ):ℝ) ≤ (τ^2/16)*(m:ℝ)) :
    RefinementAdaptationBounds ℓ m₀ m D ε τ := by
  have hℓ₁ : (1:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ' : (0:ℝ) < ℓ := by linarith only [hℓ₁]
  have hloss := Nat.cast_nonneg (α := ℝ) (m₀-m)
  have hmR : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hTauSq : τ^2 ≤ τ := by
    have h := mul_le_mul_of_nonneg_left hτ₁ hτ.le
    nlinarith only [h]
  have hTauBudget : (τ^2/16)*(m:ℝ) ≤ (τ/16)*(m:ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith only [hTauSq]) hmR
  have hSizeEq : (m₀:ℝ) = (m:ℝ)+((m₀-m:ℕ):ℝ) := by
    rw [Nat.cast_sub hm]
    ring
  have hOld : (m₀:ℝ) ≤ 2*(m:ℝ) := by
    have h := mul_le_of_le_one_left hmR (show τ/16 ≤ 1 by linarith only [hτ₁])
    linarith only [hSizeEq,hSize,hTauBudget,h]
  refine ⟨⟨hε,by linarith only [hSmall,hτ]⟩,?_,?_⟩
  · push_cast
    have hεℓ : 0 ≤ ε*(ℓ:ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hOld hεℓ
    have h2 := mul_le_mul_of_nonneg_right hSmall (show 0 ≤ (ℓ:ℝ)*(m:ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_left hℓ₁ (show 0 ≤ (τ/16)*(m:ℝ) by positivity)
    nlinarith only [h1,h2,h3,hD,hTauBudget,
      show 0 ≤ τ*(ℓ:ℝ)*(m:ℝ) by positivity]
  · have hCancel : τ*((ℓ*m:ℕ):ℝ)/(ℓ:ℝ) = τ*(m:ℝ) := by
      push_cast
      field_simp
    rw [Nat.cast_add,hCancel]
    have hε₁ : ε ≤ 1 := by linarith only [hSmall,hτ₁]
    have hTerm : (1+ε)*(D:ℝ)/(ℓ:ℝ) ≤ 2*(D:ℝ) := by
      apply (div_le_iff₀ hℓ').mpr
      have h1 := mul_le_mul_of_nonneg_right (show 1+ε ≤ 2 by linarith only [hε₁])
        (Nat.cast_nonneg D : (0:ℝ) ≤ _)
      have h2 := mul_le_mul_of_nonneg_left hℓ₁ (show 0 ≤ 2*(D:ℝ) by positivity)
      linarith only [h1,h2]
    have hετ := mul_le_mul_of_nonneg_right hSmall (show 0 ≤ τ*(m:ℝ) by positivity)
    nlinarith only [hTerm,hD,hSize,hετ,
      show 0 ≤ τ^2*(m:ℝ) by positivity]

private theorem UniformRefinementOf.adapt_with_bounds {V J : Type*}
    {profiles : J → Finset V} {P Q : Finset V} {ℓ m₀ m D : ℕ} {ε ε' : ℝ}
    (R : UniformRefinementOf (I := Fin ℓ) profiles P m₀ ε)
    (hℓ : 0 < ℓ) (hSize : Q.card = ℓ*m) (hm : m ≤ m₀)
    (hParent : max (P \ Q).card (Q \ P).card ≤ D)
    (hBounds : RefinementAdaptationBounds ℓ m₀ m D ε ε') :
    ∃ S : UniformRefinementOf (I := Fin ℓ) profiles Q m ε',
      ∀ i, max (R.cells i \ S.cells i).card (S.cells i \ R.cells i).card ≤ D+(m₀-m) := by
  have hOld : P.card = ℓ*m₀ := by simpa only [Fintype.card_fin] using R.card_parent
  obtain ⟨S,hS⟩ := R.exists_adapted hℓ hBounds.growth.1
    (hBounds.growth.1.trans hBounds.growth.2) hBounds.growth.2 hSize hm hParent
    (by rw [hOld,hSize]; exact hBounds.floor) (by rw [hSize]; exact hBounds.error)
  refine ⟨S,fun i => ?_⟩
  have hl := card_sdiff_add_card_inter (R.cells i) (S.cells i)
  have hr := card_sdiff_add_card_inter (S.cells i) (R.cells i)
  rw [R.size i,inter_comm] at hl
  rw [S.size i] at hr
  have h := hS i
  exact max_le (by omega) (by omega)

/-- Adapt the three levels to the new primary cell, keeping the base
label of every subcell and bounding the changed vertices at each level. -/
theorem PrimaryNestedRefinement.exists_adapted {V J : Type*}
    {profiles : J → Finset V} {P Q : Finset V} {s p m₀ m D : ℕ}
    {ε₁ ε₂ ε₃ τ₁ τ₂ τ₃ : ℝ}
    (R : PrimaryNestedRefinement profiles P s p m₀ ε₁ ε₂ ε₃)
    (hs : 0 < s) (hp : 0 < p) (hm : m ≤ m₀)
    (hSize : Q.card = s*(p*(2*m))) (hParent : max (P \ Q).card (Q \ P).card ≤ D)
    (h₁ : RefinementAdaptationBounds s (p*(2*m₀)) (p*(2*m)) D ε₁ τ₁)
    (h₂ : RefinementAdaptationBounds p (2*m₀) (2*m) (D+(p*(2*m₀)-p*(2*m))) ε₂ τ₂)
    (h₃ : RefinementAdaptationBounds 2 m₀ m
      (D+(p*(2*m₀)-p*(2*m))+(2*m₀-2*m)) ε₃ τ₃) :
    ∃ S : PrimaryNestedRefinement profiles Q s p m τ₁ τ₂ τ₃,
      (∀ i, max (R.first.cells i \ S.first.cells i).card
        (S.first.cells i \ R.first.cells i).card ≤ D+(p*(2*m₀)-p*(2*m))) ∧
      (∀ i j, max ((R.second i).cells j \ (S.second i).cells j).card
        ((S.second i).cells j \ (R.second i).cells j).card ≤
          D+(p*(2*m₀)-p*(2*m))+(2*m₀-2*m)) ∧
      ∀ i j k, max ((R.halves i j).cells k \ (S.halves i j).cells k).card
        ((S.halves i j).cells k \ (R.halves i j).cells k).card ≤
          D+(p*(2*m₀)-p*(2*m))+(2*m₀-2*m)+(m₀-m) := by
  have hm₂ := Nat.mul_le_mul_left 2 hm
  have hmp := Nat.mul_le_mul_left p hm₂
  obtain ⟨S₁,hS₁⟩ := R.first.adapt_with_bounds hs hSize hmp hParent h₁
  choose S₂ hS₂ using fun i => (R.second i).adapt_with_bounds hp (S₁.size i) hm₂ (hS₁ i) h₂
  choose S₃ hS₃ using fun i j => (R.halves i j).adapt_with_bounds (by decide : 0 < 2)
    ((S₂ i).size j) hm (hS₂ i j) h₃
  exact ⟨⟨S₁,S₂,S₃⟩,hS₁,hS₂,hS₃⟩

/-- The p-cells inherit a uniform profile relative to the primary cell. -/
theorem PrimaryNestedRefinement.second_uniform {V J : Type*}
    {profiles : J → Finset V} {P : Finset V} {s p m : ℕ} {ε₁ ε₂ ε₃ τ : ℝ}
    (R : PrimaryNestedRefinement profiles P s p m ε₁ ε₂ ε₃) (i : Fin s) (j : Fin p)
    (h₁ : 0 ≤ ε₁) (h₁One : ε₁ ≤ 1) (h₂ : 0 ≤ ε₂) (hτ : ε₁ ≤ τ)
    (hThreshold : ε₂ ≤ (1-ε₁)*τ) (hError : ε₁+ε₂*(1+ε₁) ≤ τ) :
    UniformProfileCell profiles P ((R.second i).cells j) (s*p) τ := by
  simpa only [Fintype.card_fin] using R.first.uniform_nested_cell i (R.second i) j
    h₁ h₁One h₂ hτ hThreshold hError

/-- Compose a p-cell profile once more to obtain the primary profile
of a half-cell. -/
theorem PrimaryNestedRefinement.half_uniform {V J : Type*}
    {profiles : J → Finset V} {P : Finset V} {s p m : ℕ} {ε₁ ε₂ ε₃ τ υ : ℝ}
    (R : PrimaryNestedRefinement profiles P s p m ε₁ ε₂ ε₃)
    (i : Fin s) (j : Fin p) (k : Fin 2)
    (hSecond : UniformProfileCell profiles P ((R.second i).cells j) (s*p) τ)
    (hτ : 0 ≤ τ) (hτOne : τ ≤ 1) (hε₃ : 0 ≤ ε₃) (hυ : τ ≤ υ)
    (hThreshold : ε₃ ≤ (1-τ)*υ) (hError : τ+ε₃*(1+τ) ≤ υ) :
    UniformProfileCell profiles P ((R.halves i j).cells k) (s*p*2) υ := by
  have hCard : P.card = (s*p)*((R.second i).cells j).card := by
    rw [(R.second i).size j]
    have h := R.first.card_parent
    simpa only [Fintype.card_fin,Nat.mul_assoc] using h
  exact hSecond.comp (by simpa only [Fintype.card_fin] using (R.halves i j).uniform k)
    (Nat.mul_pos (Nat.zero_lt_of_lt i.isLt) (Nat.zero_lt_of_lt j.isLt)) (by decide) hτ hτOne hε₃ hCard hυ hThreshold hError

/-- The total change budget measured against the smallest cell
pays for each level of the adapted refinement. -/
theorem PrimaryNestedRefinement.exists_adapted_of_small_changes {V J : Type*}
    {profiles : J → Finset V} {P Q : Finset V} {s p m₀ m D : ℕ} {ε τ : ℝ}
    (R : PrimaryNestedRefinement profiles P s p m₀ ε ε ε)
    (hs : 0 < s) (hp : 0 < p) (hm : m ≤ m₀)
    (hSize : Q.card = s*(p*(2*m))) (hParent : max (P \ Q).card (Q \ P).card ≤ D)
    (hε : 0 ≤ ε) (hSmall : ε ≤ τ/4) (hτ : 0 < τ) (hτ₁ : τ ≤ 1)
    (hCost : ((D+(p*(2*m₀)-p*(2*m))+(2*m₀-2*m)+(m₀-m):ℕ):ℝ) ≤ (τ^2/16)*(m:ℝ)) :
    ∃ S : PrimaryNestedRefinement profiles Q s p m τ τ τ,
      (∀ i, max (R.first.cells i \ S.first.cells i).card
        (S.first.cells i \ R.first.cells i).card ≤ D+(p*(2*m₀)-p*(2*m))) ∧
      (∀ i j, max ((R.second i).cells j \ (S.second i).cells j).card
        ((S.second i).cells j \ (R.second i).cells j).card ≤
          D+(p*(2*m₀)-p*(2*m))+(2*m₀-2*m)) ∧
      ∀ i j k, max ((R.halves i j).cells k \ (S.halves i j).cells k).card
        ((S.halves i j).cells k \ (R.halves i j).cells k).card ≤
          D+(p*(2*m₀)-p*(2*m))+(2*m₀-2*m)+(m₀-m) := by
  let B := D+(p*(2*m₀)-p*(2*m))+(2*m₀-2*m)+(m₀-m)
  have hSmallₙ (x y : ℕ) (hx : x ≤ B) (hy : m ≤ y) : (x:ℝ) ≤ (τ^2/16)*(y:ℝ) :=
    (show (x:ℝ) ≤ (B:ℝ) by exact_mod_cast hx).trans
      (hCost.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hy) (by positivity)))
  have h₂ : m ≤ 2*m := by omega
  have hP : m ≤ p*(2*m) := h₂.trans (by
    simpa only [one_mul] using Nat.mul_le_mul_right (2*m) (show 1 ≤ p from hp))
  have hm₂ := Nat.mul_le_mul_left 2 hm
  have hmp := Nat.mul_le_mul_left p hm₂
  apply R.exists_adapted hs hp hm hSize hParent
  · exact .of_small_changes hs hmp hε hSmall hτ hτ₁
      (hSmallₙ _ _ (by dsimp only [B]; omega) hP)
      (hSmallₙ _ _ (by dsimp only [B]; omega) hP)
  · exact .of_small_changes hp hm₂ hε hSmall hτ hτ₁
      (hSmallₙ _ _ (by dsimp only [B]; omega) h₂)
      (hSmallₙ _ _ (by dsimp only [B]; omega) h₂)
  · exact .of_small_changes (by decide) hm hε hSmall hτ hτ₁
      (hSmallₙ _ _ (by dsimp only [B]; omega) le_rfl)
      (hSmallₙ _ _ (by dsimp only [B]; omega) le_rfl)

theorem PrimaryNestedRefinement.uniform_p_and_half_cells {V J : Type*}
    {profiles : J → Finset V} {P : Finset V} {s p m : ℕ} {ε : ℝ}
    (R : PrimaryNestedRefinement profiles P s p m ε ε ε)
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1/8) (i : Fin s) (j : Fin p) :
    UniformProfileCell profiles P ((R.second i).cells j) (s*p) (4*ε) ∧
    ∀ k : Fin 2, UniformProfileCell profiles P ((R.halves i j).cells k) (s*p*2) (8*ε) := by
  have hεSq : ε^2 ≤ ε/8 := by
    have h := mul_le_mul_of_nonneg_left hε₁ hε
    nlinarith only [h]
  have hP := R.second_uniform (τ := 4*ε) i j hε (by linarith only [hε₁]) hε (by linarith only [hε])
    (by nlinarith only [hεSq,hε]) (by nlinarith only [hεSq,hε])
  exact ⟨hP,fun k => R.half_uniform i j k hP (by positivity) (by linarith only [hε₁]) hε
    (by linarith only [hε]) (by nlinarith only [hεSq,hε]) (by nlinarith only [hεSq,hε])⟩

end OverfullWork.DirectedRobustExpansion
