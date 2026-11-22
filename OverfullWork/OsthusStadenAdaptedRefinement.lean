module

public import OverfullWork.OsthusStadenCloseRefinement

@[expose] public section


/-! Quantitative forms of (URef), the adaptation in Lemma 3.12,
and the composition rule before equation (1) of Osthus–Staden. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

noncomputable def profileCount {V : Type*} (X Q : Finset V) : ℝ := (X ∩ Q).card

/-- The count condition in (URef) for a single cell. -/
def UniformProfileCell {V J : Type*} (profiles : J → Finset V)
    (P A : Finset V) (ℓ : ℕ) (ε : ℝ) : Prop :=
  ∀ j, ε*(P.card : ℝ) ≤ profileCount P (profiles j) →
    |profileCount A (profiles j) - profileCount P (profiles j)/(ℓ : ℝ)| ≤
      ε*(profileCount P (profiles j)/(ℓ : ℝ))

/-- A large profile stays large enough for the next split if it clears
that split's threshold after the worst allowed first loss. -/
theorem UniformProfileCell.comp {V J : Type*} {profiles : J → Finset V}
    {P A B : Finset V} {ℓ k : ℕ} {ε δ τ : ℝ}
    (hA : UniformProfileCell profiles P A ℓ ε)
    (hB : UniformProfileCell profiles A B k δ)
    (hℓ : 0 < ℓ) (hk : 0 < k) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hCard : P.card = ℓ*A.card) (hτ : ε ≤ τ) (hThreshold : δ ≤ (1-ε)*τ)
    (hError : ε + δ*(1+ε) ≤ τ) :
    UniformProfileCell profiles P B (ℓ*k) τ := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  intro j hj
  let q := profileCount P (profiles j)
  let a := profileCount A (profiles j)
  let b := profileCount B (profiles j)
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have hc : (P.card : ℝ) = (ℓ : ℝ)*A.card := by exact_mod_cast hCard
  have hA' := hA j ((mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg P.card)).trans hj)
  change |a-q/(ℓ : ℝ)| ≤ ε*(q/(ℓ : ℝ)) at hA'
  have hBounds := abs_le.mp hA'
  have hFloor : δ*(A.card : ℝ) ≤ a := by
    have hLow : τ*(A.card : ℝ) ≤ q/(ℓ : ℝ) := by
      apply (le_div_iff₀ hℓR).mpr
      rw [hc] at hj
      nlinarith only [hj]
    have h1 := mul_le_mul_of_nonneg_right hThreshold (Nat.cast_nonneg A.card)
    have h2 := mul_le_mul_of_nonneg_left hLow (sub_nonneg.mpr hε1)
    linarith only [h1,h2,hBounds.1]
  have hB' := hB j hFloor
  change |b-a/(k : ℝ)| ≤ δ*(a/(k : ℝ)) at hB'
  have hUpper : a ≤ (1+ε)*(q/(ℓ : ℝ)) := by linarith only [hBounds.2]
  have hUpper' := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hUpper hkR.le) hδ
  have hBudget := mul_le_mul_of_nonneg_right hError (div_nonneg (div_nonneg hq hℓR.le) hkR.le)
  change |b-q/((ℓ*k : ℕ) : ℝ)| ≤ τ*(q/((ℓ*k : ℕ) : ℝ))
  rw [Nat.cast_mul, ← div_div, show b-q/(ℓ : ℝ)/(k : ℝ) =
    (b-a/(k : ℝ))+(a-q/(ℓ : ℝ))/(k : ℝ) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_div,abs_of_pos hkR]
  have hATerm := div_le_div_of_nonneg_right hA' hkR.le
  have hTotal := add_le_add hB' hATerm
  apply hTotal.trans
  calc
    δ*(a/(k : ℝ)) + ε*(q/(ℓ : ℝ))/(k : ℝ) ≤
        δ*((1+ε)*(q/(ℓ : ℝ))/(k : ℝ)) + ε*(q/(ℓ : ℝ))/(k : ℝ) :=
      add_le_add_left hUpper' _
    _ = (ε+δ*(1+ε))*(q/(ℓ : ℝ)/(k : ℝ)) := by ring
    _ ≤ _ := hBudget

/-- Transport (URef) between aligned parent clusters and aligned cells
using their explicit vertex losses. -/
theorem UniformProfileCell.adapt {V J : Type*} {profiles : J → Finset V}
    {P P' A A' : Finset V} {ℓ : ℕ} {ε ε' : ℝ} {D d : ℕ}
    (hA : UniformProfileCell profiles P A ℓ ε) (hℓ : 0 < ℓ)
    (hε : 0 ≤ ε) (_hε' : 0 ≤ ε') (hGrowth : ε ≤ ε')
    (hParent : max (P \ P').card (P' \ P).card ≤ D)
    (hCell : max (A \ A').card (A' \ A).card ≤ d)
    (hFloor : ε*(P.card : ℝ)+(D : ℝ) ≤ ε'*(P'.card : ℝ))
    (hError : (d : ℝ)+(1+ε)*(D : ℝ)/(ℓ : ℝ) ≤
      (ε'-ε)*(ε'*(P'.card : ℝ)/(ℓ : ℝ))) :
    UniformProfileCell profiles P' A' ℓ ε' := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  intro j hj
  let q := profileCount P (profiles j)
  let q' := profileCount P' (profiles j)
  let a := profileCount A (profiles j)
  let a' := profileCount A' (profiles j)
  have hP : |q-q'| ≤ (D : ℝ) :=
    (profile_count_dist_le P P' (profiles j)).trans (by exact_mod_cast hParent)
  have hAb : |a'-a| ≤ (d : ℝ) := by
    rw [abs_sub_comm]
    exact (profile_count_dist_le A A' (profiles j)).trans (by exact_mod_cast hCell)
  have hOld := hA j (by linarith only [hFloor,hj,(abs_le.mp hP).1])
  change |a-q/(ℓ : ℝ)| ≤ ε*(q/(ℓ : ℝ)) at hOld
  have hQ : q ≤ q'+D := by linarith only [(abs_le.mp hP).2]
  have hOld' := hOld.trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hQ hℓR.le) hε)
  have hScaled : |(q-q')/(ℓ : ℝ)| ≤ (D : ℝ)/(ℓ : ℝ) := by
    rw [abs_div,abs_of_pos hℓR]
    exact div_le_div_of_nonneg_right hP hℓR.le
  have hBudget := hError.trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hj hℓR.le) (sub_nonneg.mpr hGrowth))
  change |a'-q'/(ℓ : ℝ)| ≤ ε'*(q'/(ℓ : ℝ))
  rw [show a'-q'/(ℓ : ℝ) = (a'-a)+(a-q/(ℓ : ℝ))+(q-q')/(ℓ : ℝ) by ring]
  calc
    _ ≤ |a'-a|+|a-q/(ℓ : ℝ)|+|(q-q')/(ℓ : ℝ)| := by
      exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ (d : ℝ)+ε*((q'+D)/(ℓ : ℝ))+(D : ℝ)/(ℓ : ℝ) :=
      add_le_add (add_le_add hAb hOld') hScaled
    _ = ε*(q'/(ℓ : ℝ))+((d : ℝ)+(1+ε)*(D : ℝ)/(ℓ : ℝ)) := by ring
    _ ≤ _ := by
      calc
        _ ≤ ε*(q'/(ℓ : ℝ))+(ε'-ε)*(q'/(ℓ : ℝ)) := add_le_add_right hBudget _
        _ = _ := by ring

/-- Construct a close, uniform refinement of an adapted parent, with the
cellwise closeness inherited from the loss suffered by the parent. -/
theorem exists_adapted_profile_refinement {V J : Type*} (profiles : J → Finset V)
    (P P' : Finset V) (ℓ m₀ m D : ℕ) (old : Fin ℓ → Finset V) (ε ε' : ℝ)
    (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (_hε' : 0 ≤ ε') (hGrowth : ε ≤ ε')
    (hSize : P'.card = ℓ*m) (hm : m ≤ m₀)
    (hParent : max (P \ P').card (P' \ P).card ≤ D)
    (hOld : ∀ i, old i ⊆ P ∧ (old i).card = m₀ ∧ UniformProfileCell profiles P (old i) ℓ ε)
    (hDis : ∀ i j, i ≠ j → Disjoint (old i) (old j))
    (hFloor : ε*(P.card : ℝ)+(D : ℝ) ≤ ε'*(P'.card : ℝ))
    (hError : ((D+(m₀-m):ℕ) : ℝ)+(1+ε)*(D : ℝ)/(ℓ : ℝ) ≤
      (ε'-ε)*(ε'*(P'.card : ℝ)/(ℓ : ℝ))) :
    ∃ cells : Fin ℓ → Finset V,
      (∀ i, (cells i).card = m ∧ m-D ≤ (cells i ∩ old i).card ∧
        UniformProfileCell profiles P' (cells i) ℓ ε') ∧
      (∀ i j, i ≠ j → Disjoint (cells i) (cells j)) ∧ univ.biUnion cells = P' := by
  have hOverlap (i : Fin ℓ) : m-D ≤ (old i ∩ P').card := by
    have hSub : old i \ P' ⊆ P \ P' := by
      intro x hx
      obtain ⟨hx,hx'⟩ := mem_sdiff.mp hx
      exact mem_sdiff.mpr ⟨(hOld i).1 hx,hx'⟩
    have hD := (card_le_card hSub).trans ((le_max_left _ _).trans hParent)
    have hCount := card_sdiff_add_card_inter (old i) P'
    rw [(hOld i).2.1] at hCount
    omega
  obtain ⟨cells,hCells,hCellsDis,hCover⟩ := exists_close_refinement P' old m D
    (by simpa only [Fintype.card_fin] using hSize) hOverlap hDis
  refine ⟨cells,fun i => ⟨(hCells i).1,(hCells i).2,?_⟩,hCellsDis,hCover⟩
  apply (hOld i).2.2.adapt hℓ hε _hε' hGrowth hParent _ hFloor hError
  have hCA := card_sdiff_add_card_inter (cells i) (old i)
  have hAC := card_sdiff_add_card_inter (old i) (cells i)
  rw [(hCells i).1] at hCA
  rw [(hOld i).2.1,inter_comm] at hAC
  exact max_le (by have := (hCells i).2; omega) (by have := (hCells i).2; omega)

end OverfullWork.DirectedRobustExpansion
