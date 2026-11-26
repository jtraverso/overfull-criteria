module

public import OverfullWork.ChenShanIterationDegrees
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

private theorem filter_sdiff_card_add {V : Type*} (P : V → Prop)
    (T U : Finset V) (hU : U ⊆ T) :
    ((T \ U).filter P).card+(U.filter P).card = (T.filter P).card := by
  have h : (T \ U).filter P = T.filter P \ U.filter P := by
    ext v
    simp only [mem_filter,mem_sdiff]
    tauto
  rw [h]
  exact card_sdiff_add_card_eq_card (filter_subset_filter P hU)

/-- Splitting the target part into the next prefix and its complement gives
the two degree estimates used for a crossing pair in Step 2. -/
theorem ResidualPrefixPairBounds.crossing_degree_errors
    {X Y : Type*} {F : X → Y → Prop} {source : Finset X} {T : ℕ → Finset Y}
    {ρ : ℝ} {m i l D : ℕ} {budget : ℝ}
    (h : ResidualPrefixPairBounds F source T ρ m i l D budget)
    (hNext : i+1 ≤ l) (hT : T (i+1) ⊆ T i) :
    ∀ v ∈ source,
      |(((T (i+1)).filter (F v)).card : ℝ) -
        ((nestedCoreSize ρ m (i+1) : ℝ)/m)*D| ≤ budget ∧
      |((((T i \ T (i+1)).filter (F v)).card) : ℝ) -
        (((nestedCoreSize ρ m i : ℝ)-(nestedCoreSize ρ m (i+1) : ℝ))/m)*D| ≤ 2*budget := by
  intro v hv
  have hCurrent := (h 0 (by omega) (by omega) v hv).1
  have hInside := (h 1 (by omega) hNext v hv).1
  refine ⟨hInside,?_⟩
  simp only [Nat.add_zero] at hCurrent
  have hCard : ((((T i \ T (i+1)).filter (F v)).card) : ℝ) +
      (((T (i+1)).filter (F v)).card : ℝ) = (((T i).filter (F v)).card : ℝ) := by
    exact_mod_cast filter_sdiff_card_add (F v) (T i) (T (i+1)) hT
  have hCenter :
      (((nestedCoreSize ρ m i : ℝ)-(nestedCoreSize ρ m (i+1) : ℝ))/m)*D =
        ((nestedCoreSize ρ m i : ℝ)/m)*D-((nestedCoreSize ρ m (i+1) : ℝ)/m)*D := by ring
  rw [hCenter]
  exact abs_le.mpr ⟨by linarith only [hCard,(abs_le.mp hCurrent).1,(abs_le.mp hInside).2],
    by linarith only [hCard,(abs_le.mp hCurrent).2,(abs_le.mp hInside).1]⟩

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- For the four core–color directions, the target-size condition of
(4.23) is automatic from the exact core sizes and the rounded color sizes. -/
theorem TripartiteResidualPrefixBounds.missing_neighbors
    {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    {S : NestedTripartitePrefixes A B W ρ m k l} {i : ℕ} {budget : ℝ}
    (hb : TripartiteResidualPrefixBounds F P Q S i budget)
    (hm : 0 < m) (t : ℕ) (ht : t ≤ 1) (hEnd : i+t ≤ l) :
    (∀ a ∈ S.left i, (((S.colors (i+t)).filter fun w => ¬P a w).card : ℝ) ≤ budget) ∧
    (∀ b ∈ S.right i, (((S.colors (i+t)).filter fun w => ¬Q b w).card : ℝ) ≤ budget) ∧
    (∀ w ∈ S.colors i, (((S.left (i+t)).filter fun a => ¬P a w).card : ℝ) ≤ budget) ∧
    (∀ w ∈ S.colors i, (((S.right (i+t)).filter fun b => ¬Q b w).card : ℝ) ≤ budget) := by
  let s := nestedCoreSize ρ m (i+t)
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hColor : |(((S.colors (i+t)).card : ℝ))-((s:ℝ)/m)*k| ≤ 1/2 := by
    rw [S.colorsSize _ hEnd]
    change |(nestedColorSize ((k:ℝ)/m) s : ℝ)-((s:ℝ)/m)*k| ≤ 1/2
    rw [show ((s:ℝ)/m)*k = ((k:ℝ)/m)*s by ring]
    exact nestedColorSize_error ((k:ℝ)/m) (by positivity) s
  have hCore : |(s:ℝ)-((s:ℝ)/m)*m| ≤ 1/2 := by rw [div_mul_cancel₀ _ hmR.ne',sub_self,abs_zero]; norm_num
  refine ⟨fun a ha => (hb.leftColors t ht hEnd a ha).2 hColor,
    fun b hb' => (hb.rightColors t ht hEnd b hb').2 hColor, ?_, ?_⟩
  · intro w hw
    apply (hb.colorsLeft t ht hEnd w hw).2
    simpa only [S.leftSize _ hEnd] using hCore
  · intro w hw
    apply (hb.colorsRight t ht hEnd w hw).2
    simpa only [S.rightSize _ hEnd] using hCore

end OverfullWork.ChenShan
