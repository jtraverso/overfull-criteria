module

public import OverfullWork.ChenShanInnerReserveGeometry
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

private theorem missed_filter_card {V : Type*} (T : Finset V) (E : V → Prop) :
    T \ T.filter E = T.filter (fun x => ¬E x) := by
  ext x
  simp only [mem_filter,mem_sdiff]
  tauto

private theorem filter_inter_filter {V : Type*} (T : Finset V) (E F : V → Prop) :
    T.filter E ∩ T.filter F = T.filter (fun x => E x ∧ F x) := by
  ext x
  simp only [mem_filter,mem_inter]
  tauto

private theorem neighborhood_margin_core {V : Type*}
    (T : Finset V) (E F : V → Prop) {t e η₀ : ℝ}
    (hη₀ : η₀ ≤ 1/80) (hSize : t/4 ≤ ((T.filter E).card : ℝ))
    (hError : e ≤ t/16) (hMissing : ((T.filter (fun x => ¬F x)).card : ℝ) ≤ e) :
    (1/2+20*η₀)*((T.filter E).card : ℝ) ≤ ((T.filter (fun x => E x ∧ F x)).card : ℝ) := by
  have hCommon := reserve_common_neighborhood_lower (T.filter E) (T.filter F) T
    (filter_subset _ _) (a := ((T.filter E).card : ℝ)) (d := e) le_rfl (by
      rw [missed_filter_card]
      exact hMissing)
  rw [filter_inter_filter] at hCommon
  have hGap : (1/2+20*η₀)*((T.filter E).card : ℝ) ≤ (3/4)*((T.filter E).card : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith only [hη₀]) (Nat.cast_nonneg _)
  linarith only [hCommon,hGap,hSize,hError]

private theorem neighborhood_margin_color {V : Type*}
    (T : Finset V) (E F : V → Prop) {p e η η₀ : ℝ}
    (hη₀ : 0 ≤ η₀) (hEta : 40*η₀ ≤ η) (hp : 1/2+η ≤ p)
    (hError : 4*e ≤ η*(T.card : ℝ))
    (hMissing : ((T.filter (fun x => ¬E x)).card : ℝ) ≤ e)
    (hDegree : p*(T.card : ℝ)-e ≤ ((T.filter F).card : ℝ)) :
    (1/2+20*η₀)*((T.filter E).card : ℝ) ≤ ((T.filter (fun x => E x ∧ F x)).card : ℝ) := by
  have hCommon := reserve_common_neighborhood_lower (T.filter F) (T.filter E) T
    (filter_subset _ _) hDegree (d := e) (by rw [missed_filter_card]; exact hMissing)
  rw [inter_comm,filter_inter_filter] at hCommon
  have hGap := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) T.card)
  have h20 := mul_le_mul_of_nonneg_right hEta (Nat.cast_nonneg (α := ℝ) T.card)
  have hCard : ((T.filter E).card : ℝ) ≤ T.card := by exact_mod_cast card_filter_le T E
  have hFinal := mul_le_mul_of_nonneg_left hCard (show 0 ≤ 1/2+20*η₀ by positivity)
  linarith only [hCommon,hGap,hFinal,hError,h20]

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- The six deterministic neighborhood proportions that precede (R4),
for an outer vertex and an inner vertex in each compatible part. -/
theorem crossing_r4_candidate_margins
    {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    {S : NestedTripartitePrefixes A B W ρ m k l} {i : ℕ} {δ η η₀ : ℝ}
    (hBounds : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hi : i+1 ≤ l) (hm : 0 < m)
    (hη₀ : 0 ≤ η₀) (hη₀small : η₀ ≤ 1/80) (hEta : 40*η₀ ≤ η)
    (hp : 1/2+η ≤ (k:ℝ)/m) (hBudget : 16*δ ≤ ρ) (hColor : 4*δ ≤ η*ρ) :
    (∀ a ∈ S.left i, ∀ b ∈ S.right (i+1),
      (1/2+20*η₀)*(((S.colors (i+1)).filter (fun w => P a w)).card : ℝ) ≤
        (((S.colors (i+1)).filter (fun w => P a w ∧ Q b w)).card : ℝ)) ∧
    (∀ a ∈ S.left i, ∀ w ∈ S.colors (i+1),
      (1/2+20*η₀)*(((S.right (i+1)).filter (fun b => F a b)).card : ℝ) ≤
        (((S.right (i+1)).filter (fun b => F a b ∧ Q b w)).card : ℝ)) ∧
    (∀ b ∈ S.right i, ∀ a ∈ S.left (i+1),
      (1/2+20*η₀)*(((S.colors (i+1)).filter (fun w => Q b w)).card : ℝ) ≤
        (((S.colors (i+1)).filter (fun w => Q b w ∧ P a w)).card : ℝ)) ∧
    (∀ b ∈ S.right i, ∀ w ∈ S.colors (i+1),
      (1/2+20*η₀)*(((S.left (i+1)).filter (fun a => F a b)).card : ℝ) ≤
        (((S.left (i+1)).filter (fun a => F a b ∧ P a w)).card : ℝ)) ∧
    (∀ w ∈ S.colors i, ∀ a ∈ S.left (i+1),
      (1/2+20*η₀)*(((S.right (i+1)).filter (fun b => Q b w)).card : ℝ) ≤
        (((S.right (i+1)).filter (fun b => Q b w ∧ F a b)).card : ℝ)) ∧
    (∀ w ∈ S.colors i, ∀ b ∈ S.right (i+1),
      (1/2+20*η₀)*(((S.left (i+1)).filter (fun a => P a w)).card : ℝ) ≤
        (((S.left (i+1)).filter (fun a => P a w ∧ F a b)).card : ℝ)) := by
  let n : ℝ := nestedCoreSize ρ m i
  let s : ℝ := nestedCoreSize ρ m (i+1)
  let p : ℝ := (k:ℝ)/m
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hη : 0 ≤ η := by linarith only [hEta,hη₀]
  have hHalf : 1/2 ≤ p := by linarith only [hp,hη]
  have hScale : s/m*k = p*s := by dsimp [p]; ring
  have hCore := nestedCoreSize_step_lower ρ m i
  change ρ*n ≤ s at hCore
  have hps : ρ*n/2 ≤ p*s := by
    have hh := mul_le_mul_of_nonneg_right hHalf hs
    linarith only [hh,hCore]
  have hE : δ*n ≤ ρ*n/16 := by
    have hh := mul_le_mul_of_nonneg_right hBudget hn
    linarith only [hh]
  have hC : 4*(δ*n) ≤ η*s := by
    have hh := mul_le_mul_of_nonneg_right hColor hn
    have hh' := mul_le_mul_of_nonneg_left hCore hη
    linarith only [hh,hh']
  obtain ⟨hAW,hBW,hWA,hWB⟩ := hBounds.missing_neighbors hm 1 (by decide) hi
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro a ha b hb
    have hCurr := S.rightAntitone (Nat.le_succ i) hb
    have h := (abs_le.mp (hBounds.leftColors 1 (by decide) hi a ha).1).1
    change -(δ*n) ≤ (((S.colors (i+1)).filter (fun w => P a w)).card : ℝ)-s/m*k at h
    rw [hScale] at h
    apply neighborhood_margin_core (S.colors (i+1)) (fun w => P a w) (fun w => Q b w)
      hη₀small (t := ρ*n) (e := δ*n) (by linarith only [h,hps,hE]) hE
    exact hBW b hCurr
  · intro a ha w hw
    have hCurr := S.colorsAntitone (Nat.le_succ i) hw
    have h := (abs_le.mp (hBounds.leftRight 1 (by decide) hi a ha).1).1
    change -(δ*n) ≤ (((S.right (i+1)).filter (fun b => F a b)).card : ℝ)-s/m*k at h
    rw [hScale] at h
    apply neighborhood_margin_core (S.right (i+1)) (fun b => F a b) (fun b => Q b w)
      hη₀small (t := ρ*n) (e := δ*n) (by linarith only [h,hps,hE]) hE
    exact hWB w hCurr
  · intro b hb a ha
    have hCurr := S.leftAntitone (Nat.le_succ i) ha
    have h := (abs_le.mp (hBounds.rightColors 1 (by decide) hi b hb).1).1
    change -(δ*n) ≤ (((S.colors (i+1)).filter (fun w => Q b w)).card : ℝ)-s/m*k at h
    rw [hScale] at h
    apply neighborhood_margin_core (S.colors (i+1)) (fun w => Q b w) (fun w => P a w)
      hη₀small (t := ρ*n) (e := δ*n) (by linarith only [h,hps,hE]) hE
    exact hAW a hCurr
  · intro b hb w hw
    have hCurr := S.colorsAntitone (Nat.le_succ i) hw
    have h := (abs_le.mp (hBounds.rightLeft 1 (by decide) hi b hb).1).1
    change -(δ*n) ≤ (((S.left (i+1)).filter (fun a => F a b)).card : ℝ)-s/m*k at h
    rw [hScale] at h
    apply neighborhood_margin_core (S.left (i+1)) (fun a => F a b) (fun a => P a w)
      hη₀small (t := ρ*n) (e := δ*n) (by linarith only [h,hps,hE]) hE
    exact hWA w hCurr
  · intro w hw a ha
    have hCurr := S.leftAntitone (Nat.le_succ i) ha
    have h := (abs_le.mp (hBounds.leftRight 1 (by decide) hi a hCurr).1).1
    change -(δ*n) ≤ (((S.right (i+1)).filter (fun b => F a b)).card : ℝ)-s/m*k at h
    rw [hScale] at h
    have hSize : ((S.right (i+1)).card : ℝ) = s := by
      rw [S.rightSize _ hi]
    apply neighborhood_margin_color (S.right (i+1)) (fun b => Q b w) (fun b => F a b)
      hη₀ hEta hp (e := δ*n) (by rw [hSize]; exact hC) (hWB w hw)
    rw [hSize]
    linarith only [h]
  · intro w hw b hb
    have hCurr := S.rightAntitone (Nat.le_succ i) hb
    have h := (abs_le.mp (hBounds.rightLeft 1 (by decide) hi b hCurr).1).1
    change -(δ*n) ≤ (((S.left (i+1)).filter (fun a => F a b)).card : ℝ)-s/m*k at h
    rw [hScale] at h
    have hSize : ((S.left (i+1)).card : ℝ) = s := by
      rw [S.leftSize _ hi]
    apply neighborhood_margin_color (S.left (i+1)) (fun a => P a w) (fun a => F a b)
      hη₀ hEta hp (e := δ*n) (by rw [hSize]; exact hC) (hWA w hw)
    rw [hSize]
    linarith only [h]

end OverfullWork.ChenShan
