module

public import OverfullWork.ChenShanCrossingPrefixDegrees
public import OverfullWork.ChenShanBalancedReserve
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

/-- Rounding the target class up by at most one and losing at most
(2 δ n) in its degree still leaves the gap needed for Lemma 4.12. -/
theorem crossing_min_degree {n ρ δ η size ideal deg : ℝ}
    (hn : 0 ≤ n) (hη : 0 ≤ η)
    (hSlack : 1 ≤ δ*n) (hSmall : 18*δ ≤ η*ρ)
    (hSize : ρ*n/3 ≤ size)
    (hIdeal : (1/2+η)*size ≤ ideal+1)
    (hDegree : |deg-ideal| ≤ 2*δ*n) :
    (1/2+η/2)*size ≤ deg := by
  have hGap := mul_le_mul_of_nonneg_left hSize hη
  have hScale := mul_le_mul_of_nonneg_right hSmall hn
  have hLower := (abs_le.mp hDegree).1
  linarith only [hGap,hScale,hLower,hIdeal,hSlack]

/-- The two directions at a crossing vertex have the same degree center. -/
theorem crossing_relative_balance {n ρ δ ideal out inn : ℝ}
    (hn : 0 < n) (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hSmall : 8*δ ≤ ρ)
    (hIdeal : ρ*n/2 ≤ ideal)
    (hOut : |out-ideal| ≤ 2*δ*n) (hIn : |inn-ideal| ≤ 2*δ*n) :
    |out-inn| ≤ (16*δ/ρ)*min out inn := by
  have hScale := mul_le_mul_of_nonneg_right hSmall hn.le
  have hOut' := abs_le.mp hOut
  have hIn' := abs_le.mp hIn
  have hMin : ρ*n/4 ≤ min out inn :=
    le_min (by linarith only [hScale,hIdeal,hOut'.1]) (by linarith only [hScale,hIdeal,hIn'.1])
  have hAbs : |out-inn| ≤ 4*δ*n := abs_le.mpr
    ⟨by linarith only [hOut'.1,hIn'.2], by linarith only [hOut'.2,hIn'.1]⟩
  refine hAbs.trans ?_
  calc
    _ = (16*δ/ρ)*(ρ*n/4) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hMin (by positivity)

private theorem crossing_sum_size {A : Type*} [Fintype A] (d : A → ℝ)
    {p n t ρ δ : ℝ} (hn : 0 ≤ n) (hρ : 0 < ρ) (hδ : 0 ≤ δ)
    (hp : 1/2 ≤ p) (ht : ρ*n ≤ t)
    (hd : ∀ a, |d a-p*t| ≤ 2*δ*n) :
    |(∑ a, d a)-(Fintype.card A : ℝ)*(p*t)| ≤
      (16*δ/ρ)*((Fintype.card A : ℝ)*(p*t)) := by
  have ht' : 0 ≤ t := (mul_nonneg hρ.le hn).trans ht
  have hp' := mul_le_mul_of_nonneg_right hp ht'
  have hScale : ρ*n/2 ≤ p*t := by linarith only [hp',ht]
  have hLocal := mul_le_mul_of_nonneg_left hScale
    (show 0 ≤ 16*δ/ρ by positivity)
  have hCancel : (16*δ/ρ)*(ρ*n/2) = 8*δ*n := by field_simp; ring
  rw [hCancel] at hLocal
  have hConst : (∑ _ : A, p*t) = (Fintype.card A : ℝ)*(p*t) := by simp [nsmul_eq_mul]
  conv_lhs => rw [← hConst,← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _ : A, (2*δ*n) := sum_le_sum fun a _ => hd a
    _ = (Fintype.card A : ℝ)*(2*δ*n) := by simp [nsmul_eq_mul]
    _ ≤ _ := by
      have hB : 2*δ*n ≤ (16*δ/ρ)*(p*t) := by
        linarith only [hLocal,mul_nonneg hδ hn]
      calc
        _ ≤ (Fintype.card A : ℝ)*((16*δ/ρ)*(p*t)) :=
          mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
        _ = _ := by ring

/-- Every crossing pair has an unrounded core class. Summing the degrees
on that side gives the common expected edge count without a size-rounding
term. The two orientations of the core side use the same estimate. -/
theorem crossing_pair_size_from_core {A B : Type*} [Fintype A] [Fintype B]
    (E : A → B → Prop) {p n t ρ δ : ℝ}
    (hn : 0 ≤ n) (hρ : 0 < ρ) (hδ : 0 ≤ δ)
    (hp : 1/2 ≤ p) (ht : ρ*n ≤ t) :
    ((∀ a, |reserveOutDegree E a-p*t| ≤ 2*δ*n) →
      |reservePairSize E-(Fintype.card A : ℝ)*(p*t)| ≤
        (16*δ/ρ)*((Fintype.card A : ℝ)*(p*t))) ∧
    ((∀ b, |reserveInDegree E b-p*t| ≤ 2*δ*n) →
      |reservePairSize E-(Fintype.card B : ℝ)*(p*t)| ≤
        (16*δ/ρ)*((Fintype.card B : ℝ)*(p*t))) := by
  constructor
  · exact crossing_sum_size (reserveOutDegree E) hn hρ hδ hp ht
  · rw [← sum_reserveInDegree E]
    exact crossing_sum_size (reserveInDegree E) hn hρ hδ hp ht

/-- The inner and outer core sizes both admit the same lower scale. -/
theorem nested_crossing_core_window {ρ : ℝ} {m i : ℕ}
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4)
    (hRound : 1 ≤ ρ*(nestedCoreSize ρ m i : ℝ)) :
    let n : ℝ := nestedCoreSize ρ m i
    let s : ℝ := nestedCoreSize ρ m (i+1)
    ρ*n ≤ s ∧ s ≤ 2*ρ*n ∧ ρ*n ≤ n-s := by
  dsimp only
  have hLo := nestedCoreSize_step_lower ρ m i
  have hHi := nestedCoreSize_step_upper ρ hρ.le m i
  have hρn := mul_le_mul_of_nonneg_right hρsmall (Nat.cast_nonneg (α := ℝ) (nestedCoreSize ρ m i))
  exact ⟨hLo, by linarith only [hHi,hRound], by linarith only [hHi,hRound,hρn]⟩

/-- If a target part has ideal size (q t), the core scale and
the rounding error bound give the size and degree premises for the
crossing minimum-degree estimate. -/
theorem crossing_target_geometry {n ρ η q t size ideal : ℝ}
    (hn : 0 ≤ n) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hηhalf : η ≤ 1/2)
    (hInit : 6 ≤ ρ*n) (hq : 1/2 ≤ q) (ht : ρ*n ≤ t)
    (hSize : |size-q*t| ≤ 1) (hIdeal : (1/2+η)*(q*t) ≤ ideal) :
    ρ*n/3 ≤ size ∧ (1/2+η)*size ≤ ideal+1 := by
  have ht₀ : 0 ≤ t := (mul_nonneg hρ hn).trans ht
  have hq₀ := mul_le_mul_of_nonneg_right hq ht₀
  have hR := abs_le.mp hSize
  have hUpper : (1/2+η)*size ≤ (1/2+η)*(q*t+1) :=
    mul_le_mul_of_nonneg_left (by linarith only [hR.2]) (by positivity)
  exact ⟨by linarith only [hInit,ht,hq₀,hR.1],
    by linarith only [hηhalf,hUpper,hIdeal]⟩

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

/-- The color class in the next level costs at most half a vertex in
rounding. Subtracting two rounded counts costs at most one vertex. -/
theorem NestedTripartitePrefixes.crossing_color_sizes {ρ : ℝ} {m k l i : ℕ}
    (S : NestedTripartitePrefixes A B W ρ m k l) (hNext : i+1 ≤ l) :
    let p : ℝ := (k : ℝ)/m
    let n : ℝ := nestedCoreSize ρ m i
    let s : ℝ := nestedCoreSize ρ m (i+1)
    |((S.colors (i+1)).card : ℝ)-p*s| ≤ 1/2 ∧
      |(((S.colors i \ S.colors (i+1)).card : ℝ))-p*(n-s)| ≤ 1 := by
  dsimp only
  let q : ℝ := (k:ℝ)/m
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hSize (j : ℕ) (hj : j ≤ l) :
      |((S.colors j).card : ℝ)-q*(nestedCoreSize ρ m j : ℝ)| ≤ 1/2 := by
    rw [S.colorsSize j hj]
    exact nestedColorSize_error q hq _
  have hNested := S.colorsAntitone (Nat.le_succ i)
  have hCard : (((S.colors i \ S.colors (i+1)).card : ℝ)) +
      ((S.colors (i+1)).card : ℝ) = (S.colors i).card := by
    exact_mod_cast card_sdiff_add_card_eq_card hNested
  have hNow := abs_le.mp (hSize i (by omega))
  have hNext' := abs_le.mp (hSize (i+1) hNext)
  refine ⟨hSize _ hNext, abs_le.mpr ?_⟩
  change -1 ≤ ((S.colors i \ S.colors (i+1)).card : ℝ) -
      q*((nestedCoreSize ρ m i : ℝ)-(nestedCoreSize ρ m (i+1) : ℝ)) ∧ _
  constructor <;> linarith only [hCard,hNow.1,hNow.2,hNext'.1,hNext'.2]

/-- Local balance forces the color proportion to reach the density
of the base pair. -/
theorem DenseTripartite.color_ratio_lower
    {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}
    {m : ℕ} {η ε : ℝ} (G : DenseTripartite E L R m η ε) (hm : 0 < m) :
    1/2+η ≤ (Fintype.card W : ℝ)/m := by
  have hNonempty : Nonempty A := Fintype.card_pos_iff.mp (by rwa [G.sizeA])
  let a := hNonempty.some
  have hDegree : (1/2+η)*(m:ℝ) ≤ ((univ.filter (L a)).card : ℝ) := by
    have hEq := G.balanced.1 a
    rw [Fintype.card_subtype,Fintype.card_subtype] at hEq
    simpa only [hEq] using G.degreeA a
  apply (le_div_iff₀ (show (0:ℝ) < m by exact_mod_cast hm)).mpr
  exact hDegree.trans (by exact_mod_cast card_le_univ (univ.filter (L a)))

/-- The circulation lemma applies once both incident degrees at a vertex
are controlled by the same crossing center. -/
theorem exists_balanced_reserve_of_crossing_estimates
    {J : Type*} [Fintype J] [Nonempty J] {V : J → Type*} [∀ j, Fintype (V j)]
    (next : J ≃ J) (E : (i j : J) → V i → V j → Prop)
    (g : (i : J) → V i → ℝ) {η ρ δ n μ e : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hn : 0 < n)
    (hSmall : 8*δ ≤ ρ)
    (hθsmall : 16*δ/ρ ≤ 1/4) (hθtight : (8/η)*(16*δ/ρ) < 1/2)
    (hμ : 0 < μ) (hμupper : μ < 1/4) (he : 0 < e)
    (hOutMin : ∀ i a, (1/2+η/2)*(Fintype.card (V (next i)) : ℝ) ≤
      reserveOutDegree (E i (next i)) a)
    (hInMin : ∀ i b, (1/2+η/2)*(Fintype.card (V i) : ℝ) ≤
      reserveInDegree (E i (next i)) b)
    (hSizes : ∀ i, |reservePairSize (E i (next i))-e| ≤ (16*δ/ρ)*e)
    (hCenter : ∀ i a, ρ*n/2 ≤ g i a)
    (hOut : ∀ i a, |reserveOutDegree (E i (next i)) a-g i a| ≤ 2*δ*n)
    (hIn : ∀ i a, |reserveInDegree (E (next.symm i) i) a-g i a| ≤ 2*δ*n) :
    ∃ p : (i : J) → V i → V (next i) → ℝ,
      (∀ i a b, ¬E i (next i) a b → p i a b = 0) ∧
      (∀ i a b, E i (next i) a b →
        p i a b ∈ Set.Ioo (0 : ℝ) 1 ∧ |p i a b-μ| ≤ μ*((8/η)*(16*δ/ρ))) ∧
      (∀ i (a : V (next i)), (∑ b, p (next i) a b) = ∑ b, p i b a) := by
  have hGap : 2*(1/2+η/2)-1 = η := by ring
  obtain ⟨p,hZero,hProb,hBal,_⟩ := exists_balanced_reserve_probabilities next E
    (1/2+η/2) (16*δ/ρ) μ e (by linarith only [hη]) (by positivity) hθsmall
    (by rw [hGap]; exact hθtight) hμ hμupper he hOutMin hInMin hSizes (by
      intro i a
      exact crossing_relative_balance hn hρ hδ hSmall (hCenter i a) (hOut i a) (hIn i a))
  rw [hGap] at hProb
  exact ⟨p,hZero,hProb,hBal⟩

end OverfullWork.ChenShan
