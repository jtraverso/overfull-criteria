module

public import OverfullWork.ChenShanCommonNeighborTails
public import OverfullWork.ChenShanReserveNeighborhoodMean
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

private theorem sdiff_filter_eq {V : Type*} (T : Finset V) (E : V → Prop) :
    T \ T.filter E = T.filter (fun v => ¬E v) := by
  ext v
  simp only [mem_sdiff,mem_filter]
  tauto

private theorem count_filter_lower {V : Type*} (T : Finset V) (E : V → Prop) {a d : ℝ}
    (hSize : a ≤ (T.card : ℝ)) (hMissing : ((T.filter (fun v => ¬E v)).card : ℝ) ≤ d) :
    a-d ≤ ((T.filter E).card : ℝ) := by
  have hCard : ((T.filter E).card : ℝ)+((T.filter (fun v => ¬ E v)).card : ℝ) = T.card := by
    exact_mod_cast card_filter_add_card_filter_not E
  linarith only [hSize,hMissing,hCard]

private theorem masked_common_lower {V : Type*} (T : Finset V) (E F : V → Prop) {a d : ℝ}
    (hDegree : a ≤ ((T.filter E).card : ℝ))
    (hMissing : ((T.filter (fun v => ¬F v)).card : ℝ) ≤ d) :
    a-d ≤ ((T.filter (fun v => E v ∧ F v)).card : ℝ) := by
  have h := reserve_common_neighborhood_lower (T.filter E) (T.filter F) T
    (filter_subset _ _) (d := d) hDegree (by rw [sdiff_filter_eq]; exact hMissing)
  have hEq : T.filter E ∩ T.filter F = T.filter (fun v => E v ∧ F v) := by
    ext v
    simp only [mem_inter,mem_filter]
    tauto
  simpa only [hEq] using h

/-- Lower candidate counts for the three possible types of an (R3)
edge. The calculation uses only (4.23) and the prefix sizes. -/
theorem crossing_common_neighbor_candidates
    {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    {S : NestedTripartitePrefixes A B W ρ m k l} {i : ℕ}
    {δ : ℝ} (hb : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i))
    (hi : i+1 ≤ l) (hHalf : 1/2 ≤ (k:ℝ)/m)
    (hInner : ρ*(nestedCoreSize ρ m i : ℝ) ≤ nestedCoreSize ρ m (i+1))
    (hδ : 0 ≤ δ) (hSmall : 18*δ ≤ ρ)
    (hRound : 1/2 ≤ δ*nestedCoreSize ρ m i) :
    let n : ℝ := nestedCoreSize ρ m i
    (∀ a ∈ S.left i, ∀ b ∈ S.right i,
      ρ*n/3 ≤ (((S.colors (i+1)).filter (fun w => P a w ∧ Q b w)).card : ℝ)) ∧
    (∀ a ∈ S.left i, ∀ w ∈ S.colors i,
      ρ*n/3 ≤ (((S.right (i+1)).filter (fun b => F a b ∧ Q b w)).card : ℝ)) ∧
    (∀ b ∈ S.right i, ∀ w ∈ S.colors i,
      ρ*n/3 ≤ (((S.left (i+1)).filter (fun a => F a b ∧ P a w)).card : ℝ)) := by
  dsimp only
  let n : ℝ := nestedCoreSize ρ m i
  let s : ℝ := nestedCoreSize ρ m (i+1)
  let p : ℝ := (k:ℝ)/m
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hp := mul_le_mul_of_nonneg_right hHalf hs
  have hps : ρ*n/2 ≤ p*s := by linarith only [hInner,hp]
  have hδn := mul_nonneg hδ hn
  have hBudget := mul_le_mul_of_nonneg_right hSmall hn
  have hScale : s/m*k = p*s := by dsimp [p]; ring
  have hColor := (abs_le.mp (S.crossing_color_sizes hi).1).1
  obtain ⟨hAW,hBW,hWA,hWB⟩ := hb.missing_neighbors (by
    by_contra! h
    have hm : m=0 := by omega
    rw [hm,Nat.cast_zero,div_zero] at hHalf
    norm_num at hHalf) 1 (by decide) hi
  refine ⟨?_,?_,?_⟩
  · intro a ha b hb'
    have hDeg : p*s-1/2-δ*n ≤ (((S.colors (i+1)).filter (P a)).card : ℝ) :=
      count_filter_lower _ _ (by linarith only [hColor]) (hAW a ha)
    have h := masked_common_lower (S.colors (i+1)) (P a) (Q b) hDeg (hBW b hb')
    linarith only [h,hps,hBudget,hRound]
  · intro a ha w hw
    have h := (abs_le.mp (hb.leftRight 1 (by decide) hi a ha).1).1
    change -(δ*n) ≤ (((S.right (i+1)).filter (F a)).card : ℝ)-s/m*k at h
    rw [hScale] at h
    have hDeg : p*s-δ*n ≤ (((S.right (i+1)).filter (F a)).card : ℝ) :=
      by linarith only [h]
    have hc := masked_common_lower (S.right (i+1)) (F a) (fun b => Q b w) hDeg (hWB w hw)
    linarith only [hc,hps,hBudget,hδn]
  · intro b hb' w hw
    have h := (abs_le.mp (hb.rightLeft 1 (by decide) hi b hb').1).1
    change -(δ*n) ≤ (((S.left (i+1)).filter (fun a => F a b)).card : ℝ)-s/m*k at h
    rw [hScale] at h
    have hDeg : p*s-δ*n ≤ (((S.left (i+1)).filter (fun a => F a b)).card : ℝ) :=
      by linarith only [h]
    have hc := masked_common_lower (S.left (i+1)) (fun a => F a b) (fun a => P a w) hDeg (hWA w hw)
    linarith only [hc,hps,hBudget,hδn]

/-- Every (R3) candidate set in the inner prefix has at most 8ρn vertices. -/
theorem crossing_inner_vertices_card_le (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (hi : i+1 ≤ l) (hm : 0 < m) (hk : (k:ℝ) ≤ (3/2)*(m:ℝ))
    (hs : 1 ≤ nestedCoreSize ρ m (i+1))
    (hSize : (nestedCoreSize ρ m (i+1) : ℝ) ≤ 2*ρ*nestedCoreSize ρ m i) :
    ((S.vertices (i+1)).card : ℝ) ≤ 8*ρ*nestedCoreSize ρ m i := by
  have hNat := S.vertices_card_le hm hk (i+1) hi hs
  have hReal : ((S.vertices (i+1)).card : ℝ) ≤ 4*(nestedCoreSize ρ m (i+1) : ℝ) :=
    by exact_mod_cast hNat
  linarith only [hReal,hSize]

end OverfullWork.ChenShan
