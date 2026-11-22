module

public import OverfullWork.CMSOperation41ActiveBands

@[expose] public section


/-! Rounding and survival at the two trimming limits. The long limit
uses the exact losses of vertices still in the original low set. -/
namespace OverfullWork.CMSTrimmingRound

open Finset
open scoped Classical

variable {V : Type*} [DecidableEq V]

private theorem low_survivor_pays_for_rounds (W : ℕ → Finset V) (degree : ℕ → V → ℕ)
    (l : ℕ)
    (hNested : ∀ i < l,W (i+1) ⊆ W i)
    (hDrop : ∀ i < l,2 ≤ (W i).card → ∀ v ∈ W (i+1),degree (i+1) v+1 ≤ degree i v)
    (hMany : 2 ≤ (W l).card) (v : V) (hv : v ∈ W l) :
    v ∈ W 0 ∧ degree l v+l ≤ degree 0 v := by
  have hContain (i : ℕ) (hi : i ≤ l) : W l ⊆ W i := by
    have hAll (j : ℕ) (hj : i ≤ j) (hjl : j ≤ l) : W j ⊆ W i := by
      induction j with
      | zero =>
        have he : i = 0 := by omega
        subst i
        exact Subset.rfl
      | succ j ih =>
        by_cases he : i = j+1
        · rw [he]
        · exact (hNested j (by omega)).trans (ih (by omega) (by omega))
    exact hAll l hi le_rfl
  have hTotal (i : ℕ) (hi : i ≤ l) : degree i v+i ≤ degree 0 v := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hCard : 2 ≤ (W i).card := hMany.trans (card_le_card (hContain i (by omega)))
      have h := hDrop i (by omega) hCard v (hContain (i+1) hi hv)
      have hp := ih (by omega)
      omega
  exact ⟨hContain 0 (Nat.zero_le _) hv,hTotal l le_rfl⟩

theorem low_set_card_le_one_at_long_limit (W : ℕ → Finset V) (degree : ℕ → V → ℕ)
    (l : ℕ) (limit : ℝ)
    (hNested : ∀ i < l,W (i+1) ⊆ W i)
    (hLow : ∀ v ∈ W 0,(degree 0 v:ℝ) < limit)
    (hDrop : ∀ i < l,2 ≤ (W i).card → ∀ v ∈ W (i+1),degree (i+1) v+1 ≤ degree i v)
    (hLast : limit ≤ (l:ℝ)) :
    (W l).card ≤ 1 := by
  by_contra! hMany
  obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0 < (W l).card)
  obtain ⟨hStart,hDebit⟩ := low_survivor_pays_for_rounds W degree l hNested hDrop (by omega) v hv
  have hD : (l:ℝ) ≤ (degree 0 v:ℝ) := by exact_mod_cast (show l ≤ degree 0 v by omega)
  exact (not_lt_of_ge (hLast.trans hD)) (hLow v hStart)

/-- At the actual floored limit, two surviving original low vertices
would already have spent all of their initial degree. -/
theorem low_set_card_le_one_at_floored_long_limit (W : ℕ → Finset V) (degree : ℕ → V → ℕ)
    (limit : ℝ) :
    let l := ⌊limit⌋₊
    (∀ i < l,W (i+1) ⊆ W i) →
    (∀ v ∈ W 0,(degree 0 v:ℝ) < limit) →
    (∀ i < l,2 ≤ (W i).card → ∀ v ∈ W (i+1),degree (i+1) v+1 ≤ degree i v) →
    (∀ v ∈ W l,0 < degree l v) →
    (W l).card ≤ 1 := by
  intro l hNested hLow hDrop hLive
  by_contra! hMany
  obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0 < (W l).card)
  obtain ⟨hStart,hDebit⟩ := low_survivor_pays_for_rounds W degree l hNested hDrop (by omega) v hv
  have hFirst : degree 0 v ≤ l := Nat.le_floor ((hLow v hStart).le)
  have hPositive := hLive v hv
  omega

theorem trimming_degree_at_rounded_limit (D d l : ℕ) (shift : ℝ)
    (hD : d+2*l = D)
    (hLast : (D:ℝ)/3-shift ≤ (l:ℝ))
    (hPrev : (l:ℝ) ≤ (D:ℝ)/3-shift+1) :
    (D:ℝ)/3+2*shift-2 ≤ (d:ℝ) ∧ (d:ℝ) ≤ (D:ℝ)/3+2*shift := by
  have h : (d:ℝ)+2*(l:ℝ) = (D:ℝ) := by exact_mod_cast hD
  constructor <;> linarith only [h,hLast,hPrev]

theorem ordinary_degree_profile_at_trimming_limit
    (D d l n a : ℕ) (η : ℝ) (hη : 0 ≤ η) (hD : d+2*l = D)
    (hRoom : 2*η^2*(n:ℝ)+4 ≤ η*(n:ℝ))
    (hLast : (D:ℝ)/3-2*η*(n:ℝ) ≤ (l:ℝ))
    (hDegree : (D:ℝ)/3-η*(n:ℝ)-2*η^2*(n:ℝ)-4 ≤ (a:ℝ)) :
    (d:ℝ)-6*η*(n:ℝ) ≤ (a:ℝ) := by
  have h : (d:ℝ)+2*(l:ℝ) = (D:ℝ) := by exact_mod_cast hD
  linarith only [h,hRoom,hLast,hDegree]

end OverfullWork.CMSTrimmingRound
