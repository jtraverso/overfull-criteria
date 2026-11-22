module

public import OverfullWork.KuhnOsthusChordReserveConstruction

@[expose] public section


/-! Integral budgets for the two reserves in Lemma 9.3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

/-- The sampled centre is just above the requested degree density.
The floor of the degree and the two ceilings are paid for by the
regularity tolerance. -/
theorem chord_base_cycle_integer_budgets (d₁ ε η δ : ℝ) (m : ℕ)
    (h₁ : 0 ≤ d₁) (hε : 0 < ε) (hm : 1 ≤ ε*(m:ℝ)) (hMargin : 8*ε ≤ δ*η) :
    let d := d₁+5*ε
    let r := ⌊d₁*(m:ℝ)⌋₊
    let h := ⌈ε*(m:ℝ)⌉₊
    let loss := ⌈7*ε*(m:ℝ)⌉₊
    0 < d ∧ (m:ℝ)*ε ≤ (h:ℝ) ∧ ((r+2*h:ℕ):ℝ) ≤ (d-ε)*(m:ℝ) ∧
      (r:ℝ) ≤ (d-2*ε)*(m:ℝ) ∧ (d+ε)*(m:ℝ) ≤ (r:ℝ)+(loss:ℝ) ∧
      (loss:ℝ) ≤ δ*((m:ℝ)*η) := by
  intro d r h loss
  have hrLo : d₁*(m:ℝ) < (r:ℝ)+1 := Nat.lt_floor_add_one _
  have hrHi : (r:ℝ) ≤ d₁*(m:ℝ) := Nat.floor_le (by positivity)
  have hhLo : ε*(m:ℝ) ≤ (h:ℝ) := Nat.le_ceil _
  have hhHi : (h:ℝ) ≤ ε*(m:ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hLossLo : 7*ε*(m:ℝ) ≤ (loss:ℝ) := Nat.le_ceil _
  have hLossHi : (loss:ℝ) ≤ 7*ε*(m:ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hMargin' := mul_le_mul_of_nonneg_right hMargin (Nat.cast_nonneg m)
  have hεm : 0 ≤ ε*(m:ℝ) := by positivity
  refine ⟨by dsimp only [d]; linarith only [h₁,hε], by linarith only [hhLo], ?_, ?_, ?_, ?_⟩
  · push_cast
    dsimp only [d]
    nlinarith only [hrHi,hhHi,hm]
  · dsimp only [d]
    nlinarith only [hrHi,hεm]
  · dsimp only [d]
    nlinarith only [hrLo,hLossLo,hm]
  · nlinarith only [hLossHi,hMargin',hm]

/-- The walk matching threshold is an integer ceiling. The lower
demand and upper degree constraints follow from the margins on the
number of matchings per quarter. -/
theorem chord_walk_quarter_integer_budgets (d η : ℝ) (m r : ℕ)
    (hd : 2*η ≤ d) (hm : 1 ≤ (m:ℝ)*η)
    (hDemand : (r:ℝ) < (d-2*η)*((m:ℝ)*η))
    (hRoom : (r:ℝ) ≤ (d-3*η)*(m:ℝ)) :
    let h := ⌈(m:ℝ)*η⌉₊
    0 < h ∧ (m:ℝ)*η ≤ (h:ℝ) ∧ (r:ℝ) < (d-2*η)*(h:ℝ) ∧
      ((h+r:ℕ):ℝ) ≤ (d-η)*(m:ℝ) := by
  intro h
  have hLo : (m:ℝ)*η ≤ (h:ℝ) := Nat.le_ceil _
  have hHi : (h:ℝ) ≤ (m:ℝ)*η+1 := (Nat.ceil_lt_add_one (by linarith only [hm])).le
  have hPos : 0 < h := Nat.ceil_pos.mpr (by linarith only [hm])
  refine ⟨hPos,hLo,hDemand.trans_le (mul_le_mul_of_nonneg_left hLo (sub_nonneg.mpr hd)),?_⟩
  push_cast
  nlinarith only [hHi,hm,hRoom]

/-- A small shift in the density centre costs the same amount in the
uniformity and degree tolerance. -/
theorem IsSuperregularPair.shift_density {V : Type*} [Fintype V]
    {G : Digraph V} {A B : Finset V} {ε d d' δ : ℝ}
    (h : IsSuperregularPair G ε d A B) (hδ : |d-d'| ≤ δ) :
    IsSuperregularPair G (ε+δ) d' A B := by
  have hNonneg : 0 ≤ δ := (abs_nonneg _).trans hδ
  have hTol : ε ≤ ε+δ := le_add_of_nonneg_right hNonneg
  refine ⟨?_,(abs_sub_le _ _ _).trans (add_le_add h.2.1 hδ),?_,?_⟩
  · intro A' hA B' hB ha hb
    exact (h.1 A' hA B' hB
      ((mul_le_mul_of_nonneg_left hTol (Nat.cast_nonneg _)).trans ha)
      ((mul_le_mul_of_nonneg_left hTol (Nat.cast_nonneg _)).trans hb)).trans_le hTol
  · intro x hx
    have hShift : |d*(B.card:ℝ)-d'*(B.card:ℝ)| ≤ δ*(B.card:ℝ) := by
      rw [←sub_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg B.card : (0:ℝ) ≤ B.card)]
      exact mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)
    rw [add_mul]
    exact (abs_sub_le _ _ _).trans (add_le_add (h.2.2.1 x hx) hShift)
  · intro y hy
    have hShift : |d*(A.card:ℝ)-d'*(A.card:ℝ)| ≤ δ*(A.card:ℝ) := by
      rw [←sub_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg A.card : (0:ℝ) ≤ A.card)]
      exact mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)
    rw [add_mul]
    exact (abs_sub_le _ _ _).trans (add_le_add (h.2.2.2 y hy) hShift)

/-- The exact integer degree can be used with a centre fixed before
the cluster size is known. -/
theorem chord_base_cycle_floor_density_error (d₁ ε : ℝ) (m : ℕ)
    (h₁ : 0 ≤ d₁) (hm : 0 < m) (hCut : 1 ≤ ε*(m:ℝ)) :
    |(⌊d₁*(m:ℝ)⌋₊:ℝ)/(m:ℝ)-d₁| ≤ ε := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hUp : (⌊d₁*(m:ℝ)⌋₊:ℝ) ≤ d₁*(m:ℝ) := Nat.floor_le (mul_nonneg h₁ hm'.le)
  have hDown : d₁*(m:ℝ) < (⌊d₁*(m:ℝ)⌋₊:ℝ)+1 := Nat.lt_floor_add_one _
  have hLower : d₁-ε ≤ (⌊d₁*(m:ℝ)⌋₊:ℝ)/(m:ℝ) :=
    (le_div_iff₀ hm').mpr (by nlinarith only [hDown,hCut])
  have hUpper : (⌊d₁*(m:ℝ)⌋₊:ℝ)/(m:ℝ) ≤ d₁ := (div_le_iff₀ hm').mpr hUp
  have hε : 0 ≤ ε := nonneg_of_mul_nonneg_left (by linarith only [hCut]) hm'
  exact abs_le.mpr ⟨by linarith only [hLower],by linarith only [hUpper,hε]⟩

/-- The cycle sampler and Lemma 11.2 can use one fixed positive
density. The tolerance still pays for the centre shift caused by
rounding the cycle degree. -/
theorem exists_chord_cycle_sampling_tolerances (ρ d : ℝ)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hDensity : ρ < d) :
    ∃ ε η δ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ η ≤ 1 ∧ 0 ≤ δ ∧
      2*(ε+δ) ≤ η ∧ 8*ε ≤ δ*η ∧ ρ+5*ε ≤ d ∧ η+ε ≤ ρ/512 := by
  let η := ρ/2048
  let δ := η/8
  let ε := min (δ*η/16) ((d-ρ)/10)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hη₁ : η ≤ 1 := by dsimp only [η]; linarith only [hρ₁]
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hε : 0 < ε := lt_min (by positivity) (by linarith only [hDensity])
  have hSample : ε ≤ δ*η/16 := min_le_left _ _
  have hHost : ε ≤ (d-ρ)/10 := min_le_right _ _
  have hSmall : ε ≤ δ/16 := by
    have h := mul_le_of_le_one_right hδ.le hη₁
    linarith only [h,hSample]
  have hSlack : ε ≤ η/128 := by dsimp only [δ] at hSmall; linarith only [hSmall]
  refine ⟨ε,η,δ,hε,by linarith only [hSlack,hη₁],hη,hη₁,hδ.le,?_,?_,?_,?_⟩
  · dsimp only [δ]
    linarith only [hSlack,hη]
  · linarith only [hSample,mul_nonneg hδ.le hη.le]
  · linarith only [hHost,hDensity]
  · dsimp only [η] at hSlack ⊢
    linarith only [hSlack,hρ]

/-- The same rounded preprocessing and cycle degrees satisfy the
budget in (11.9) when their density parameters satisfy it. -/
theorem chord_absorption_budget_of_floors (d₀ d₁ : ℝ) (m k : ℕ)
    (hd₀ : 0 ≤ d₀) (hBudget : d₀*(k:ℝ)^2 ≤ d₁) :
    ⌊d₀*(m:ℝ)⌋₊*k^2 ≤ ⌊d₁*(m:ℝ)⌋₊ := by
  apply Nat.le_floor
  have hFloor : (⌊d₀*(m:ℝ)⌋₊:ℝ) ≤ d₀*(m:ℝ) := Nat.floor_le (by positivity)
  push_cast
  calc
    _ ≤ d₀*(m:ℝ)*(k:ℝ)^2 := mul_le_mul_of_nonneg_right hFloor (sq_nonneg _)
    _ = (d₀*(k:ℝ)^2)*(m:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hBudget (Nat.cast_nonneg _)

end OverfullWork.DirectedRobustExpansion
