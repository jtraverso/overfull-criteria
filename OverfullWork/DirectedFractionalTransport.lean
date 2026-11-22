module

public import OverfullWork.DirectedArcSelection
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section


/-! Transport directed robust expansion to a selected fraction using
uniform cut discrepancy. The set-size interval is preserved. -/
namespace OverfullWork.DirectedFractionalTransport
open Finset DirectedRobustExpansion DirectedArcSelection
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 14000000

theorem robust_of_cut_lower_bound (G H : Digraph V) (p : ℝ) (r s t : ℕ) (E : ℝ) (hp : 0 ≤ p)
    (hRobust : IsRobustAt G r t) (hGap : (s:ℝ) ≤ p*(r:ℝ))
    (hError : E < (p*(r:ℝ)-(s:ℝ))*((r:ℝ)-(s:ℝ)))
    (hCuts : ∀ S T : Finset V,p*(incidences G S T:ℝ) ≤ (incidences H S T:ℝ)+E) :
    IsRobustAt H s t := by
  intro S hLo hHi
  by_contra hBad
  let R := neighbourhood G r S
  let N := neighbourhood H s S
  let B := R\N
  have hGrow := hRobust S hLo hHi
  have hSplit := card_sdiff_add_card_inter R N
  have hInter := card_le_card (s:=R ∩ N) (t:=N) inter_subset_right
  have hB : r ≤ B.card+s := by
    change S.card+r ≤ R.card at hGrow
    change ¬S.card+s ≤ N.card at hBad
    change B.card+(R ∩ N).card=R.card at hSplit
    omega
  have hSource : r*B.card ≤ incidences G S B := by
    calc
      _ = ∑ _v ∈ B,r := by simp [Nat.mul_comm]
      _ ≤ _ := by
        unfold incidences
        apply sum_le_sum
        intro v hv
        exact (mem_filter.mp (mem_sdiff.mp hv).1).2
  have hTarget : incidences H S B ≤ s*B.card := by
    calc
      _ ≤ ∑ _v ∈ B,s := by
        unfold incidences
        apply sum_le_sum
        intro v hv
        have hn : ¬s ≤ inNeighbours H S v := by
          intro hh
          exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨mem_univ _,hh⟩)
        omega
      _ = _ := by simp [Nat.mul_comm]
  have hSourceR : (r:ℝ)*(B.card:ℝ) ≤ (incidences G S B:ℝ) := by exact_mod_cast hSource
  have hTargetR : (incidences H S B:ℝ) ≤ (s:ℝ)*(B.card:ℝ) := by exact_mod_cast hTarget
  have hBR : (r:ℝ)-(s:ℝ) ≤ (B.card:ℝ) := by
    have hh : (r:ℝ) ≤ (B.card:ℝ)+(s:ℝ) := by exact_mod_cast hB
    linarith only [hh]
  have hGapR : (0:ℝ) ≤ p*(r:ℝ)-(s:ℝ) := sub_nonneg.mpr hGap
  have hProduct := mul_le_mul_of_nonneg_left hBR hGapR
  have hCut := hCuts S B
  have hScaled := mul_le_mul_of_nonneg_left hSourceR hp
  nlinarith only [hScaled,hTargetR,hProduct,hCut,hError]

theorem robust_fraction_of_cut_error (G H : Digraph V) (p : ℝ) (r t : ℕ) (E : ℝ)
    (hRobust : IsRobustAt G r t) (hp : 0 < p) (hp1 : p ≤ 1)
    (hTwo : 2 ≤ p*(r:ℝ)) (hError : 8*E ≤ p*(r:ℝ)^2)
    (hCuts : ∀ S T : Finset V,p*(incidences G S T:ℝ) ≤ (incidences H S T:ℝ)+E) :
    0 < ⌊p*(r:ℝ)/2⌋₊ ∧ IsRobustAt H ⌊p*(r:ℝ)/2⌋₊ t := by
  let s := ⌊p*(r:ℝ)/2⌋₊
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hs : (s:ℝ) ≤ p*(r:ℝ)/2 := Nat.floor_le (by positivity)
  have hpr : p*(r:ℝ) ≤ (r:ℝ) := by nlinarith only [hp1,hr0]
  have hA : p*(r:ℝ)/2 ≤ p*(r:ℝ)-(s:ℝ) := by linarith only [hs]
  have hB : (r:ℝ)/2 ≤ (r:ℝ)-(s:ℝ) := by linarith only [hs,hpr]
  have hMult := mul_le_mul hA hB (by positivity : (0:ℝ) ≤ (r:ℝ)/2)
    (by linarith only [hA,hTwo] : (0:ℝ) ≤ p*(r:ℝ)-(s:ℝ))
  have hPos : (0:ℝ) < p*(r:ℝ)^2 := by
    have hr : (0:ℝ) < r := by nlinarith only [hTwo,hpr]
    positivity
  refine ⟨Nat.floor_pos.mpr (by linarith only [hTwo]),
    robust_of_cut_lower_bound G H p r s t E hp.le hRobust (by linarith only [hs,hTwo]) ?_ hCuts⟩
  nlinarith only [hMult,hError,hPos]

/-- The upward rounding pays a fixed unit and retains the paper's fraction. -/
theorem robust_ceil_fraction_of_cut_error (G H : Digraph V) (p : ℝ) (r t : ℕ) (E : ℝ)
    (hRobust : IsRobustAt G r t) (hp : 0 < p) (hp1 : p ≤ 1)
    (hEight : 8 ≤ p*(r:ℝ)) (hError : 8*E ≤ p*(r:ℝ)^2)
    (hCuts : ∀ S T : Finset V,p*(incidences G S T:ℝ) ≤ (incidences H S T:ℝ)+E) :
    0 < ⌈p*(r:ℝ)/2⌉₊ ∧ IsRobustAt H ⌈p*(r:ℝ)/2⌉₊ t := by
  let s := ⌈p*(r:ℝ)/2⌉₊
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hs : (s:ℝ) < p*(r:ℝ)/2+1 := Nat.ceil_lt_add_one (by positivity)
  have hpr : p*(r:ℝ) ≤ (r:ℝ) := by nlinarith only [hp1,hr0]
  have hA : 3*p*(r:ℝ)/8 ≤ p*(r:ℝ)-(s:ℝ) := by linarith only [hs,hEight]
  have hB : 3*(r:ℝ)/8 ≤ (r:ℝ)-(s:ℝ) := by linarith only [hs,hpr,hEight]
  have hMult := mul_le_mul hA hB (by positivity : (0:ℝ) ≤ 3*(r:ℝ)/8)
    (by linarith only [hA,hEight] : (0:ℝ) ≤ p*(r:ℝ)-(s:ℝ))
  have hPos : (0:ℝ) < p*(r:ℝ)^2 := by
    have hr : (0:ℝ) < r := by linarith only [hEight,hpr]
    positivity
  refine ⟨Nat.one_le_ceil_iff.mpr (by linarith only [hEight]),
    robust_of_cut_lower_bound G H p r s t E hp.le hRobust (by linarith only [hs,hEight]) ?_ hCuts⟩
  nlinarith only [hMult,hError,hPos]

end OverfullWork.DirectedFractionalTransport
