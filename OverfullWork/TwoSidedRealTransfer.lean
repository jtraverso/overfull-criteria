module

public import OverfullWork.TwoSidedClusterQuotient
public import OverfullWork.NormalizedRobustQuotient

@[expose] public section


/-! Real normalized robust transfer for distinct source/target partitions.
Only ordinary target vertices need a deleted indegree bound. -/
namespace OverfullWork.TwoSidedClusterQuotient
open Finset DirectedRobustExpansion DirectedClusterQuotient
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

theorem conditional_neighbour_loss (D H : Digraph V) (hLe : H ≤ D)
    (g : V → Option I) (L : ℕ)
    (hLoss : ∀ v,g v ≠ none → inDegree (D\H) v ≤ L) :
    ∀ A v,g v ≠ none → inNeighbours D A v ≤ inNeighbours H A v+L := by
  intro A v hv
  have hPart := DirectedArcSelection.incidence_partition D H hLe A {v}
  simp only [incidences,sum_singleton] at hPart
  have hBound := (RobustClusterQuotient.inNeighbours_mono (D\H) (subset_univ A) v).trans (hLoss v hv)
  change inNeighbours (D\H) A v ≤ L at hBound
  omega

theorem real_robust_from_host (D H : Digraph V) (hLe : H ≤ D)
    (f g : V → Option I) (m L : ℕ) (hm : 0 < m)
    (hF : ∀ i,(cluster f i).card=m) (hG : ∀ i,(cluster g i).card=m) (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hRobust : IsRealRobust D ν τ) (hLoss : ∀ v,g v ≠ none → inDegree (D\H) v ≤ L)
    (hSmall : ((exceptional g).card:ℝ)+(L:ℝ)+(m:ℝ) ≤ ν*(Fintype.card V:ℝ)/2)
    (hInterval : τ*(Fintype.card V:ℝ)+1 ≤ 2*τ*(m:ℝ)*(Fintype.card I:ℝ)) :
    IsRealRobust (quotient H f g) (ν/2) (2*τ) := by
  let r := ⌈ν*(Fintype.card V:ℝ)⌉₊
  let t := ⌈τ*(Fintype.card V:ℝ)⌉₊
  let s := ⌈(ν/2)*(Fintype.card I:ℝ)⌉₊
  let T := ⌈(2*τ)*(Fintype.card I:ℝ)⌉₊
  have hOrder : (Fintype.card V:ℝ)=((exceptional g).card:ℝ)+(m:ℝ)*(Fintype.card I:ℝ) := by
    exact_mod_cast order_eq g m hG
  have hOrderScaled := congrArg (fun x : ℝ => ν*x) hOrder
  have hT : t ≤ m*T := by
    have hSource : (t:ℝ) < τ*(Fintype.card V:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
    have hTarget := mul_le_mul_of_nonneg_left (Nat.le_ceil ((2*τ)*(Fintype.card I:ℝ)))
      (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    have hh : (t:ℝ) ≤ (m:ℝ)*(T:ℝ) := by nlinarith only [hSource,hTarget,hInterval]
    exact_mod_cast hh
  have hBudget : (exceptional g).card+L+m*s ≤ r := by
    have hSource : ν*(Fintype.card V:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
    have hTarget : (s:ℝ) < (ν/2)*(Fintype.card I:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
    have hScale := mul_le_mul_of_nonneg_left hTarget.le (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    have hPay := mul_nonneg hν.le (Nat.cast_nonneg (exceptional g).card : (0:ℝ) ≤ (exceptional g).card)
    have hh : ((exceptional g).card:ℝ)+(L:ℝ)+(m:ℝ)*(s:ℝ) ≤ (r:ℝ) := by
      nlinarith only [hScale,hSmall,hSource,hOrderScaled,hPay]
    exact_mod_cast hh
  have hInteger := robust_from_host D H f g m hm hF hG r t s T L
    (integer_of_real D ν τ hν.le hRobust)
    (conditional_neighbour_loss D H hLe g L hLoss) hT hBudget
  exact real_of_integer_at_ceil_interval (quotient H f g) s (ν/2) (2*τ) (by positivity)
    hInteger (Nat.le_ceil _)

end OverfullWork.TwoSidedClusterQuotient
