module

public import OverfullWork.RobustClusterQuotient

@[expose] public section


/-! Exact real parameters for the counting step of KOT Lemma 14.
The graph, pure subgraph and equal-cluster map are actual inputs.
Explicit scalar budgets pay ceilings, exception and neighbour loss.
This does not construct a directed regularity partition. -/
namespace OverfullWork.RobustClusterQuotient
open Finset DirectedRobustExpansion DirectedClusterQuotient
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

theorem real_robust_of_deleted_indegree (D H : Digraph V) (hLe : H ≤ D)
    (f : V → Option I) (m L : ℕ) (hm : 0 < m)
    (hSize : ∀ i,(cluster f i).card=m) (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hRobust : IsRealRobust D ν τ) (hLoss : ∀ v,inDegree (D\H) v ≤ L)
    (hSmall : ((exceptional f).card:ℝ)+(L:ℝ)+(m:ℝ) ≤ ν*(Fintype.card V:ℝ)/2)
    (hInterval : τ*(Fintype.card V:ℝ)+1 ≤ 2*τ*(m:ℝ)*(Fintype.card I:ℝ)) :
    IsRealRobust (quotient H f) (ν/2) (2*τ) := by
  let r := ⌈ν*(Fintype.card V:ℝ)⌉₊
  let t := ⌈τ*(Fintype.card V:ℝ)⌉₊
  let s := ⌈(ν/2)*(Fintype.card I:ℝ)⌉₊
  let T := ⌈(2*τ)*(Fintype.card I:ℝ)⌉₊
  have hOrder : (Fintype.card V:ℝ)=((exceptional f).card:ℝ)+(m:ℝ)*(Fintype.card I:ℝ) := by
    exact_mod_cast order_eq f m hSize
  have hOrderScaled := congrArg (fun x : ℝ => ν*x) hOrder
  have hT : t ≤ m*T := by
    have hSource : (t:ℝ) < τ*(Fintype.card V:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
    have hTarget := mul_le_mul_of_nonneg_left (Nat.le_ceil ((2*τ)*(Fintype.card I:ℝ)))
      (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    have hh : (t:ℝ) ≤ (m:ℝ)*(T:ℝ) := by nlinarith only [hSource,hTarget,hInterval]
    exact_mod_cast hh
  have hBudget : (exceptional f).card+L+m*s ≤ r := by
    have hSource : ν*(Fintype.card V:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
    have hTarget : (s:ℝ) < (ν/2)*(Fintype.card I:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
    have hScale := mul_le_mul_of_nonneg_left hTarget.le (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    have hPay := mul_nonneg hν.le (Nat.cast_nonneg (exceptional f).card : (0:ℝ) ≤ (exceptional f).card)
    have hh : ((exceptional f).card:ℝ)+(L:ℝ)+(m:ℝ)*(s:ℝ) ≤ (r:ℝ) := by
      nlinarith only [hScale,hSmall,hSource,hOrderScaled,hPay]
    exact_mod_cast hh
  have hInteger := robust_of_deleted_indegree D H hLe f m hm hSize r t s T L
    (integer_of_real D ν τ hν.le hRobust) hLoss hT hBudget
  exact real_of_integer_at_ceil_interval (quotient H f) s (ν/2) (2*τ) (by positivity)
    hInteger (Nat.le_ceil _)

theorem inDegree_le_exceptional_add_quotient (H : Digraph V) (f : V → Option I)
    (m : ℕ) (hSize : ∀ i,(cluster f i).card=m) (v : V) (j : I) (hv : f v=some j) :
    inDegree H v ≤ (exceptional f).card+m*inDegree (quotient H f) j := by
  apply card_le_exceptional_add_lift f m hSize
    (univ.filter fun u => H.Adj u v) (univ.filter fun i => (quotient H f).Adj i j)
  intro u hu i hui
  exact mem_filter.mpr ⟨mem_univ _,u,v,hui,hv,(mem_filter.mp hu).2⟩

theorem outDegree_le_exceptional_add_quotient (H : Digraph V) (f : V → Option I)
    (m : ℕ) (hSize : ∀ i,(cluster f i).card=m) (v : V) (j : I) (hv : f v=some j) :
    outDegree H v ≤ (exceptional f).card+m*outDegree (quotient H f) j := by
  apply card_le_exceptional_add_lift f m hSize
    (univ.filter fun u => H.Adj v u) (univ.filter fun i => (quotient H f).Adj j i)
  intro u hu i hui
  exact mem_filter.mpr ⟨mem_univ _,v,u,hv,hui,(mem_filter.mp hu).2⟩

theorem real_semidegree_lower_bound (H : Digraph V) (f : V → Option I) (m L : ℕ)
    (hm : 0 < m) (hSize : ∀ i,(cluster f i).card=m) (α : ℝ) (hα : 0 < α)
    (hIn : ∀ v,α*(Fintype.card V:ℝ)-(L:ℝ) ≤ (inDegree H v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ)-(L:ℝ) ≤ (outDegree H v:ℝ))
    (hSmall : ((exceptional f).card:ℝ)+(L:ℝ) ≤ α*(Fintype.card V:ℝ)/2) :
    (∀ j,(α/2)*(Fintype.card I:ℝ) ≤ (inDegree (quotient H f) j:ℝ)) ∧
    (∀ j,(α/2)*(Fintype.card I:ℝ) ≤ (outDegree (quotient H f) j:ℝ)) := by
  have hOrder : (Fintype.card V:ℝ)=((exceptional f).card:ℝ)+(m:ℝ)*(Fintype.card I:ℝ) := by
    exact_mod_cast order_eq f m hSize
  have hOrderScaled := congrArg (fun x : ℝ => α*x) hOrder
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hPay := mul_nonneg hα.le (Nat.cast_nonneg (exceptional f).card : (0:ℝ) ≤ (exceptional f).card)
  have hScalar : ∀ d q : ℝ,α*(Fintype.card V:ℝ)-(L:ℝ) ≤ d →
      d ≤ ((exceptional f).card:ℝ)+(m:ℝ)*q → (α/2)*(Fintype.card I:ℝ) ≤ q := by
    intro d q hd hq
    have hh : (m:ℝ)*((α/2)*(Fintype.card I:ℝ)) ≤ (m:ℝ)*q := by
      nlinarith only [hd,hq,hSmall,hOrderScaled,hPay]
    exact (mul_le_mul_iff_right₀ hmR).mp hh
  have hVertex : ∀ j : I,∃ v : V,f v=some j := by
    intro j
    have hPos : 0 < (cluster f j).card := by rw [hSize];exact hm
    obtain ⟨v,hv⟩ := card_pos.mp hPos
    exact ⟨v,(mem_cluster f j v).mp hv⟩
  constructor
  · intro j
    obtain ⟨v,hv⟩ := hVertex j
    have hh : (inDegree H v:ℝ) ≤ ((exceptional f).card:ℝ)+(m:ℝ)*(inDegree (quotient H f) j:ℝ) := by
      exact_mod_cast inDegree_le_exceptional_add_quotient H f m hSize v j hv
    exact hScalar _ _ (hIn v) hh
  · intro j
    obtain ⟨v,hv⟩ := hVertex j
    have hh : (outDegree H v:ℝ) ≤ ((exceptional f).card:ℝ)+(m:ℝ)*(outDegree (quotient H f) j:ℝ) := by
      exact_mod_cast outDegree_le_exceptional_add_quotient H f m hSize v j hv
    exact hScalar _ _ (hOut v) hh

/-- Explicit sufficient scalar inequalities for the hierarchy in KOT 14. -/
theorem paper_scale_budgets (f : V → Option I) (m L : ℕ)
    (hSize : ∀ i,(cluster f i).card=m) (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hClusters : 4 ≤ ν*(Fintype.card I:ℝ))
    (hOrderLarge : 2 ≤ τ*(Fintype.card V:ℝ))
    (hException : ((exceptional f).card:ℝ) ≤ (Fintype.card V:ℝ)/4)
    (hLossSmall : ((exceptional f).card:ℝ)+(L:ℝ) ≤ ν*(Fintype.card V:ℝ)/4) :
    ((exceptional f).card:ℝ)+(L:ℝ)+(m:ℝ) ≤ ν*(Fintype.card V:ℝ)/2 ∧
      τ*(Fintype.card V:ℝ)+1 ≤ 2*τ*(m:ℝ)*(Fintype.card I:ℝ) := by
  have hOrder : (Fintype.card V:ℝ)=((exceptional f).card:ℝ)+(m:ℝ)*(Fintype.card I:ℝ) := by
    exact_mod_cast order_eq f m hSize
  have hM := mul_le_mul_of_nonneg_left hClusters (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hνOrder := congrArg (fun x : ℝ => ν*x) hOrder
  have hτOrder := congrArg (fun x : ℝ => τ*x) hOrder
  have hνException := mul_nonneg hν.le (Nat.cast_nonneg (exceptional f).card : (0:ℝ) ≤ (exceptional f).card)
  have hτException := mul_le_mul_of_nonneg_left hException hτ.le
  constructor
  · nlinarith only [hM,hνOrder,hνException,hLossSmall]
  · nlinarith only [hτOrder,hτException,hOrderLarge]

theorem outdegree_loss_of_deleted_outdegree (D H : Digraph V) (hLe : H ≤ D)
    (L : ℕ) (hLoss : ∀ v,outDegree (D\H) v ≤ L) (v : V) :
    outDegree D v ≤ outDegree H v+L := by
  have hPart := DirectedArcSelection.incidence_partition D H hLe {v} univ
  rw [DirectedArcSelection.incidences_outDegree,DirectedArcSelection.incidences_outDegree,
    DirectedArcSelection.incidences_outDegree] at hPart
  have hh := hLoss v
  omega

/-- The normalized inheritance conclusions of KOT 14 from an actual
pure subgraph and actual equal clusters, with all scalar budgets paid.
Existence of those regularity outputs is not a premise about R's
robustness: R is constructed here and its robustness is a conclusion. -/
theorem real_quotient_transfer (D H : Digraph V) (hLe : H ≤ D)
    (f : V → Option I) (m L : ℕ) (hm : 0 < m)
    (hSize : ∀ i,(cluster f i).card=m) (ν τ α : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (hLossIn : ∀ v,inDegree (D\H) v ≤ L) (hLossOut : ∀ v,outDegree (D\H) v ≤ L)
    (hClusters : 4 ≤ ν*(Fintype.card I:ℝ))
    (hOrderLarge : 2 ≤ τ*(Fintype.card V:ℝ))
    (hException : ((exceptional f).card:ℝ) ≤ (Fintype.card V:ℝ)/4)
    (hLossSmall : ((exceptional f).card:ℝ)+(L:ℝ) ≤ ν*(Fintype.card V:ℝ)/4)
    (hDegreeSmall : ((exceptional f).card:ℝ)+(L:ℝ) ≤ α*(Fintype.card V:ℝ)/2) :
    IsRealRobust (quotient H f) (ν/2) (2*τ) ∧
      (∀ j,(α/2)*(Fintype.card I:ℝ) ≤ (inDegree (quotient H f) j:ℝ)) ∧
      (∀ j,(α/2)*(Fintype.card I:ℝ) ≤ (outDegree (quotient H f) j:ℝ)) := by
  obtain ⟨hSmall,hInterval⟩ := paper_scale_budgets f m L hSize ν τ hν hτ
    hClusters hOrderLarge hException hLossSmall
  have hPureIn : ∀ v,α*(Fintype.card V:ℝ)-(L:ℝ) ≤ (inDegree H v:ℝ) := by
    intro v
    have hh : (inDegree D v:ℝ) ≤ (inDegree H v:ℝ)+(L:ℝ) := by
      exact_mod_cast neighbour_loss_of_deleted_indegree D H hLe L hLossIn univ v
    linarith only [hh,hIn v]
  have hPureOut : ∀ v,α*(Fintype.card V:ℝ)-(L:ℝ) ≤ (outDegree H v:ℝ) := by
    intro v
    have hh : (outDegree D v:ℝ) ≤ (outDegree H v:ℝ)+(L:ℝ) := by
      exact_mod_cast outdegree_loss_of_deleted_outdegree D H hLe L hLossOut v
    linarith only [hh,hOut v]
  exact ⟨real_robust_of_deleted_indegree D H hLe f m L hm hSize ν τ hν hτ hRobust hLossIn hSmall hInterval,
    real_semidegree_lower_bound H f m L hm hSize α hα hPureIn hPureOut hDegreeSmall⟩

end OverfullWork.RobustClusterQuotient
