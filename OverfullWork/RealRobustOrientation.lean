module

public import OverfullWork.RealDirectedRobustExpansion
public import OverfullWork.BalancedRobustOrientation
public import OverfullWork.RealRobustExpansion

@[expose] public section


/-! Exact normalized robust orientation, Gao--Shan Lemma 2.11.
Upward rounding is paid in the cut-transport estimate. The final result
uses the published real parameters nu/4 and tau, not a floor surrogate. -/
namespace OverfullWork.RobustExpansion
open SimpleGraph Finset PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem integer_of_real_ceil (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν τ : ℝ) (hν : 0 ≤ ν) (hRobust : IsRealRobust G ν τ) :
    IsRobustAt G ⌈ν*(Fintype.card V:ℝ)⌉₊ ⌈τ*(Fintype.card V:ℝ)⌉₊ := by
  intro S hlo hhi
  have hLo : τ*(Fintype.card V:ℝ) ≤ (S.card:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hlo)
  have hHi : (S.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ) := by
    have hh : (S.card:ℝ)+(⌈τ*(Fintype.card V:ℝ)⌉₊:ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast hhi
    have hτ := Nat.le_ceil (τ*(Fintype.card V:ℝ))
    nlinarith only [hh,hτ]
  have hEq : realNeighbourhood G ν S=neighbourhood G ⌈ν*(Fintype.card V:ℝ)⌉₊ S := by
    ext v
    simp only [realNeighbourhood,neighbourhood,mem_filter,mem_univ,true_and,Nat.ceil_le]
  have hGrow := hRobust S hLo hHi
  rw [hEq] at hGrow
  have hCeil := Nat.ceil_le.mpr hGrow
  rw [add_comm,Nat.ceil_add_natCast (mul_nonneg hν (Nat.cast_nonneg _))] at hCeil
  omega

end OverfullWork.RobustExpansion

namespace OverfullWork.BalancedRobustOrientation
open SimpleGraph Finset
open scoped Classical
universe u
set_option maxHeartbeats 18000000

theorem robust_ceil_quarter_of_cut_error {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Digraph V) (r t : ℕ) (E : ℝ)
    (hRobust : RobustExpansion.IsRobustAt G r t) (hr : 16 ≤ r)
    (hError : 8*E ≤ (r:ℝ)^2)
    (hCuts : ∀ S T : Finset V,(EdgeSigningWeights.incidences G S T:ℝ) ≤
      2*(DirectedRobustExpansion.incidences D S T:ℝ)+E) :
    DirectedRobustExpansion.IsRobustAt D ⌈(r:ℝ)/4⌉₊ t := by
  let s := ⌈(r:ℝ)/4⌉₊
  have hrR : (16:ℝ) ≤ r := by exact_mod_cast hr
  have hs : (s:ℝ) < (r:ℝ)/4+1 := Nat.ceil_lt_add_one (by positivity)
  have hA : 3*(r:ℝ)/8 ≤ (r:ℝ)-2*(s:ℝ) := by linarith only [hs,hrR]
  have hB : (r:ℝ)/2 ≤ (r:ℝ)-(s:ℝ) := by linarith only [hs,hrR]
  have hMult := mul_le_mul hA hB (by positivity : (0:ℝ) ≤ (r:ℝ)/2)
    (by linarith only [hA,hrR] : (0:ℝ) ≤ (r:ℝ)-2*(s:ℝ))
  have hGapR : 2*(s:ℝ) ≤ (r:ℝ) := by linarith only [hs,hrR]
  have hGap : 2*s ≤ r := by exact_mod_cast hGapR
  apply DirectedRobustCutTransport.robust_of_cut_lower_bound G D r s t E hRobust hGap ?_ hCuts
  nlinarith only [hError,hMult,hrR]

theorem exists_uniform_ceil_orientation (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (r t : ℕ),
      N ≤ Fintype.card V → RobustExpansion.IsRobustAt G r t →
      ρ*(Fintype.card V:ℝ) ≤ (r:ℝ) →
      ∃ D : Digraph V,DirectedRobustExpansion.IsOrientationOf D G ∧
        (∀ v,|2*(DirectedRobustExpansion.inDegree D v:ℝ)-(G.degree v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        (∀ v,|2*(DirectedRobustExpansion.outDegree D v:ℝ)-(G.degree v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        DirectedRobustExpansion.IsRobustAt D ⌈(r:ℝ)/4⌉₊ t := by
  let δ := min ε (ρ^2/16)
  have hδ : 0 < δ := by dsimp only [δ];positivity
  obtain ⟨N₀,hOrient⟩ := exists_balanced_orientation.{u} δ hδ
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (32/ρ)
  refine ⟨max N₀ N₁,?_⟩
  intro V _ _ G _ r t hn hRobust hR
  let n := Fintype.card V
  obtain ⟨D,hD,hIn,hOut,hCuts⟩ := hOrient G (by omega)
  have hδle : δ ≤ ε := min_le_left _ _
  have hδρ : 16*δ ≤ ρ^2 := by
    have hh := min_le_right ε (ρ^2/16)
    change δ ≤ ρ^2/16 at hh
    linarith only [hh]
  have hN₁n : (N₁:ℝ) ≤ n := by exact_mod_cast (show N₁ ≤ n by omega)
  have hLarge : (32:ℝ) < ρ*(n:ℝ) := by
    have hh := (div_lt_iff₀ hρ).mp (hN₁.trans_le hN₁n)
    nlinarith only [hh]
  have hr : 16 ≤ r := by exact_mod_cast (show (16:ℝ) ≤ r by linarith only [hLarge,hR])
  have hError : 8*(δ*(n:ℝ)^2) ≤ (r:ℝ)^2 := by
    have hδn := mul_le_mul_of_nonneg_right hδρ (sq_nonneg (n:ℝ))
    have hR2 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ρ*(n:ℝ)) hR 2
    have hNonneg : (0:ℝ) ≤ δ*(n:ℝ)^2 := by positivity
    nlinarith only [hδn,hR2,hNonneg]
  have hLower : ∀ S T : Finset V,(EdgeSigningWeights.incidences G S T:ℝ) ≤
      2*(DirectedRobustExpansion.incidences D S T:ℝ)+δ*(n:ℝ)^2 := by
    intro S T
    have hh := (abs_lt.mp (hCuts S T)).1
    linarith only [hh]
  have hRD := robust_ceil_quarter_of_cut_error G D r t (δ*(n:ℝ)^2) hRobust hr hError hLower
  have hTol := mul_le_mul_of_nonneg_right hδle (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  exact ⟨D,hD,(fun v => (hIn v).trans_le hTol),(fun v => (hOut v).trans_le hTol),hRD⟩

/-- Gao--Shan Lemma 2.11 with the exact published real parameters. -/
theorem exists_real_relative_orientation (ν τ α η : ℝ)
    (hν : 0 < ν) (hτ : 0 ≤ τ) (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],N ≤ Fintype.card V →
      RobustExpansion.IsRealRobust G ν τ →
      (∀ v,α*(Fintype.card V:ℝ) ≤ (G.degree v:ℝ)) →
      ∃ D : Digraph V,DirectedRobustExpansion.IsOrientationOf D G ∧
        (∀ v,|2*(DirectedRobustExpansion.inDegree D v:ℝ)-(G.degree v:ℝ)| < η*(G.degree v:ℝ)) ∧
        (∀ v,|2*(DirectedRobustExpansion.outDegree D v:ℝ)-(G.degree v:ℝ)| < η*(G.degree v:ℝ)) ∧
        DirectedRobustExpansion.IsRealRobust D (ν/4) τ := by
  obtain ⟨N,hN⟩ := exists_uniform_ceil_orientation.{u} ν (η*α) hν (mul_pos hη hα)
  refine ⟨N,?_⟩
  intro V _ _ G _ hn hRobust hDegree
  let r := ⌈ν*(Fintype.card V:ℝ)⌉₊
  let t := ⌈τ*(Fintype.card V:ℝ)⌉₊
  obtain ⟨D,hD,hIn,hOut,hRD⟩ := hN G r t hn
    (RobustExpansion.integer_of_real_ceil G ν τ hν.le hRobust) (Nat.le_ceil _)
  have hTol : ∀ v,(η*α)*(Fintype.card V:ℝ) ≤ η*(G.degree v:ℝ) := by
    intro v
    have hh := mul_le_mul_of_nonneg_left (hDegree v) hη.le
    linarith only [hh]
  refine ⟨D,hD,(fun v => (hIn v).trans_le (hTol v)),
    (fun v => (hOut v).trans_le (hTol v)),?_⟩
  apply DirectedRobustExpansion.real_of_integer_at_ceil_interval D _ (ν/4) τ hτ hRD
  have h₁ := Nat.le_ceil (ν*(Fintype.card V:ℝ))
  have h₂ := Nat.le_ceil ((r:ℝ)/4)
  change ν*(Fintype.card V:ℝ) ≤ (r:ℝ) at h₁
  nlinarith only [h₁,h₂]

end OverfullWork.BalancedRobustOrientation
