module

public import OverfullWork.OrientedEdgeSigning
public import OverfullWork.DirectedRobustCutTransport

@[expose] public section


/-! A uniform robust orientation, following Gao--Shan Lemma 2.11
(arXiv:2405.18494v2, citing Kühn--Osthus Lemma 3.1).
An actual Mathlib digraph is constructed with every source edge oriented
once, relative semidegree error, and positive quarter robust threshold.
This is an orientation lemma, not a spanning-layout packing theorem. -/
namespace OverfullWork.BalancedRobustOrientation
open SimpleGraph Finset OrientedEdgeSigning
open scoped Classical
universe u
set_option maxHeartbeats 18000000

theorem exists_balanced_orientation (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],N ≤ Fintype.card V →
      ∃ D : Digraph V,DirectedRobustExpansion.IsOrientationOf D G ∧
        (∀ v,|2*(DirectedRobustExpansion.inDegree D v:ℝ)-(G.degree v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        (∀ v,|2*(DirectedRobustExpansion.outDegree D v:ℝ)-(G.degree v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        ∀ S T : Finset V,
          |2*(DirectedRobustExpansion.incidences D S T:ℝ)-(EdgeSigningWeights.incidences G S T:ℝ)| <
            ε*(Fintype.card V:ℝ)^2 := by
  obtain ⟨N,hSign⟩ := DegreeCutSigning.exists_degree_cut_signing.{u,u} ε hε
  refine ⟨N,?_⟩
  intro V _ _ G _ hn
  let code : V → ℕ := fun v => (Fintype.equivFin V v).val
  have hCode : Function.Injective code := Fin.val_injective.comp (Fintype.equivFin V).injective
  obtain ⟨s,hDegree,hCuts⟩ := hSign
    (fun v => cutWeight G code univ {v}) (fun ST => cutWeight G code ST.1 ST.2) hn
    (degree_variance_bound G code) (fun ST => cut_variance_bound G code ST.1 ST.2)
  let D := oriented G code s
  have hD : DirectedRobustExpansion.IsOrientationOf D G := isOrientationOf G code hCode s
  have hIn : ∀ v,|2*(DirectedRobustExpansion.inDegree D v:ℝ)-(G.degree v:ℝ)| <
      ε*(Fintype.card V:ℝ) := by
    intro v
    have hh := hDegree v
    rw [signed_cut_identity G code hCode s univ {v},
      DirectedRobustExpansion.incidences_degree,EdgeSigningWeights.incidences_degree] at hh
    exact hh
  refine ⟨D,hD,hIn,?_,?_⟩
  · intro v
    have hPay := DirectedRobustExpansion.degree_partition D G hD v
    have hPayR : (DirectedRobustExpansion.inDegree D v:ℝ)+
        (DirectedRobustExpansion.outDegree D v:ℝ)=(G.degree v:ℝ) := by exact_mod_cast hPay
    have hNeg : 2*(DirectedRobustExpansion.outDegree D v:ℝ)-(G.degree v:ℝ)=
        -(2*(DirectedRobustExpansion.inDegree D v:ℝ)-(G.degree v:ℝ)) := by linarith only [hPayR]
    rw [hNeg,abs_neg]
    exact hIn v
  · intro S T
    have hh := hCuts S T
    rw [signed_cut_identity G code hCode s S T] at hh
    exact hh

theorem exists_uniform_robust_orientation (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (r t : ℕ),
      N ≤ Fintype.card V → RobustExpansion.IsRobustAt G r t →
      ρ*(Fintype.card V:ℝ) ≤ (r:ℝ) →
      ∃ D : Digraph V,DirectedRobustExpansion.IsOrientationOf D G ∧
        (∀ v,|2*(DirectedRobustExpansion.inDegree D v:ℝ)-(G.degree v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        (∀ v,|2*(DirectedRobustExpansion.outDegree D v:ℝ)-(G.degree v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        0 < r/4 ∧ DirectedRobustExpansion.IsRobustAt D (r/4) t := by
  let δ := min ε (ρ^2/16)
  have hδ : 0 < δ := by dsimp only [δ];positivity
  obtain ⟨N₀,hOrient⟩ := exists_balanced_orientation.{u} δ hδ
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (8/ρ)
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
  have hEight : (8:ℝ) < ρ*(n:ℝ) := by
    have hh := (div_lt_iff₀ hρ).mp (hN₁.trans_le hN₁n)
    nlinarith only [hh]
  have hr : 4 ≤ r := by exact_mod_cast (show (4:ℝ) ≤ r by linarith only [hEight,hR])
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
  obtain ⟨hPos,hRobustD⟩ := DirectedRobustCutTransport.robust_quarter_of_cut_error G D r t
    (δ*(n:ℝ)^2) hRobust hr hError hLower
  have hTolerance := mul_le_mul_of_nonneg_right hδle (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  exact ⟨D,hD,(fun v => (hIn v).trans_le hTolerance),
    (fun v => (hOut v).trans_le hTolerance),hPos,hRobustD⟩

theorem exists_relative_robust_orientation (ρ α η : ℝ)
    (hρ : 0 < ρ) (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (r t : ℕ),
      N ≤ Fintype.card V → RobustExpansion.IsRobustAt G r t →
      ρ*(Fintype.card V:ℝ) ≤ (r:ℝ) →
      (∀ v,α*(Fintype.card V:ℝ) ≤ (G.degree v:ℝ)) →
      ∃ D : Digraph V,DirectedRobustExpansion.IsOrientationOf D G ∧
        (∀ v,|2*(DirectedRobustExpansion.inDegree D v:ℝ)-(G.degree v:ℝ)| < η*(G.degree v:ℝ)) ∧
        (∀ v,|2*(DirectedRobustExpansion.outDegree D v:ℝ)-(G.degree v:ℝ)| < η*(G.degree v:ℝ)) ∧
        0 < r/4 ∧ DirectedRobustExpansion.IsRobustAt D (r/4) t := by
  obtain ⟨N,hN⟩ := exists_uniform_robust_orientation.{u} ρ (η*α) hρ (mul_pos hη hα)
  refine ⟨N,?_⟩
  intro V _ _ G _ r t hn hRobust hr hDegree
  obtain ⟨D,hD,hIn,hOut,hPos,hRD⟩ := hN G r t hn hRobust hr
  have hTol : ∀ v,(η*α)*(Fintype.card V:ℝ) ≤ η*(G.degree v:ℝ) := by
    intro v
    have hh := mul_le_mul_of_nonneg_left (hDegree v) hη.le
    linarith only [hh]
  exact ⟨D,hD,(fun v => (hIn v).trans_le (hTol v)),
    (fun v => (hOut v).trans_le (hTol v)),hPos,hRD⟩

/-- A positive linear semidegree bound for the subsequent directed steps. -/
theorem exists_linear_semidegree_orientation (ρ α : ℝ)
    (hρ : 0 < ρ) (hα : 0 < α) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (r t : ℕ),
      N ≤ Fintype.card V → RobustExpansion.IsRobustAt G r t →
      ρ*(Fintype.card V:ℝ) ≤ (r:ℝ) →
      (∀ v,α*(Fintype.card V:ℝ) ≤ (G.degree v:ℝ)) →
      ∃ D : Digraph V,DirectedRobustExpansion.IsOrientationOf D G ∧
        (∀ v,α*(Fintype.card V:ℝ)/4 < (DirectedRobustExpansion.inDegree D v:ℝ)) ∧
        (∀ v,α*(Fintype.card V:ℝ)/4 < (DirectedRobustExpansion.outDegree D v:ℝ)) ∧
        0 < r/4 ∧ DirectedRobustExpansion.IsRobustAt D (r/4) t := by
  obtain ⟨N,hN⟩ := exists_relative_robust_orientation.{u} ρ α (1/2) hρ hα (by norm_num)
  refine ⟨N,?_⟩
  intro V _ _ G _ r t hn hRobust hr hDegree
  obtain ⟨D,hD,hIn,hOut,hPos,hRD⟩ := hN G r t hn hRobust hr hDegree
  refine ⟨D,hD,?_,?_,hPos,hRD⟩
  · intro v
    have hh := (abs_lt.mp (hIn v)).1
    linarith only [hh,hDegree v]
  · intro v
    have hh := (abs_lt.mp (hOut v)).1
    linarith only [hh,hDegree v]

end OverfullWork.BalancedRobustOrientation
