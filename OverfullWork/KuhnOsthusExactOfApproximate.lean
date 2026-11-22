module

public import OverfullWork.KuhnOsthusAbsorptionFromRobustHost
public import OverfullWork.RobustVertexSamplingTheorem

@[expose] public section


/-! The exact directed and undirected decompositions from the
approximate packing of Osthus–Staden. -/
namespace OverfullWork.DirectedRobustExpansion

universe u

/-- Existence part of Osthus–Staden Theorem 1.1 in the real-parameter
robust expansion convention. -/
def RobustApproximateHamiltonPacking : Prop :=
  ∀ α : ℝ, 0 < α → ∃ τ : ℝ, 0 < τ ∧
    ∀ ν η : ℝ, 0 < ν → 0 < η → ∃ N : ℕ,
    ∀ {V : Type u} [Fintype V] (D : Digraph V) (r : ℕ),
      N ≤ Fintype.card V → α*(Fintype.card V:ℝ) ≤ (r:ℝ) → IsRealRobust D ν τ →
      (∀ v, inDegree D v = r ∧ outDegree D v = r) → (∀ v, ¬ D.Adj v v) →
      ∃ (s : ℕ) (C : Fin s → Equiv.Perm V), (1-η)*(r:ℝ) ≤ (s:ℝ) ∧ matchingUnion C ≤ D ∧
        (∀ i, HasSpanningCycle (fun x y => C i x = y)) ∧ ∀ i j, i ≠ j → ∀ v, C i v ≠ C j v

set_option maxHeartbeats 950000 in
/-- The two universal reserve operators apply to the remainder of the
approximate packing at the end of Kühn–Osthus Theorem 1.2. All choices,
including the relative packing error, precede the order of the host. -/
theorem kuhn_osthus_directed_decomposition_of_approximate
    (hApprox : RobustApproximateHamiltonPacking.{u}) :
    ∀ α : ℝ, 0 < α → ∃ τ : ℝ, 0 < τ ∧
      ∀ ν : ℝ, 0 < ν → ∃ N : ℕ, ∀ {V : Type u} [Fintype V]
        (G : Digraph V) (r : ℕ), N ≤ Fintype.card V →
        α*(Fintype.card V:ℝ) ≤ (r:ℝ) → IsRealRobust G ν τ →
        (∀ v, outDegree G v = r ∧ inDegree G v = r) → (∀ v, ¬ G.Adj v v) →
        Nonempty (DirectedHamiltonDecomposition G r) := by
  intro α hα
  let β := min (α/8) 1
  have hβ : 0 < β := lt_min (by positivity) (by norm_num)
  have hβ₁ : β ≤ 1 := min_le_right _ _
  have hβα : 8*β ≤ α := by linarith only [(min_le_left _ _ : β ≤ α/8)]
  obtain ⟨τ₀,hτ₀,hPack⟩ := hApprox β hβ
  let τ := min τ₀ (β/128)
  have hτ : 0 < τ := lt_min hτ₀ (by positivity)
  have hτβ : 128*τ ≤ β := by linarith only [(min_le_right _ _ : τ ≤ β/128)]
  refine ⟨τ,hτ,?_⟩
  intro ν hν
  let μ := min ν (min τ 1)
  have hμ : 0 < μ := lt_min hν (lt_min hτ (by norm_num))
  have hμ₁ : μ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hμτ : μ ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
  let d := min (μ/16) β
  have hd : 0 < d := lt_min (by positivity) hβ
  have hdμ : 8*d ≤ μ := by linarith only [(min_le_left _ _ : d ≤ μ/16),hμ]
  obtain ⟨d₁,ζ,hd₁,hζ,hζμ,hζSize,hBudget,hBudget',hReserves⟩ :=
    exists_kuhn_osthus_absorption_from_robust_host.{u} μ τ β d (1/2) 802 le_rfl
      hμ hμ₁ hμτ hβ hβ₁ (by linarith only [hτβ,hτ]) hd hdμ (min_le_right _ _) (by norm_num) (by norm_num)
  obtain ⟨η,hη,hηβ,N₁,hN₁⟩ := hReserves β hβ
  obtain ⟨N₂,hN₂⟩ := hPack (μ/2) η (by positivity) hη
  obtain ⟨N₃,hN₃⟩ := kuhn_osthus_final_assembly_of_relative_approximate_pack.{u} μ τ β d₁ ζ η
    hμ hμ₁ hμτ hτβ hβ₁ hd₁.le hη.le hηβ hζμ hζSize hBudget hBudget'
  refine ⟨max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro V _ G r hN hDense hRob hReg hLoop
  let _ : Nonempty V := Fintype.card_pos_iff.mp ((le_max_left _ _).trans hN)
  have hReg' (v : V) : inDegree G v = r ∧ outDegree G v = r := (hReg v).symm
  have hRob' : IsRealRobust G μ τ := real_robust_mono G (min_le_left _ _) le_rfl hRob
  have hDense' : (8*β)*(Fintype.card V:ℝ) ≤ (r:ℝ) :=
    (mul_le_mul_of_nonneg_right hβα (Nat.cast_nonneg _)).trans hDense
  obtain ⟨Z,P,B,m,b,t,_,hm,hr,hZ,hB,hLe,hDis,hDeg,_,hProcess,hAbsorb⟩ :=
    hN₁ G r ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) hRob' hDense' hReg' hLoop
  have hDense₂ : 2*β*(Fintype.card V:ℝ) ≤ (r:ℝ) := by
    linarith only [hDense',mul_nonneg hβ.le (Nat.cast_nonneg (Fintype.card V))]
  refine hN₃ G P B Z r b t m ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
    hm hr hDense₂ hZ hB hLoop hReg' hRob' hLe hDis hDeg ?_ hProcess hAbsorb
  intro D hD hDRob hDReg hDDense
  exact hN₂ D (r-b-4*Z.card) ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
    hDDense (real_robust_mono D le_rfl (min_le_left _ _) hDRob) hDReg (fun v h => hLoop v (hD h))

/-- The existence assertion of CMS Theorem 5.5 follows from the same
approximate packing theorem on loopless directed graphs. -/
theorem cms_theorem_5_5_of_approximate
    (hApprox : RobustApproximateHamiltonPacking.{u}) (α : ℝ) (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
        N ≤ Fintype.card V → α*(Fintype.card V:ℝ) ≤ 2*(k:ℝ) → RobustExpansion.IsRealRobust G ν τ →
        (∀ v, G.degree v = 2*k) → Nonempty (HamiltonDecomposition G k) :=
  robust_even_decomposition_of_loopless_directed (kuhn_osthus_directed_decomposition_of_approximate hApprox) α hα

end OverfullWork.DirectedRobustExpansion
