module

public import OverfullWork.OrdinaryParallelResidue

@[expose] public section


/-! Apply CMS Theorem 5.5 after all ordinary parallel copies have been
incorporated into the cyclic layers of CMS §5.2, Case 1. -/
namespace OverfullWork.EvenHamiltonFactorization

open Finset SimpleGraph MultiGraph CanonicalPairTriangle RobustExpansion
open scoped Classical
universe u

set_option maxHeartbeats 2200000 in
/-- The complete ordinary factorization from a small partition of the
parallel copies into nonempty matchings. All path covers, surviving
degrees, the simple factorization, and the final palette are outputs. -/
theorem robust_regular_multigraph_colourable_of_parallel_matchings
    (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ∃ μ : ℝ, 0 < μ ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (M : MultiGraph V) (r ℓ : ℕ)
        (J : Fin ℓ → MultiGraph V),
        N ≤ Fintype.card V → Even (Fintype.card V) → α*(Fintype.card V:ℝ) ≤ (r:ℝ) →
        M.IsRegularOfDegree r → IsRealRobust M.supportGraph ν τ →
        sumCopies univ J = M.parallelCopies → (∀ i v, (J i).degree v ≤ 1) →
        (∀ i, 0 < (J i).edgeCount ∧ ((J i).edgeCount:ℝ) ≤ μ^4*(Fintype.card V:ℝ)) →
        2*(ℓ:ℝ) ≤ μ*(Fintype.card V:ℝ) → 8*(ℓ:ℝ) ≤ α*(Fintype.card V:ℝ) →
        Nonempty (M.EdgeColoring r) := by
  obtain ⟨τ₀,hτ₀,hFactor⟩ := robust_regular_colourable.{u} (α/2) (by positivity)
    (by linarith only [hα₁])
  let τ := min τ₀ (α/1024)
  have hτ : 0 < τ := lt_min hτ₀ (by positivity)
  have hτₐ : 256*τ ≤ α/2 := by linarith only [(min_le_right _ _ : τ ≤ α/1024),hα]
  refine ⟨τ,hτ,?_⟩
  intro ν hν
  let μ := min (ν/2) τ
  have hμ : 0 < μ := lt_min (by positivity) hτ
  have hμτ : μ ≤ τ := min_le_right _ _
  have hμν : μ ≤ ν/2 := min_le_left _ _
  obtain ⟨N₀,hN₀⟩ := hFactor μ hμ
  obtain ⟨N₁,hN₁⟩ := exists_hamilton_layers_through_matchings.{u} μ τ (α/2)
    hμ hμτ hτₐ (by linarith only [hα₁])
  refine ⟨μ,hμ,max N₀ N₁,?_⟩
  intro V _ _ M r ℓ J hN hEven hDeg hReg hRob hJ hMatching hCount hLoss hAlpha
  let G := M.supportGraph
  have hNn : 0 ≤ (Fintype.card V:ℝ) := Nat.cast_nonneg _
  have hRob₀ : IsRealRobust G (2*μ) τ := by
    have hμ₂ : 2*μ ≤ ν := by linarith only [hμν]
    simpa only [sdiff_bot] using isRealRobust_sdiff_with_loss G (⊥ : SimpleGraph V)
      ν (2*μ) τ τ 0 hμ₂ le_rfl
      (by simpa only [Nat.cast_zero] using mul_nonneg (sub_nonneg.mpr hμ₂) hNn) (by simp) hRob
  have hOrd (v : V) : G.degree v + M.parallelCopies.degree v = r := by
    have hh := congrArg (fun P : MultiGraph V => P.degree v) M.simple_add_parallelCopies
    rw [degree_addCopies,degree_ofSimpleGraph,hReg] at hh
    exact hh
  have hPar (v : V) : M.parallelCopies.degree v ≤ ℓ := by
    rw [←hJ,degree_sumCopies]
    calc
      _ ≤ ∑ _i : Fin ℓ, 1 := sum_le_sum (fun i _ => hMatching i v)
      _ = ℓ := by simp
  have hOrdReal (v : V) :
      (α/2)*(Fintype.card V:ℝ)+2*(ℓ:ℝ) ≤ (G.degree v:ℝ) := by
    have hEq : (G.degree v:ℝ)+(M.parallelCopies.degree v:ℝ) = (r:ℝ) := by exact_mod_cast hOrd v
    have hParR : (M.parallelCopies.degree v:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hPar v
    nlinarith only [hEq,hParR,hAlpha,hDeg]
  obtain ⟨F,hF,hDis,hLayers⟩ := hN₁ G ℓ J ((le_max_right _ _).trans hN) hEven hRob₀
    hOrdReal hLoss hMatching hCount
  have hTwoℓ : 2*ℓ ≤ r := by
    exact_mod_cast (show (2:ℝ)*(ℓ:ℝ) ≤ (r:ℝ) from (by linarith only [hAlpha,hDeg,Nat.cast_nonneg (α := ℝ) ℓ]))
  let Q := ⨆ i, F i
  let H := G \ Q
  obtain ⟨hH,hExtend⟩ := regular_simple_residue_of_hamilton_layers M r ℓ hReg hTwoℓ J hJ F hF hDis hLayers
  have hQdeg (v : V) : Q.degree v ≤ 2*ℓ := by
    calc
      _ ≤ ∑ i,(F i).degree v := DenseBatchPathPacking.degree_iSup_le_sum F v
      _ ≤ ∑ _i : Fin ℓ, 2 := by
        apply sum_le_sum
        intro i _
        have h := (hLayers i).1 v
        simp only [degree_addCopies,degree_ofSimpleGraph] at h
        omega
      _ = 2*ℓ := by simp [Nat.mul_comm]
  have hHRob : IsRealRobust H μ τ₀ :=
    isRealRobust_sdiff_with_loss G Q ν μ τ τ₀ (2*ℓ) (by linarith only [hν,hμν])
      (min_le_left _ _) (by
        push_cast
        nlinarith only [hLoss,mul_le_mul_of_nonneg_right hμν hNn]) hQdeg hRob
  have hResDeg : (α/2)*(Fintype.card V:ℝ) ≤ ((r-2*ℓ:ℕ):ℝ) := by
    rw [Nat.cast_sub hTwoℓ]
    push_cast
    nlinarith only [hDeg,hAlpha,Nat.cast_nonneg (α := ℝ) ℓ]
  exact hExtend (hN₀ H (r-2*ℓ) ((le_max_left _ _).trans hN) hEven hResDeg hHRob hH)

end OverfullWork.EvenHamiltonFactorization
