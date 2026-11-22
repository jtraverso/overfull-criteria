module

public import OverfullWork.CMSOddDeficitStop
public import OverfullWork.CMSOperation42StopCases

@[expose] public section


/-! The empty active complement is reduced to the actual induced
odd core with no change to the edge-colouring problem. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion OddCutDeficit CanonicalRegularization
open scoped Classical
universe u

set_option maxHeartbeats 1400000 in
theorem cms_colourable_of_empty_active_complement_stop (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ : ℝ,0 < σ ∧ ∀ ν : ℝ,0 < ν → ν ≤ σ/4 →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (B : ℕ),
          let n := Fintype.card V
          let m := X.card
          let d := G.maxDegree
          N ≤ m → Odd m → α*(m:ℝ) ≤ (d:ℝ) → B+7 ≤ d →
          ((B+4:ℕ):ℝ) ≤ 5*η*((m:ℝ)-1) →
          ClassTwoMatchingRun.budget G X ≤ d+B →
          (∑ y ∈ Xᶜ,G.degree y) = 0 →
          ¬G.HasOverfullSubgraph → IsRealRobust G (8*ν) σ →
          (Xᶜ.card:ℝ) ≤ ν*(n:ℝ) → 4*(Xᶜ.card:ℝ) ≤ σ*(n:ℝ) →
          G.EdgeColorable d := by
  obtain ⟨τ,hτ,hUse⟩ := cms_colourable_of_odd_deficit_stop.{u} α hα hα₁
  let σ := min (τ/4) (1/2)
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hστ : σ ≤ τ/4 := min_le_left _ _
  have hHalf : σ ≤ 1/2 := min_le_right _ _
  refine ⟨σ,hσ,?_⟩
  intro ν hν hνσ
  obtain ⟨ηMax,hηMax,hUse⟩ := hUse ν hν (by linarith only [hνσ,hστ,hσ])
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N,hN⟩ := hUse η hη hηMax
  refine ⟨N,?_⟩
  intro V _ _ G _ X B n m d hn hOdd hDens hRoom hScale hBudget hZero hNo hRob hSmall hSmallτ
  have hSupport : G.support ⊆ (X : Set V) := by
    intro v hv
    by_contra h
    have hvY : v ∈ Xᶜ := mem_compl.mpr h
    have hPos := (G.degree_pos_iff_mem_support v).mpr hv
    have hD : G.degree v ≤ ∑ y ∈ Xᶜ,G.degree y :=
      single_le_sum (f := fun y => G.degree y) (fun _ _ => Nat.zero_le _) hvY
    omega
  let J := G.induce (X : Set V)
  have hCard : Fintype.card (↥(X : Set V)) = m := Fintype.card_coe X
  have hMax : J.maxDegree = d := maxDegree_induce_of_positive_support_subset G X hSupport (by omega)
  have hDeg (v : X) : J.degree v = G.degree v.val := by
    simpa only [J,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      G.degree_induce_of_support_subset hSupport v
  have hBudget' : deficitMass J J.maxDegree univ ≤ J.maxDegree+B := by
    have hDef : deficitMass J d univ = deficitMass G d X := by
      unfold deficitMass
      simp_rw [hDeg]
      exact (sum_subtype X (fun _=>Iff.rfl) (fun v=>d-G.degree v)).symm
    unfold ClassTwoMatchingRun.budget at hBudget
    change deficitMass G d X+(∑ y ∈ Xᶜ,G.degree y) ≤ d+B at hBudget
    rw [hMax,hDef]
    omega
  have hRobJ := induced_graph_robust_of_small_complement G X (8*ν) σ
    (by positivity) (by linarith only [hνσ,hHalf]) hσ.le hHalf hRob
    (by change 8*(Xᶜ.card:ℝ) ≤ (8*ν)*(n:ℝ); nlinarith only [hSmall]) hSmallτ
  have hRob' : IsRealRobust J (4*ν) (τ/2) := by
    intro A hLo hHi
    have hT := mul_le_mul_of_nonneg_right (show 2*σ ≤ τ/2 by linarith only [hστ])
      (Nat.cast_nonneg (α := ℝ) (Fintype.card (↥(X : Set V))))
    have h := hRobJ A (hT.trans hLo) (by linarith only [hHi,hT])
    rwa [show 8*ν/2 = 4*ν by ring] at h
  have hNoJ := Critical.no_overfull_of_copy (Copy.induce G (X : Set V)) hMax hNo
  have hColour := hN J B (by rwa [hCard]) (by rwa [hCard]) (by rwa [hCard,hMax])
    (by rwa [hMax]) (by rwa [hCard]) hBudget' hNoJ hRob'
  exact colourable_of_induced_support_subset G X hSupport d (by rwa [hMax] at hColour)

end OverfullWork.CMSMatchingRemoval
