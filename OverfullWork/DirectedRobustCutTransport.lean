module

public import OverfullWork.DirectedRobustExpansion

@[expose] public section


/-! Transport undirected robust expansion to actual robust out-expansion
by uniform directed-cut discrepancy. The admissible set-size interval is
unchanged. No Hamiltonicity or spanning-realization claim is made. -/
namespace OverfullWork.DirectedRobustCutTransport
open SimpleGraph Finset PrunedCore RobustExpansion EdgeSigningWeights
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 14000000

theorem robust_of_cut_lower_bound (G : SimpleGraph V) (H : Digraph V)
    [DecidableRel G.Adj] (r s t : ℕ) (E : ℝ)
    (hRobust : IsRobustAt G r t) (hGap : 2*s ≤ r)
    (hError : E < ((r:ℝ)-2*(s:ℝ))*((r:ℝ)-(s:ℝ)))
    (hCuts : ∀ S T : Finset V,(incidences G S T:ℝ) ≤ 2*(DirectedRobustExpansion.incidences H S T:ℝ)+E) :
    DirectedRobustExpansion.IsRobustAt H s t := by
  intro S hLo hHi
  by_contra hBad
  let R := neighbourhood G r S
  let N := DirectedRobustExpansion.neighbourhood H s S
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
        rw [incidences_eq_sum]
        apply sum_le_sum
        intro v hv
        exact (mem_filter.mp (mem_sdiff.mp hv).1).2
  have hTarget : DirectedRobustExpansion.incidences H S B ≤ s*B.card := by
    calc
      _ ≤ ∑ _v ∈ B,s := by
        unfold DirectedRobustExpansion.incidences
        apply sum_le_sum
        intro v hv
        have hn : ¬s ≤ DirectedRobustExpansion.inNeighbours H S v := by
          intro hh
          exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨mem_univ _,hh⟩)
        omega
      _ = _ := by simp [Nat.mul_comm]
  have hSourceR : (r:ℝ)*(B.card:ℝ) ≤ (incidences G S B:ℝ) := by exact_mod_cast hSource
  have hTargetR : (DirectedRobustExpansion.incidences H S B:ℝ) ≤ (s:ℝ)*(B.card:ℝ) := by exact_mod_cast hTarget
  have hBR : (r:ℝ)-(s:ℝ) ≤ (B.card:ℝ) := by
    have hh : (r:ℝ) ≤ (B.card:ℝ)+(s:ℝ) := by exact_mod_cast hB
    linarith only [hh]
  have hGapR : (0:ℝ) ≤ (r:ℝ)-2*(s:ℝ) := by
    have hh : 2*(s:ℝ) ≤ (r:ℝ) := by exact_mod_cast hGap
    linarith only [hh]
  have hProduct := mul_le_mul_of_nonneg_left hBR hGapR
  have hCut := hCuts S B
  nlinarith only [hSourceR,hTargetR,hProduct,hCut,hError]

theorem robust_quarter_of_cut_error (G : SimpleGraph V) (H : Digraph V)
    [DecidableRel G.Adj] (r t : ℕ) (E : ℝ)
    (hRobust : IsRobustAt G r t) (hr : 4 ≤ r) (hError : 8*E ≤ (r:ℝ)^2)
    (hCuts : ∀ S T : Finset V,(incidences G S T:ℝ) ≤ 2*(DirectedRobustExpansion.incidences H S T:ℝ)+E) :
    0 < r/4 ∧ DirectedRobustExpansion.IsRobustAt H (r/4) t := by
  have hFour : 4*(r/4) ≤ r := Nat.mul_div_le r 4
  have hFourR : 4*((r/4:ℕ):ℝ) ≤ (r:ℝ) := by exact_mod_cast hFour
  have hProduct := mul_le_mul_of_nonneg_left hFourR (Nat.cast_nonneg r : (0:ℝ) ≤ r)
  have hPos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hSquare : (0:ℝ) ≤ (((r/4:ℕ):ℝ))^2 := sq_nonneg _
  refine ⟨by omega,robust_of_cut_lower_bound G H r (r/4) t E hRobust (by omega) ?_ hCuts⟩
  nlinarith only [hError,hProduct,hPos,hSquare]

end OverfullWork.DirectedRobustCutTransport
