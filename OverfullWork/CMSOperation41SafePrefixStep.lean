module

public import OverfullWork.CMSOperation41PreprocessingLoss
public import OverfullWork.CMSOperation41ExactRecords

@[expose] public section


/-! Applying Claim 4.2(4) to an actual prefix. The deficit of the
two-colour layer is at most two per exceptional vertex and at most
two in total on the ordinary core. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing RobustExpansion
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem missing_degree_bound_from_core_charge (L : SimpleGraph V) [DecidableRel L.Adj]
    (U : Finset V) (hCore : (∑ v ∈ Uᶜ,(2-L.degree v)) ≤ 2) :
    (∑ v,(2-L.degree v)) ≤ 2*U.card+2 := by
  have hU : (∑ v ∈ U,(2-L.degree v)) ≤ 2*U.card := calc
    _ ≤ ∑ _v ∈ U,2 := sum_le_sum (fun v _ => Nat.sub_le 2 (L.degree v))
    _ = _ := by simp [Nat.mul_comm]
  have hSum := sum_add_sum_compl U (fun v => 2-L.degree v)
  omega

theorem realized_trimming_step_no_overfull (G H L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel L.Adj]
    (active U W : Finset V) (degree : V → ℕ) (r t b a B : ℕ)
    (p : DeletionRun W G H) (hClean : G.IsIndepSet (W : Set V) ∨ H=G) (hW : W ⊆ U) :
    let R := sdiff H L
    let d := G.maxDegree
    H.maxDegree = d → 2 ≤ d → L ≤ H → R.maxDegree = d-2 →
    (∀ v,L.degree v ≤ 2) → (∑ v ∈ Uᶜ,(2-L.degree v)) ≤ 2 →
    IsRobustAt R r t → t+2 ≤ d → d ≤ r*r →
    (∀ u v,G.Adj u v → d-b ≤ G.degree u+G.degree v) →
    (∀ v,v ∉ U → d ≤ G.degree v+a) →
    3*b+6*(t+U.card+2) ≤ d → 2*a+2*(t+U.card+2) ≤ d →
    6*U.card+6 ≤ B →
    (∀ v,0 < G.degree v → v ∈ active) →
    (∀ v ∈ active,degree v = G.degree v) →
    ¬HasAlmostOverfullRecord active d B degree → ¬R.HasOverfullSubgraph := by
  intro R d hHMax hD hLe hRMax hLayer hCharge hRob hT hRate hWeak hOrd hM₁ hM₂ hB
    hPositive hExact hNo
  have hWCard : W.card ≤ U.card := card_le_card hW
  have hLoss (v : V) : G.degree v ≤ R.degree v+(U.card+2) := by
    rcases hClean with hInd | hSame
    · have h := degree_loss_from_actual_cleanup_and_layer p hInd hLe hLayer v
      have h' : G.degree v ≤ R.degree v+(W.card+2) := by
        simpa only [R,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using h
      omega
    · have hEq : H.degree v = G.degree v := by
        simp only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
        rw [hSame]
      have h : R.degree v+L.degree v = H.degree v := by
        simpa only [R,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
          MaximumMatching.degree_sdiff_add_of_le H L hLe v
      have hh : L.degree v ≤ U.card+2 := (hLayer v).trans (by omega)
      rw [←hEq,←h]
      exact Nat.add_le_add_left hh _
  have hNo' : ¬HasAlmostOverfullRecord active d (2*U.card+2+4*(U.card+1)) degree := by
    rintro ⟨X,hX,hOdd,hCut⟩
    exact hNo ⟨X,hX,hOdd,by omega⟩
  exact no_overfull_after_clean_and_trim_of_active_records G H L active U degree r t b (U.card+2) a
    (2*U.card+2) (DeletionRun.le_source p) hHMax hD hLe hRMax hLayer
    (missing_degree_bound_from_core_charge L U hCharge) hLoss hRob hT hRate hWeak hOrd
    (by omega) (by omega) hPositive hExact hNo'

end OverfullWork.CMSTrimmingRound
