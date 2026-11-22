module

public import OverfullWork.CMSTwoCentreBaseOddCuts

@[expose] public section


/-! Discharge no-overfullness for the two identified parts by the
ordinary source bounds and the actual degree imbalance. -/
namespace OverfullWork.TwoIndependentIdentifications

open Finset SimpleGraph RobustExpansion TwoCentreOrdinaryCore
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem no_overfull_two_identifications_of_robust (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hInd : G.IsIndepSet (Z : Set V)) (r t : ℕ) :
    let M := graph G Z A hA hInd
    let d := G.maxDegree
    Even (Fintype.card (Vertices Z)) → ¬G.HasOverfullSubgraph →
    IsRobustAt M.supportGraph r t → d ≤ r*r →
    (∀ x y : Outside Z, x ≠ y →
      d+2*t ≤ M.supportGraph.degree (Sum.inr x)+M.supportGraph.degree (Sum.inr y)) →
    M.degree (Sum.inl false)+M.degree (Sum.inl true) ≤ d →
    (∀ x : Outside Z, M.degree (Sum.inl false) ≤ G.degree x.val) →
    M.degree (Sum.inl false) ≤ M.degree (Sum.inl true) →
    M.degree (Sum.inl true) ≤ M.degree (Sum.inl false)+(∑ x : Outside Z, (d-G.degree x.val)) →
    ¬M.HasOverfullSubset d := by
  intro M d hEven hNo hRob hRate hOrd hSum hMin hOrder hImbalance
  have hD (v : Vertices Z) : M.degree v ≤ d := by
    cases v with
    | inl i => cases i <;> omega
    | inr x =>
      change (graph G Z A hA hInd).degree (Sum.inr x) ≤ d
      rw [degree_inr]
      exact G.degree_le_maxDegree x.val
  have hTotal : (∑ v : Vertices Z, (d-M.degree v)) =
      (d-M.degree (Sum.inl false))+(d-M.degree (Sum.inl true))+
        (∑ x : Outside Z,(d-G.degree x.val)) := by
    rw [Fintype.sum_sum_type,Fintype.sum_bool]
    change d-M.degree (Sum.inl true)+(d-M.degree (Sum.inl false))+
        (∑ x : Outside Z, (d-(graph G Z A hA hInd).degree (Sum.inr x))) = _
    simp_rw [degree_inr]
    ac_rfl
  apply no_overfull_of_robust_two_centre_base M d r t hEven hD hRob hRate hOrd hSum
  · intro x
    change M.degree (Sum.inl false) ≤ (graph G Z A hA hInd).degree (Sum.inr x)
    rw [degree_inr]
    exact hMin x
  · intro i
    rw [hTotal]
    have ha := hD (Sum.inl false)
    have hb := hD (Sum.inl true)
    cases i <;> omega
  · exact no_overfull_ordinary G Z A hA hInd hNo

end OverfullWork.TwoIndependentIdentifications
