module

public import OverfullWork.LooplessRealization
public import OverfullWork.CompletionOffCentreBudget
public import OverfullWork.TwoCentreCompletionBarrier

@[expose] public section


/-! A loopless regular completion for two low centres.
The degree imbalance is paid by actual ordinary deficits. No assertion of
global no-overfullness or existence of a colouring is included. -/
namespace OverfullWork.TwoCentreRegularCompletion
open SimpleGraph Finset
open scoped Classical
variable {W : Type*} [Fintype W] [DecidableEq W]
set_option maxHeartbeats 5000000

def ordinaryDeficit (M : MultiGraph (Sum Bool W)) (D : ℕ) : ℕ :=
  ∑ w : W, (D-M.degree (Sum.inr w))

theorem deficit_sum (M : MultiGraph (Sum Bool W)) (D : ℕ) :
    (∑ v, (D-M.degree v))=(D-M.degree (Sum.inl false))+
      (D-M.degree (Sum.inl true))+ordinaryDeficit M D := by
  rw [Fintype.sum_sum_type,Fintype.sum_bool]
  unfold ordinaryDeficit
  omega

theorem deficit_even (M : MultiGraph (Sum Bool W)) (D : ℕ)
    (hD : ∀ v, M.degree v ≤ D) (heven : Even (Fintype.card (Sum Bool W))) :
    Even (∑ v, (D-M.degree v)) := by
  obtain ⟨m,hm⟩ := heven
  have hId := M.total_deficit_of_bounded D hD
  rw [M.sum_degrees_eq_twice_edgeCount,hm] at hId
  have hProd : (m+m)*D=2*(m*D) := by ring
  rw [hProd] at hId
  refine ⟨m*D-M.edgeCount,?_⟩
  omega

theorem deficit_balanced (M : MultiGraph (Sum Bool W)) (D : ℕ)
    (hD : ∀ v, M.degree v ≤ D)
    (hOrder : M.degree (Sum.inl false) ≤ M.degree (Sum.inl true))
    (hGap : M.degree (Sum.inl true) ≤ M.degree (Sum.inl false)+ordinaryDeficit M D)
    (hSmall : ordinaryDeficit M D+M.degree (Sum.inl false)+M.degree (Sum.inl true) ≤ 2*D) :
    ∀ v, 2*(D-M.degree v) ≤ ∑ w, (D-M.degree w) := by
  intro v
  rw [deficit_sum]
  have hA := hD (Sum.inl false)
  have hB := hD (Sum.inl true)
  cases v with
  | inl i => cases i <;> omega
  | inr w =>
    have hw : D-M.degree (Sum.inr w) ≤ ordinaryDeficit M D :=
      single_le_sum (f:=fun w : W => D-M.degree (Sum.inr w))
        (fun _ _ => Nat.zero_le _) (mem_univ w)
    omega

theorem exists_completion (M : MultiGraph (Sum Bool W)) (D : ℕ)
    (hD : ∀ v, M.degree v ≤ D) (heven : Even (Fintype.card (Sum Bool W)))
    (hOrder : M.degree (Sum.inl false) ≤ M.degree (Sum.inl true))
    (hGap : M.degree (Sum.inl true) ≤ M.degree (Sum.inl false)+ordinaryDeficit M D)
    (hSmall : ordinaryDeficit M D+M.degree (Sum.inl false)+M.degree (Sum.inl true) ≤ 2*D) :
    ∃ J : MultiGraph (Sum Bool W),
      (∀ v, J.degree v=D-M.degree v) ∧ (M.addCopies J).IsRegularOfDegree D := by
  obtain ⟨J,hJ⟩ := LooplessRealization.exists_realization (fun v => D-M.degree v)
    (deficit_even M D hD heven) (deficit_balanced M D hD hOrder hGap hSmall)
  refine ⟨J,hJ,?_⟩
  intro v
  rw [MultiGraph.degree_addCopies,hJ]
  exact Nat.add_sub_of_le (hD v)

theorem added_off_first_centre (M J : MultiGraph (Sum Bool W)) (D : ℕ)
    (hReg : (M.addCopies J).IsRegularOfDegree D)
    (hOrder : M.degree (Sum.inl false) ≤ M.degree (Sum.inl true)) :
    J.twiceInternal (univ.erase (Sum.inl false)) ≤ ordinaryDeficit M D := by
  apply CompletionOffCentreBudget.outside_internal_le M J D (ordinaryDeficit M D) (Sum.inl false) hReg
  have hAll := sum_erase_add univ (fun v => D-M.degree v) (mem_univ (Sum.inl false))
  rw [deficit_sum] at hAll
  have hDA := hReg (Sum.inl false)
  have hDB := hReg (Sum.inl true)
  rw [MultiGraph.degree_addCopies] at hDA hDB
  omega

theorem pair_reserve (M J : MultiGraph (Sum Bool W)) (D : ℕ)
    (hJ : ∀ v, J.degree v=D-M.degree v) :
    D ≤ (M.addCopies J).mult s(Sum.inl false,Sum.inl true)+
      M.degree (Sum.inl true)+ordinaryDeficit M D := by
  have hOther : (∑ v ∈ (univ.erase (Sum.inl false)).erase (Sum.inl true),J.degree v)=
      ordinaryDeficit M D := by
    have hAll := sum_erase_add univ (fun v => J.degree v) (mem_univ (Sum.inl false))
    have hSub := sum_erase_add (univ.erase (Sum.inl false)) (fun v => J.degree v)
      (show Sum.inl true ∈ (univ.erase (Sum.inl false) : Finset (Sum Bool W)) by simp)
    have hSum : (∑ v, J.degree v)=J.degree (Sum.inl false)+J.degree (Sum.inl true)+
        ordinaryDeficit M D := by
      simp only [hJ]
      exact deficit_sum M D
    omega
  have hBound := J.degree_le_pair_add_other_degrees (Sum.inl false) (Sum.inl true)
    (by simp)
  rw [hOther,hJ] at hBound
  change D ≤ M.mult _+J.mult _+M.degree (Sum.inl true)+ordinaryDeficit M D
  omega

end OverfullWork.TwoCentreRegularCompletion
