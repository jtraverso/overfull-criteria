module

public import OverfullWork.TwoCentreSupportSplit

@[expose] public section


/-! A finite factorization endpoint for the completed two-low-centre case.
The peeling and the ordinary factorization are constructed by the existing
engines. Every additional hypothesis is an explicit numerical reserve. -/
namespace OverfullWork.TwoCentreHeavyFactorization
open SimpleGraph Finset TwoCentreSupportSplit HeavyPairPeeling HeavyPairBoundary Gate8J2I
open scoped Classical
variable {W : Type*} [Fintype W] [DecidableEq W]
set_option maxHeartbeats 10000000

theorem colourable (M : MultiGraph (Sum Bool W)) (D q C m : ℕ)
    (hReg : M.IsRegularOfDegree D) (hNo : ¬M.HasOverfullSubset D)
    (hSimple : ∀ u v : W, M.mult s(Sum.inr u,Sum.inr v) ≤ 1)
    (hCard : Fintype.card W=2*m) (hm : 4 ≤ m)
    (hq : q=D-M.mult s(Sum.inl false,Sum.inl true))
    (hC : 4000 ≤ C) (hSize : linearHalfBound C (2*q+1) ≤ m)
    (hSlack : 2*m+10*q+12 ≤ 2*D) (hDense : (C+64)*m ≤ C*(D-2*q)) :
    Nonempty (M.EdgeColoring D) := by
  have hEq := split_eq M
  have hBudget := extra_budget M D hReg hSimple
  have hReg' : ((base M).addCopies (extra M)).IsRegularOfDegree D := by rwa [hEq]
  have hNo' : ¬((base M).addCopies (extra M)).HasOverfullSubset D := by rwa [hEq]
  have hBudget' : (extra M).twiceInternal (univ.erase (Sum.inl false)) ≤ 2*q := by omega
  have hCardAll : Fintype.card (Sum Bool W)=2*m+2 := by
    rw [Fintype.card_sum,Fintype.card_bool,hCard]
    omega
  obtain ⟨p⟩ := exists_certificate (base M) (extra M) D (2*q) (Sum.inl false) (Sum.inl true)
    (by simp) (base_star M) hReg' hNo' hBudget'
    (by rw [hCardAll];exact ⟨m+1,by omega⟩) (by omega)
    (by rw [hEq,hCardAll,←hq];omega)
  have hOrdCard : Fintype.card ↥(outside (Sum.inl false : Sum Bool W) (Sum.inl true))=2*m := by
    have hh := card_outside (Sum.inl false : Sum Bool W) (Sum.inl true) (by simp)
    omega
  have hCol := colourable_of_linear_reserve (base M) (extra M) D q (2*q) C m
    (Sum.inl false) (Sum.inl true) (by simpa only [hEq,hq] using p) (by simp)
    (base_star M) hReg' (by rwa [hEq]) hBudget' hC hSize hOrdCard hDense
  rwa [hEq] at hCol

end OverfullWork.TwoCentreHeavyFactorization
