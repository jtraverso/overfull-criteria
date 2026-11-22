module

public import OverfullWork.OrdinaryMatchingHamiltonLayer

@[expose] public section


/-! Pack all nonempty parallel-copy matchings into even Hamilton
layers in the successive ordinary supports of CMS §5.2, Case 1. -/
namespace OverfullWork.EvenHamiltonFactorization

open SimpleGraph MultiGraph Finset RobustExpansion
open scoped Classical
universe u

set_option maxHeartbeats 1700000 in
/-- Realize each extra matching in its own Hamilton layer. The
ordinary simple parts are pairwise edge-disjoint and the support
loses at most two edges per vertex per layer. -/
theorem exists_hamilton_layers_through_matchings
    (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (ℓ : ℕ) (J : Fin ℓ → MultiGraph V),
      N ≤ Fintype.card V → Even (Fintype.card V) → IsRealRobust G (2*ν) τ →
      (∀ v, α*(Fintype.card V:ℝ)+2*(ℓ:ℝ) ≤ (G.degree v:ℝ)) →
      2*(ℓ:ℝ) ≤ ν*(Fintype.card V:ℝ) →
      (∀ i v, (J i).degree v ≤ 1) →
      (∀ i, 0 < (J i).edgeCount ∧ ((J i).edgeCount:ℝ) ≤ ν^4*(Fintype.card V:ℝ)) →
      ∃ F : Fin ℓ → SimpleGraph V,
        (∀ i, F i ≤ G) ∧
        (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧
        ∀ i, let L := (ofSimpleGraph (F i)).addCopies (J i)
          L.IsRegularOfDegree 2 ∧ Nonempty (L.EdgeColoring 2) := by
  obtain ⟨N,hN⟩ := exists_coloured_hamilton_layer_through_matching.{u} ν τ α hν hντ hτα hα
  refine ⟨N,?_⟩
  intro V _ _ G _ ℓ J hSize hEven hRob hDeg hBudget hMatching hCount
  induction ℓ with
  | zero =>
    exact ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ ℓ ih =>
    have hL : (ℓ:ℝ) ≤ (↑(ℓ+1 : ℕ):ℝ) := by exact_mod_cast Nat.le_succ ℓ
    obtain ⟨F,hF,hDis,hReg⟩ := ih (fun i => J i.succ)
      (fun v => by linarith only [hL,hDeg v]) (by linarith only [hL,hBudget])
      (fun i v => hMatching i.succ v) (fun i => hCount i.succ)
    let Q := ⨆ i, F i
    let H := G \ Q
    have hQ : Q ≤ G := iSup_le hF
    have hQdeg (v : V) : Q.degree v ≤ 2*ℓ := by
      calc
        _ ≤ ∑ i,(F i).degree v := DenseBatchPathPacking.degree_iSup_le_sum F v
        _ ≤ ∑ _i : Fin ℓ, 2 := by
          apply sum_le_sum
          intro i _
          have h := (hReg i).1 v
          simp only [degree_addCopies,degree_ofSimpleGraph] at h
          omega
        _ = 2*ℓ := by simp [Nat.mul_comm]
    have hPay : ((2*ℓ:ℕ):ℝ) ≤ (2*ν-ν)*(Fintype.card V:ℝ) := by
      push_cast
      linarith only [hL,hBudget]
    have hHRob : IsRealRobust H ν τ :=
      isRealRobust_sdiff_with_loss G Q (2*ν) ν τ τ (2*ℓ) (by linarith only [hν]) le_rfl hPay hQdeg hRob
    have hHDeg (v : V) : α*(Fintype.card V:ℝ) ≤ (H.degree v:ℝ) := by
      have hAdd : (H.degree v:ℝ)+(Q.degree v:ℝ) = (G.degree v:ℝ) := by
        exact_mod_cast MaximumMatching.degree_sdiff_add_of_le G Q hQ v
      have hQv : (Q.degree v:ℝ) ≤ 2*(ℓ:ℝ) := by exact_mod_cast hQdeg v
      linarith only [hL,hAdd,hQv,hDeg v]
    obtain ⟨F₀,hF₀,hF₀Reg⟩ := hN H (J 0) hSize hEven hHRob hHDeg (hMatching 0)
      (hCount 0).1 (hCount 0).2
    have hNewDis (j : Fin ℓ) : Disjoint F₀ (F j) := by
      apply disjoint_iff_inf_le.mpr
      intro x y hxy
      exact ((hF₀ hxy.1).2 ((le_iSup F j) hxy.2)).elim
    let F' : Fin (ℓ+1) → SimpleGraph V := Fin.cases F₀ F
    refine ⟨F',?_,?_,?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => exact hF₀.trans sdiff_le
      | succ i => exact hF i
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact hNewDis j
      | succ i =>
        induction j using Fin.cases with
        | zero => exact (hNewDis i).symm
        | succ j => exact hDis i j (fun h => hij (congrArg Fin.succ h))
    · intro i
      induction i using Fin.cases with
      | zero => exact hF₀Reg
      | succ i => exact hReg i

end OverfullWork.EvenHamiltonFactorization
