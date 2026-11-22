module

public import OverfullWork.RobustTotalDeletion
public import OverfullWork.GeneralBipartiteRegularitySource

@[expose] public section


/-! Construct a robust pure graph from simple-graph regularity as in
CMS Lemma 5.4. The ambient loss bound is in total degree. -/
namespace OverfullWork.RobustExpansion

open Finset SimpleGraph Finpartition
open scoped Classical
universe u

/-- The actual regularity partition of a robust simple graph has a
pure graph that is still robust. No minimum-degree assumption is
needed at this step. -/
theorem exists_cms_robust_pure_partition
    (ν τ ε d β : ℝ) (kMin : ℕ) (hν : 0 < ν) (hε : 0 < ε) (hd : 0 ≤ d) (hβ : 0 < β)
    (hBudget : 4*ε+β/2+4*d ≤ (ν/2)^2) :
    ∃ K N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → IsRealRobust G ν τ →
      ∃ P : Finpartition (univ : Finset V),
        P.IsEquipartition ∧ P.IsUniform G ε ∧ kMin ≤ P.parts.card ∧ P.parts.card ≤ K ∧
        IsRealRobust (G.regularityReduced P ε d) (ν/2) τ := by
  let k := max kMin ⌈4/β⌉₊
  refine ⟨SzemerediRegularity.bound ε k,max 1 k,?_⟩
  intro V _ _ G dec hN hRob
  have hDec : dec = fun a b => Classical.propDecidable (G.Adj a b) := by
    funext a b
    exact Subsingleton.elim _ _
  subst dec
  letI : Nonempty V := Fintype.card_pos_iff.mp ((le_max_left _ _).trans hN)
  obtain ⟨P,hEqui,hLow,hHigh,hUnif⟩ := szemeredi_regularity G hε ((le_max_right _ _).trans hN)
  refine ⟨P,hEqui,hUnif,(le_max_left _ _).trans hLow,hHigh,?_⟩
  let H := G.regularityReduced P ε d
  let F := G \ H
  have hParts : 4/β ≤ (P.parts.card:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right kMin ⌈4/β⌉₊).trans hLow)
  have hOrder := BipartiteRegularitySource.general_ordered_reduction_budget
    G P ε d β hε hd hβ hEqui hUnif hParts
  have hSumNat :
      (∑ v, F.degree v) = ((univ ×ˢ univ).filter fun xy : V × V => F.Adj xy.1 xy.2).card := by
    simp only [degree,neighborFinset_eq_filter,card_filter,sum_product]
  have hSum : (∑ v, (F.degree v:ℝ)) ≤ ((ν-ν/2)*(Fintype.card V:ℝ))^2 := by
    rw [←Nat.cast_sum,hSumNat]
    change (((univ ×ˢ univ).filter fun xy : V × V =>
      G.Adj xy.1 xy.2 ∧ ¬H.Adj xy.1 xy.2).card:ℝ) ≤ _
    refine hOrder.trans ?_
    calc
      _ ≤ (ν/2)^2*(Fintype.card V:ℝ)^2 := mul_le_mul_of_nonneg_right hBudget (sq_nonneg _)
      _ = _ := by ring
  have hR := isRealRobust_sdiff_of_total_degree_loss G F ν (ν/2) τ τ
    (by linarith only [hν]) le_rfl hSum hRob
  have hLe : H ≤ G := regularityReduced_le
  have hEq : G \ F = H := by
    ext x y
    change G.Adj x y ∧ ¬(G.Adj x y ∧ ¬H.Adj x y) ↔ H.Adj x y
    exact ⟨fun h => by by_contra hn; exact h.2 ⟨h.1,hn⟩, fun h => ⟨hLe h,fun hh => hh.2 h⟩⟩
  exact isRealRobust_mono_simple (G \ F) H hEq.le (ν/2) τ hR

end OverfullWork.RobustExpansion
