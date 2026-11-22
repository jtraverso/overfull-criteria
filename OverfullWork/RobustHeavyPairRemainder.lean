module

public import OverfullWork.RobustHeavyPairPeeling
public import OverfullWork.HeavyPairReassembly
public import OverfullWork.CrossingSupportGrowth

@[expose] public section


/-! The ordinary residue after the two-centre cycle removals in
CMS §5.2, Case 1. -/
namespace OverfullWork.HeavyPairPeeling
open SimpleGraph MultiGraph Finset HeavyPairBoundary RobustExpansion PrunedCore
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The real robust-neighbour budget is preserved in the ordinary
support after peeling. Removing a copy can delete a simple edge only
when its pair occurs in the cover. -/
theorem Certificate.ordinary_robust {M : MultiGraph V} {d q : ℕ} {a b : V}
    (c : Certificate M d q a b) (ν ν' τ τ' : ℝ)
    (hν : ν' ≤ ν) (hτ : τ ≤ τ')
    (hLoss : 2*(q:ℝ) ≤ (ν-ν')*((outside a b).card:ℝ))
    (hM : IsRealRobust (M.supportGraph.induce (outside a b : Set V)) ν τ) :
    IsRealRobust (ordinary c.residual a b).supportGraph ν' τ' := by
  let G := M.supportGraph.induce (outside a b : Set V)
  let F := (ordinary c.cover a b).supportGraph
  let R := (ordinary c.residual a b).supportGraph
  have hF (x : outside a b) : F.degree x ≤ 2*q := by
    apply (support_degree_le_degree (ordinary c.cover a b) x).trans
    rw [degree_eq_sum_mult]
    simp only [ordinary_mult]
    rw [sum_coe_sort (outside a b) (fun y : V => c.cover.mult s(x.val,y)),
      ← c.regular x.val,c.cover.degree_eq_sum_mult]
    exact sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hLoss' : ((2*q:ℕ):ℝ) ≤ (ν-ν')*(Fintype.card ↥(outside a b):ℝ) := by
    simpa only [Fintype.card_coe,Nat.cast_mul,Nat.cast_ofNat] using hLoss
  have hRob : IsRealRobust (G \ F) ν' τ' :=
    isRealRobust_sdiff_with_loss G F ν ν' τ τ' (2*q) hν hτ hLoss' hF hM
  have hKeep : G \ F ≤ R := by
    intro x y hxy
    obtain ⟨hOld,hNew⟩ := hxy
    change 0 < M.mult s(x.val,y.val) at hOld
    change ¬ 0 < c.cover.mult s(x.val,y.val) at hNew
    change 0 < M.mult s(x.val,y.val)-c.cover.mult s(x.val,y.val)
    omega
  intro T hLo hHi
  have hSub : realNeighbourhood (G \ F) ν' T ⊆ realNeighbourhood R ν' T := by
    intro v hv
    have hInc :
        neighboursIn (G \ F) T v ≤ neighboursIn R T v := by
      rw [RobustExpansion.neighboursIn_eq_filter_card,RobustExpansion.neighboursIn_eq_filter_card]
      exact card_le_card fun w hw => mem_filter.mpr ⟨(mem_filter.mp hw).1,hKeep (mem_filter.mp hw).2⟩
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2.trans (by exact_mod_cast hInc)⟩
  have hCard : ((realNeighbourhood (G \ F) ν' T).card:ℝ) ≤
      ((realNeighbourhood R ν' T).card:ℝ) := by exact_mod_cast card_le_card hSub
  exact (hRob T hLo hHi).trans hCard

/-- After the ordinary residue is simple, the exact factorization
from CMS Theorem 5.5 supplies all its colours and the original peeled
multigraph receives the disjoint union of the two palettes. -/
theorem colourable_of_simple_robust_residue (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {M : MultiGraph V} {d q : ℕ} {a b : V}
        (c : Certificate M d q a b) (hab : a ≠ b),
        let W := ↥(outside a b)
        let R := ordinary c.residual a b
        N ≤ Fintype.card W → Even (Fintype.card V) → M.IsRegularOfDegree d →
        q = d-M.mult s(a,b) → (∀ e, R.mult e ≤ 1) →
        α*((outside a b).card:ℝ) ≤ ((d-2*q:ℕ):ℝ) →
        IsRealRobust R.supportGraph ν τ → Nonempty (M.EdgeColoring d) := by
  obtain ⟨τ,hτ,hDec⟩ := EvenHamiltonFactorization.robust_regular_colourable.{u} α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν
  obtain ⟨N,hN⟩ := hDec ν hν
  refine ⟨N,?_⟩
  intro V _ _ M d q a b c hab W R hSize hEven hM hq hSimple hDegree hRob
  have hCard : Fintype.card W+2 = Fintype.card V := by
    have h := card_outside a b hab
    dsimp only [W]
    omega
  have hEvenW : Even (Fintype.card W) := by
    obtain ⟨k,hk⟩ := hEven
    exact ⟨k-1,by omega⟩
  have hReg (x : W) : R.supportGraph.degree x = d-2*q := by
    rw [←degree_ofSimpleGraph,of_supportGraph _ hSimple]
    exact c.ordinary_regular hab x
  have hDegree' : α*(Fintype.card W:ℝ) ≤ ((d-2*q:ℕ):ℝ) := by
    simpa only [W,Fintype.card_coe] using hDegree
  obtain ⟨C⟩ := hN R.supportGraph (d-2*q) hSize hEvenW hDegree' hRob hReg
  rw [of_supportGraph _ hSimple] at C
  exact c.colouring_of_ordinary hab hM hq C

end OverfullWork.HeavyPairPeeling
