module

public import OverfullWork.RobustBatchPathPacking
public import OverfullWork.HeavyPairPeeling
public import OverfullWork.RobustShortPaths

@[expose] public section


/-! The two-centre Hamilton-cycle removals of CMS §5.2, Case 1. -/
namespace OverfullWork.RobustExpansion
open Finset SimpleGraph PrunedCore
open scoped Classical
universe u

/-- Inducing on a large set costs at most the number of deleted
vertices in the robust neighbourhood. -/
theorem isRealRobust_induce_with_loss {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (ν ν' τ τ' : ℝ)
    (hWin : τ*(Fintype.card V:ℝ) ≤ τ'*(X.card:ℝ))
    (hLoss : ν'*(X.card:ℝ)+((univ \ X).card:ℝ) ≤ ν*(Fintype.card V:ℝ))
    (hRob : IsRealRobust G ν τ) : IsRealRobust (G.induce (X : Set V)) ν' τ' := by
  intro A hLo hHi
  let H := G.induce (X : Set V)
  let B := A.image Subtype.val
  have hB : B.card = A.card := card_image_of_injective _ Subtype.val_injective
  have hC : Fintype.card ↥(X : Set V) = X.card := Fintype.card_coe X
  rw [hC] at hLo hHi
  have hOrder : (X.card:ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast card_le_univ X
  have hGrow := hRob B (by rw [hB]; linarith only [hWin,hLo])
    (by rw [hB]; nlinarith only [hWin,hHi,hOrder])
  have hSub : realNeighbourhood G ν B \ (univ \ X) ⊆
      (realNeighbourhood H ν' A).image Subtype.val := by
    intro v hv
    obtain ⟨hv,hvX⟩ := mem_sdiff.mp hv
    have hvX' : v ∈ X := by simpa using hvX
    let w : ↥(X : Set V) := ⟨v,hvX'⟩
    have hOcc := (mem_filter.mp hv).2
    have hEq := RobustShortPaths.neighboursIn_induce_image G (X : Set V) A w
    have hF : Subtype.fintype (Membership.mem (X : Set V)) = FinsetCoe.fintype X :=
      Subsingleton.elim _ _
    rw [hF] at hEq
    change neighboursIn H A w = neighboursIn G B v at hEq
    have hw : w ∈ realNeighbourhood H ν' A := mem_filter.mpr ⟨mem_univ _,by
      rw [hC,hEq]
      linarith only [hOcc,hLoss,Nat.cast_nonneg (α := ℝ) (univ \ X).card]⟩
    exact mem_image.mpr ⟨w,hw,rfl⟩
  have hBound := card_le_card hSub
  rw [card_image_of_injective _ Subtype.val_injective] at hBound
  have hPaid : ((realNeighbourhood G ν B).card:ℝ) ≤
      ((realNeighbourhood H ν' A).card:ℝ)+((univ \ X).card:ℝ) := by
    exact_mod_cast (card_le_card_sdiff_add_card (s := realNeighbourhood G ν B)
      (t := univ \ X)).trans (Nat.add_le_add_right hBound _)
  rw [hB] at hGrow
  change _ ≤ ((realNeighbourhood H ν' A).card:ℝ)
  rw [hC]
  linarith only [hGrow,hPaid,hLoss]

end OverfullWork.RobustExpansion

namespace OverfullWork.HeavyPairPeeling
open Finset SimpleGraph HeavyPairBoundary RobustExpansion
open scoped Classical
universe u

/-- The ordinary support can be below the Dirac threshold. Robust
linkage in successive residues constructs the same actual peeling
certificate as in the dense version of Case 1. -/
theorem exists_robust_certificate (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (M : MultiGraph V) (d : ℕ)
      (a b : V) (hab : a ≠ b),
      let W := ↥(outside a b)
      let G := M.supportGraph.induce (outside a b : Set V)
      let q := d-M.mult s(a,b)
      N ≤ Fintype.card W → Even (Fintype.card V) →
      M.IsRegularOfDegree d → ¬ M.HasOverfullSubset d →
      IsRealRobust G (2*ν) τ →
      (∀ w, α*(Fintype.card W:ℝ)+2*(q:ℝ) ≤ (G.degree w:ℝ)) →
      2*(q:ℝ) ≤ ν*(Fintype.card W:ℝ) →
      q ≤ M.mult s(a,b) → Nonempty (Certificate M d q a b) := by
  obtain ⟨N,hN⟩ := DenseBatchPathPacking.exists_robust_packing.{u} ν τ α hν hντ hτα hα
  obtain ⟨N',hN'⟩ := exists_nat_ge (1/ν^4)
  refine ⟨max 2 (max N N'),?_⟩
  intro V _ _ M d a b hab W G q hSize hEven hReg hNo hRob hDeg hBudget hCopies
  have hCore : 2 ≤ Fintype.card W := (le_max_left _ _).trans hSize
  have hSizeN : N ≤ Fintype.card W := (le_max_left _ _).trans ((le_max_right _ _).trans hSize)
  have hSizeN' : N' ≤ Fintype.card W := (le_max_right _ _).trans ((le_max_right _ _).trans hSize)
  have hOne : 1 ≤ ν^4*(Fintype.card W:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ (pow_pos hν 4)).mp (hN'.trans (by exact_mod_cast hSizeN'))
  obtain ⟨e,he,hCard⟩ := exists_boundary_pairing M d hReg hNo a b hab
  let f : Fin q ≃ (Σ w : outside a b, Fin (M.mult s(a,w.val))) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hCard.symm)
  obtain ⟨P⟩ := hN G q 1 (fun j _ => (f j).1) (fun j _ => (e (f j)).1)
    hSizeN hRob hDeg hBudget (by decide) (by
      rw [Nat.cast_one]
      exact hOne)
    (fun _ _ _ _ => Subsingleton.elim _ _) (fun _ _ _ _ => Subsingleton.elim _ _)
    (fun j i k h => he (f j) (congrArg Subtype.val h))
  exact certificate_of_boundary_packing M d a b hab hReg hEven hCore hCopies f (f.trans e) P

end OverfullWork.HeavyPairPeeling
