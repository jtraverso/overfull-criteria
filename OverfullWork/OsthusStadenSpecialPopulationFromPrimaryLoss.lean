module

public import OverfullWork.OsthusStadenSpecialExceptionOccurrences

@[expose] public section


/-! Count the special exceptional set using the actual adaptive loss.
Core exceptions do not contribute to its load on the special bank. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

/-- The special set in a layer contains at most the vertices removed
from its primary classes plus one per refined p-cell. -/
theorem special_population_bound_from_primary_loss
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero s] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ η d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) s p m τ τ τ}
    (A : UnwoundPrimarySlices G thin E g σ τ η d R)
    (f : V → Option I) (M : ℕ) (loss trim : ℝ)
    (hBase : ∀ i, (cluster f i).card = M)
    (hSize : ∀ t i, (cluster (g t) i).card = s*(p*(2*m)) ∧ cluster (g t) i ⊆ cluster f i)
    (hDrop : ((M-s*(p*(2*m)):ℕ):ℝ) ≤ loss*(M:ℝ))
    (hLoss : 0 ≤ loss) (hCost : 1 ≤ trim*((2*m:ℕ):ℝ))
    (erase : RefinedFactorIndex r s p → RefinedVertex I s p → V)
    (bridges : RefinedFactorIndex r s p → Finset V) (j : RefinedFactorIndex r s p) :
    ((specialExceptions (exceptional f) (fun k => primaryPCells (R k.1)) erase bridges j).card:ℝ) ≤
      (loss+trim)*(Fintype.card V:ℝ) := by
  let K := Fintype.card I
  let n := Fintype.card V
  let U := Fintype.card (RefinedVertex I s p)
  let mOrd := s*(p*(2*m))
  have hU : U = K*s*p := by simp [U,K,RefinedVertex,ZMod.card]
  have hBaseOrder : n = (exceptional f).card+M*K := order_eq f M hBase
  have hOrder : n = (exceptional (g j.1)).card+mOrd*K :=
    order_eq (g j.1) mOrd (fun i => (hSize j.1 i).1)
  have hSub : exceptional f ⊆ exceptional (g j.1) := by
    intro x hx
    apply (mem_exceptional _ x).mpr
    cases he : g j.1 x with
    | none => rfl
    | some i =>
      have hi := (hSize j.1 i).2 ((mem_cluster (g j.1) i x).mpr he)
      have hNone := (mem_exceptional f x).mp hx
      rw [(mem_cluster f i x).mp hi] at hNone
      contradiction
  have hNew : ((exceptional (g j.1)) \ exceptional f).card = (M-mOrd)*K := by
    rw [card_sdiff_of_subset hSub,Nat.sub_mul]
    omega
  have hBasePart : ((M:ℕ):ℝ)*(K:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (show M*K ≤ n by omega)
  have hOldLoss : (((M-mOrd:ℕ)*K:ℕ):ℝ) ≤ loss*(n:ℝ) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (loss*(M:ℝ))*(K:ℝ) := mul_le_mul_of_nonneg_right hDrop (Nat.cast_nonneg _)
      _ = loss*((M:ℝ)*(K:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hBasePart hLoss
  have hCellPart : (U:ℝ)*((2*m:ℕ):ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (show U*(2*m) ≤ n by
      rw [hU,show K*s*p*(2*m) = mOrd*K by dsimp only [mOrd]; ring]
      omega)
  have hTrim : 0 ≤ trim := by
    by_contra! h
    have hzero := mul_nonpos_of_nonpos_of_nonneg h.le (Nat.cast_nonneg (α := ℝ) (2*m))
    linarith only [hzero,hCost]
  have hExtra : (U:ℝ) ≤ trim*(n:ℝ) := by
    calc
      _ ≤ (U:ℝ)*(trim*((2*m:ℕ):ℝ)) := le_mul_of_one_le_right (Nat.cast_nonneg _) hCost
      _ = trim*((U:ℝ)*((2*m:ℕ):ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCellPart hTrim
  have hCard := special_exception_size_on_trimmed_layers A (exceptional f) erase bridges j
  rw [hNew] at hCard
  have hBound : ((specialExceptions (exceptional f) (fun k => primaryPCells (R k.1)) erase bridges j).card:ℝ) ≤
      (((M-mOrd:ℕ)*K:ℕ):ℝ)+(U:ℝ) := by exact_mod_cast hCard
  nlinarith only [hBound,hOldLoss,hExtra]

end OverfullWork.DirectedRobustExpansion
