module

public import OverfullWork.DirectedResidualCycleAbsorption
public import OverfullWork.LongDirectedCycleFactor
public import OverfullWork.LooplessEndpointContraction

@[expose] public section


/-! The Hamiltonian case of Lo–Patel Theorem 6.1 once the small
absorbing cycle has been constructed. -/
namespace OverfullWork.DirectedAbsorbingLadder

open Finset DirectedRobustExpansion DirectedPrefactor DirectedEndpointContraction
open scoped Classical
variable {V : Type*} [Fintype V]

theorem AbsorbingCycle.hamilton_of_robust (D : Digraph V) (ν τ γ : ℝ) {d : ℕ}
    (C : AbsorbingCycle D d)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1)
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v, γ*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v, γ*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (hReserve : (C.vertices.length:ℝ)+1 ≤ ν*(Fintype.card V:ℝ)/4)
    (hN : 32 ≤ ν*(Fintype.card V:ℝ))
    (hBig : 128 ≤ (ν/2)^3*((Fintype.card V:ℝ)/2))
    (hRound : 4 ≤ (ν^2/32)*((Fintype.card V:ℝ)/2))
    (hd : 4/(ν^2/32) ≤ (d:ℝ)) :
    ∃ T : List V, T.Nodup ∧ (∀ v, v ∈ T) ∧ T.head? = some C.root ∧
      (T ++ [C.root]).IsChain D.Adj := by
  classical
  let E := C.vertices.toFinset
  let X := (univ : Finset V) \ E
  let W := ↥X
  let e : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hRange : ∀ x, x ∈ Set.range e ↔ x ∉ C.vertices := by
    intro x
    constructor
    · rintro ⟨w, rfl⟩ hw
      exact (mem_sdiff.mp w.prop).2 (List.mem_toFinset.mpr hw)
    · intro hw
      exact ⟨⟨x, mem_sdiff.mpr ⟨mem_univ _, fun h => hw (List.mem_toFinset.mp h)⟩⟩, rfl⟩
  have hCard : Fintype.card W = Fintype.card V-E.card := by
    exact (Fintype.card_coe X).trans (card_univ_sdiff E)
  have hEq : (Fintype.card W:ℝ)+(E.card:ℝ) = (Fintype.card V:ℝ) := by
    have h := card_le_univ E
    exact_mod_cast (show Fintype.card W+E.card = Fintype.card V by omega)
  have hDef : Fintype.card V-Fintype.card W = E.card := by
    have h := card_le_univ E
    omega
  have hEC : E.card = C.vertices.length := List.toFinset_card_of_nodup C.simple
  have hLoss : (E.card:ℝ)+1 ≤ ν*(Fintype.card V:ℝ)/4 := by rwa [hEC]
  have hν1 : ν ≤ 1 := by linarith only [hντ, hτγ, hν, hγ]
  have hνγ : ν ≤ γ := by linarith only [hντ, hτγ, hν]
  have hνScale := mul_le_mul_of_nonneg_right hν1 (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  have hγScale := mul_le_mul_of_nonneg_right hνγ (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  have hτScale := mul_le_mul_of_nonneg_right hντ (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  have hW : (Fintype.card V:ℝ)/2 ≤ (Fintype.card W:ℝ) := by linarith only [hEq, hLoss, hνScale]
  have hWν := mul_le_mul_of_nonneg_left hW hν.le
  have hR := robust_loopless_contracted D e e ν τ hν (hν.trans_le hντ) hRobust
    (by linarith only [hWν, hN]) (by linarith only [hτScale, hN])
    (by rw [hDef]; linarith only [hLoss, hνScale])
    (by rw [hDef]; exact hLoss)
  obtain ⟨hMinIn, hMinOut⟩ := semidegrees_loopless_contracted D e e γ
    (hν.le.trans hνγ) hIn hOut (by rw [hDef]; linarith only [hLoss, hγScale, hN])
  let ξ := ν^2/32
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξEq : ξ = (ν/2)^2/8 := by dsimp [ξ]; ring
  have hξBound : ξ ≤ ν/32 := by dsimp [ξ]; nlinarith [mul_le_mul_of_nonneg_left hν1 hν.le]
  have hDegree : 2*τ+ξ+γ/8 ≤ γ/2 := by linarith only [hξBound, hντ, hτγ, hν]
  have hPaid := mul_le_mul_of_nonneg_right hDegree (Nat.cast_nonneg (Fintype.card W) : (0:ℝ) ≤ _)
  have hWγ := mul_le_mul_of_nonneg_left hW (hν.le.trans hνγ)
  have hMargin : 2 ≤ (γ/8)*(Fintype.card W:ℝ) := by linarith only [hWγ, hγScale, hN]
  obtain ⟨σ, hEdge, hCount⟩ := exists_factor_with_few_cycles (looplessContracted D e e)
    (ν/2) (2*τ) ξ (by positivity) (by linarith only [hν1]) (by linarith only [hν,hντ])
    hξ hξEq.le (hBig.trans (mul_le_mul_of_nonneg_left hW (by positivity)))
    (hRound.trans (mul_le_mul_of_nonneg_left hW hξ.le)) hR
    (fun w => by have := hMinIn w; linarith only [this, hPaid, hMargin])
    (fun w => by have := hMinOut w; linarith only [this, hPaid, hMargin])
  exact C.hamilton_of_residual_factor e hRange σ (fun w => (hEdge w).2)
    (by exact_mod_cast hCount.trans hd)

end OverfullWork.DirectedAbsorbingLadder
