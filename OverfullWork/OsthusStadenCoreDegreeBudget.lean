module

public import OverfullWork.OsthusStadenExceptionalPhaseSlots

@[expose] public section


/-! The numerical bounds of Osthus–Staden (27)–(28) with integer banks. -/
namespace OverfullWork.DirectedRobustExpansion

/-- The slack in the primary target degree pays for the possibly
incomplete final phase. The bank still satisfies the bound used in (27). -/
theorem core_exception_bank_budget (r s p K : ℕ) (a γ β N m : ℝ)
    (hβ : 0 < β) (ha : 0 ≤ a) (hγ : γ ≤ a) (hm : 0 ≤ m)
    (hr : r = ⌊(a-γ)*(K:ℝ)/β⌋₊)
    (hSlack : (2*(p:ℝ))*β ≤ γ*(K:ℝ))
    (hCells : (2*(s:ℝ))*(p:ℝ)*(2*m)*(K:ℝ) ≤ N) :
    (β*(2*m))*((((2*s)*p*2:ℕ):ℝ)*(exceptionalPhaseBankSize r (2*s) p:ℝ)) ≤
      (s:ℝ)*(a*N) := by
  let S : ℝ := 2*(s:ℝ)
  let P : ℝ := p
  let C : ℝ := ((2*s-1)*(p-1):ℕ)
  let M : ℝ := ((r/(2*p)+1:ℕ):ℝ)
  let k := exceptionalPhaseBankSize r (2*s) p
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hP : 0 ≤ P := Nat.cast_nonneg p
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hDiv : (2*P)*M ≤ (r:ℝ)+2*P := by
    have h := Nat.div_mul_le_self r (2*p)
    have h' : (↑(r/(2*p):ℕ):ℝ)*(2*P) ≤ (r:ℝ) := by
      dsimp only [P]
      exact_mod_cast h
    have hM : M = (↑(r/(2*p):ℕ):ℝ)+1 := by simp only [M,Nat.cast_add,Nat.cast_one]
    rw [hM]
    linarith only [h']
  have hK : 2*(k:ℝ) ≤ M*C := by
    have h : 2*k ≤ (r/(2*p)+1)*((2*s-1)*(p-1)) := by
      unfold k exceptionalPhaseBankSize
      rw [Nat.mul_comm 2]
      exact Nat.div_mul_le_self _ _
    dsimp only [M,C]
    exact_mod_cast h
  have hCoeff : C ≤ S*P := by
    have h : (2*s-1)*(p-1) ≤ (2*s)*p := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    dsimp only [C,S,P]
    exact_mod_cast h
  have hR : β*((r:ℝ)+2*P) ≤ a*(K:ℝ) := by
    have hFloor := Nat.floor_le (div_nonneg (mul_nonneg (sub_nonneg.mpr hγ) (Nat.cast_nonneg K)) hβ.le)
    rw [←hr] at hFloor
    have h := (le_div_iff₀ hβ).mp hFloor
    dsimp only [P]
    linarith only [h,hSlack]
  have hQ : (S*P*2)*(k:ℝ) ≤ (s:ℝ)*((r:ℝ)+2*P)*C := by
    calc
      _ = (s:ℝ)*(2*P)*(2*(k:ℝ)) := by dsimp only [S]; ring
      _ ≤ (s:ℝ)*(2*P)*(M*C) := mul_le_mul_of_nonneg_left hK (by positivity)
      _ = (s:ℝ)*C*((2*P)*M) := by ring
      _ ≤ (s:ℝ)*C*((r:ℝ)+2*P) := mul_le_mul_of_nonneg_left hDiv (mul_nonneg (Nat.cast_nonneg _) hC)
      _ = _ := by ring
  have hPay : a*((K:ℝ)*C*(2*m)) ≤ a*N := by
    have hBound : (K:ℝ)*C*(2*m) ≤ N := by
      have h := mul_le_mul_of_nonneg_left hCoeff
        (show 0 ≤ (K:ℝ)*(2*m) by positivity)
      change S*P*(2*m)*(K:ℝ) ≤ N at hCells
      linarith only [h,hCells]
    exact mul_le_mul_of_nonneg_left hBound ha
  have hEq : ((((2*s)*p*2:ℕ):ℝ)) = S*P*2 := by
    dsimp only [S,P]
    push_cast
    rfl
  rw [hEq]
  calc
    _ ≤ (β*(2*m))*((s:ℝ)*((r:ℝ)+2*P)*C) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = (s:ℝ)*C*(2*m)*(β*((r:ℝ)+2*P)) := by ring
    _ ≤ (s:ℝ)*C*(2*m)*(a*(K:ℝ)) :=
      mul_le_mul_of_nonneg_left hR (show 0 ≤ (s:ℝ)*C*(2*m) by positivity)
    _ = (s:ℝ)*(a*((K:ℝ)*C*(2*m))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hPay (Nat.cast_nonneg s)

/-- Three relative losses and one additive loss suffice for (28).
This form keeps the error from allocating and clipping the pieces
separate from the population and refinement errors. -/
theorem core_exception_degree_budget (s : ℕ) (A u q e ζ z W error : ℝ)
    (hu : 0 ≤ u) (hq : 0 < q) (he : 0 ≤ e) (heζ : e ≤ ζ) (hζ : ζ ≤ 1/4)
    (hs : (1-ζ)*(s:ℝ) ≤ ((s-1:ℕ):ℝ))
    (hBank : u*q ≤ (s:ℝ)*A) (hLoss : z+e*W ≤ ζ*A)
    (hNonneg : 0 ≤ A) (hError : error ≤ ζ*u) :
    (1-4*ζ)*u ≤ ((s-1:ℕ):ℝ)*(1-e)*(A-z-e*W)/q - error := by
  have hζ₀ := he.trans heζ
  have hL : 0 ≤ 1-ζ := by linarith only [hζ]
  have hE : 0 ≤ 1-e := hL.trans (by linarith only [heζ])
  have hRemain : (1-ζ)*A ≤ A-z-e*W := by linarith only [hLoss]
  have hRemPos : 0 ≤ A-z-e*W := (mul_nonneg hL hNonneg).trans hRemain
  have hPay : (1-ζ)^3*u*q ≤ ((s-1:ℕ):ℝ)*(1-e)*(A-z-e*W) := by
    calc
      _ = (1-ζ)^3*(u*q) := by ring
      _ ≤ (1-ζ)^3*((s:ℝ)*A) :=
        mul_le_mul_of_nonneg_left hBank (pow_nonneg hL _)
      _ = ((1-ζ)*(s:ℝ))*(1-ζ)*((1-ζ)*A) := by ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul hs (by linarith only [heζ]) hL (Nat.cast_nonneg _)) hRemain
        (mul_nonneg hL hNonneg) (mul_nonneg (Nat.cast_nonneg _) hE)
  have hDiv := (le_div_iff₀ hq).mpr hPay
  have hCube : 1-3*ζ ≤ (1-ζ)^3 := by
    have h := mul_nonneg (sq_nonneg ζ) (show 0 ≤ 3-ζ by linarith only [hζ])
    nlinarith only [h]
  have hPay' := mul_le_mul_of_nonneg_right hCube hu
  linarith only [hDiv,hPay',hError]

/-- Apply (27) and (28) together to the budget for the physical degree
sum. The additive loss includes splitting and clipping all pieces. -/
theorem core_exception_layer_budget_from_target
    (r s p K M κ : ℕ) (a γ β N m e ζ z error : ℝ)
    (hs : 0 < s) (hp : 3 ≤ p) (hβ : 0 < β) (ha : 0 ≤ a) (hγ : γ ≤ a)
    (hN : 0 ≤ N) (hm : 0 ≤ m) (he : 0 ≤ e) (heζ : e ≤ ζ) (hζ : ζ ≤ 1/4)
    (hr : r = ⌊(a-γ)*(K:ℝ)/β⌋₊)
    (hSlack : (2*(p:ℝ))*β ≤ γ*(K:ℝ))
    (hCells : (2*(s:ℝ))*(p:ℝ)*(2*m)*(K:ℝ) ≤ N)
    (hDirections : (1-ζ)*(s:ℝ) ≤ ((s-1:ℕ):ℝ))
    (hExceptional : z+e*((K:ℝ)*(M:ℝ)) ≤ ζ*(a*N))
    (hError : error ≤ ζ*(β*(2*m))) (hκ : (κ:ℝ) ≤ (1-4*ζ)*(β*(2*m))) :
    let q := ((((2*s)*p*2:ℕ):ℝ)*(exceptionalPhaseBankSize r (2*s) p:ℝ))
    (κ:ℝ) ≤ ((s-1:ℕ):ℝ)*(1-e)*(a*N-z-e*((K:ℝ)*(M:ℝ)))/q-error := by
  intro q
  have hℓ : 0 < (2*s)*p*2 :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by decide)
  have hk : 0 < exceptionalPhaseBankSize r (2*s) p := exceptionalPhaseBankSize_pos (by omega) hp
  have hq : 0 < q := by
    have hℓR : (0:ℝ) < ((2*s)*p*2:ℕ) := by exact_mod_cast hℓ
    have hkR : (0:ℝ) < exceptionalPhaseBankSize r (2*s) p := by exact_mod_cast hk
    exact mul_pos hℓR hkR
  exact hκ.trans (core_exception_degree_budget s (a*N) (β*(2*m)) q e ζ z ((K:ℝ)*(M:ℝ)) error
    (by positivity) hq he heζ hζ hDirections
    (core_exception_bank_budget r s p K a γ β N m hβ ha hγ hm hr hSlack hCells)
    hExceptional (mul_nonneg ha hN) hError)

end OverfullWork.DirectedRobustExpansion
