module

public import OverfullWork.KuhnOsthusExceptionalCapacityScale

@[expose] public section


/-! Choose the capacities and cut threshold in the original
exceptional factor construction. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical

/-- The same reciprocal capacity scale works for each application of
Lemma 7.6. Rounding pays for the cut and makes the loss small enough
for the path-cover construction on the remaining vertices. -/
theorem wound_exceptional_integral_budgets (m c z N : ℕ) (ε δ η d : ℝ)
    (hc : 32 ≤ c) (hm : 2*c ≤ m) (hN : 2*N ≤ m)
    (hε : 0 < ε) (hη : 0 ≤ η) (hη₁ : η ≤ 1/4)
    (hScale : 20 ≤ (c:ℝ)*ε) (hδ : 4*δ ≤ ε)
    (hDensity : 6*ε ≤ d) (hLarge : 1 ≤ ε*(m:ℝ)) :
    let e := ⌊(m:ℝ)*η⌋₊
    let cap := m/c
    let loss := cap+(cap+2)+2*cap
    0 < cap ∧ 2*z+(2*z)/cap*m ≤ (4*c+2)*z ∧
    (m:ℝ)/(2*(c:ℝ)) ≤ (cap:ℝ) ∧
    2*(cap+2+2*cap)+e < m-cap ∧ loss < m ∧ N ≤ m-loss ∧
    ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) ∧
    (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε ∧ (m:ℝ)*η ≤ (e:ℝ)+1 := by
  intro e cap loss
  have hFloor : (e:ℝ) ≤ (m:ℝ)*η := Nat.floor_le (by positivity)
  have hFloor' : (e:ℝ) ≤ (m:ℝ)/4 := by
    linarith only [hFloor,mul_le_mul_of_nonneg_left hη₁ (Nat.cast_nonneg m)]
  have he : e ≤ m/4 := (Nat.le_div_iff_mul_le (by decide)).mpr (by
    exact_mod_cast (show (e:ℝ)*4 ≤ (m:ℝ) by linarith only [hFloor']))
  obtain ⟨hCap,_,hEnds,hSize,hLoss,hRoom⟩ := kuhn_osthus_exceptional_capacities m c z e hc hm he
  have hPos : 0 < m := by omega
  have hLoss' : loss ≤ m/4 := hLoss
  have hLossCast : (loss:ℝ) = 4*(cap:ℝ)+2 := by dsimp only [loss]; push_cast; ring
  have hCapUpper : (cap:ℝ)*(c:ℝ) ≤ m := by exact_mod_cast Nat.div_mul_le_self m c
  have hM : (2:ℝ)*c ≤ m := by exact_mod_cast hm
  have hPaid : (2:ℝ) ≤ (m:ℝ)*ε/20 := by
    have h₁ := mul_le_mul_of_nonneg_right hM hε.le
    linarith only [h₁,hScale]
  have hCapPay : (cap:ℝ) ≤ (m:ℝ)*ε/20 := by
    have h₁ := mul_le_mul_of_nonneg_left hScale (Nat.cast_nonneg cap)
    have h₂ := mul_le_mul_of_nonneg_right hCapUpper hε.le
    linarith only [h₁,h₂]
  have hLossPay : (loss:ℝ) ≤ (m:ℝ)*ε/4 := by linarith only [hPaid,hCapPay,hLossCast]
  have hRem : (3/4:ℝ)*(m:ℝ) ≤ ((m-loss:ℕ):ℝ) := by
    have hl : 4*loss ≤ m := by omega
    have hh : (4:ℝ)*(loss:ℝ) ≤ (m:ℝ) := by exact_mod_cast hl
    rw [Nat.cast_sub (by omega : loss ≤ m)]
    linarith only [hh]
  have hHall : ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) := by
    have h := mul_le_mul_of_nonneg_left hRem (show 0 ≤ d-2*ε by linarith only [hDensity,hε])
    have h' := mul_le_mul_of_nonneg_right (show 4*ε ≤ d-2*ε by linarith only [hDensity])
      (show (0:ℝ) ≤ (3/4)*(m:ℝ) by positivity)
    nlinarith only [h,h',hLarge,mul_nonneg hε.le (Nat.cast_nonneg m)]
  have hPay : (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε := by
    have h := mul_le_mul_of_nonneg_right hRem hε.le
    have h' := mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [h,h',hLossPay,mul_nonneg hε.le (Nat.cast_nonneg m)]
  exact ⟨hCap,hEnds,hSize,hRoom,by omega,by omega,hHall,hPay,(Nat.lt_floor_add_one _).le⟩

end OverfullWork.DirectedRobustExpansion
