module

public import OverfullWork.KuhnOsthusChordRoundBudgets

@[expose] public section


/-! Integral choices for the arc counts and the footprint of one
round of Kühn–Osthus Lemma 9.7. -/
namespace OverfullWork.DirectedRobustExpansion

/-- Divide a real-valued scale down to an integer while keeping
the article's exact degree for the universal-walk reserve. -/
theorem chord_round_integer_scales (f g ell k m a : ℕ) (hf : 0 < f) (hk : 0 < k)
    (hm : m = 4*ell*a) (hLarge : 24*f ≤ 8*g^2*m)
    (hFine : 4*ell*390*(8*g^2) ≤ f) :
    let q := f*k
    let scale := (8*g^2*m)/f
    let degree := 96*ell*g^2*k
    let cap := (2*g^2*(k*m))/q
    24 ≤ scale ∧
      q*(12*scale) ≤ 4*(degree*a) ∧
      4*(degree*a) ≤ q*(12*(scale+1)) ∧
      3*scale*q ≤ degree*a ∧
      3*(130*scale) ≤ a ∧
      3*cap ≤ scale ∧
      cap ≤ scale/2 := by
  intro q scale degree cap
  let p := 8*g^2*m
  have hs : scale*f ≤ p := Nat.div_mul_le_self _ _
  have hRem := Nat.mod_add_div p f
  have hRemLt := Nat.mod_lt p hf
  have hsp : p < (scale+1)*f := by
    change p%f+f*scale = p at hRem
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm scale f]
    omega
  have hTarget : 4*(degree*a) = 12*p*k := by
    dsimp [degree,p]
    rw [hm]
    ring
  have hLow : q*(12*scale) ≤ 4*(degree*a) := by
    rw [hTarget]
    calc
      q*(12*scale) = 12*(scale*f)*k := by dsimp [q]; ring
      _ ≤ _ := Nat.mul_le_mul_right k (Nat.mul_le_mul_left 12 hs)
  have hHigh : 4*(degree*a) ≤ q*(12*(scale+1)) := by
    rw [hTarget]
    calc
      12*p*k ≤ 12*((scale+1)*f)*k := Nat.mul_le_mul_right k (Nat.mul_le_mul_left 12 hsp.le)
      _ = _ := by dsimp [q]; ring
  have hWindow : 3*scale*q ≤ degree*a := by
    have hq : 4*(3*scale*q) ≤ 4*(degree*a) := by
      convert hLow using 1
      ring
    omega
  have hRoom : 390*scale ≤ a := by
    apply Nat.le_of_mul_le_mul_right _ hf
    calc
      (390*scale)*f ≤ 390*p := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hs
      _ = (4*ell*390*(8*g^2))*a := by dsimp [p]; rw [hm]; ring
      _ ≤ a*f := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right a hFine
  have hCap : cap = (2*g^2*m)/f := by
    change (2*g^2*(k*m))/(f*k) = _
    have he : 2*g^2*(k*m) = (2*g^2*m)*k := by ring
    rw [he,Nat.mul_div_mul_right _ _ hk]
  have hCapPay : cap*f ≤ 2*g^2*m := by rw [hCap]; exact Nat.div_mul_le_self _ _
  have hCapBound : 3*cap ≤ scale := by
    apply (Nat.le_div_iff_mul_le hf).mpr
    rw [Nat.mul_assoc]
    calc
      3*(cap*f) ≤ 3*(2*g^2*m) := Nat.mul_le_mul_left _ hCapPay
      _ = 6*(g^2*m) := by ring
      _ ≤ 8*(g^2*m) := Nat.mul_le_mul_right _ (by decide)
      _ = 8*g^2*m := by ring
  exact ⟨(Nat.le_div_iff_mul_le hf).mpr hLarge,hLow,hHigh,hWindow,by omega,hCapBound,by omega⟩

/-- Convert the integer footprint from the realized rounds to the
small footprint used in the common cycle completion. -/
theorem integer_chord_round_footprint_budget (f g ell m : ℕ) (ρ : ℝ)
    (hf : 0 < f)
    (hFine : (1+26*(ell:ℝ))*(8*(g:ℝ)^2) ≤ (ρ/512)*(f:ℝ)) :
    let scale := (8*g^2*m)/f
    let K := scale+2*(ell*(13*scale))
    (K:ℝ) ≤ (ρ/512)*(m:ℝ) := by
  intro scale K
  have hScale : (scale:ℝ) ≤ (8*(g:ℝ)^2/(f:ℝ))*(m:ℝ) := by
    have h := Nat.div_mul_le_self (8*g^2*m) f
    have hf' : (0:ℝ) < f := by exact_mod_cast hf
    rw [←mul_div_right_comm]
    apply (le_div_iff₀ hf').mpr
    exact_mod_cast h
  apply chord_round_footprint_budget f g ell m K ρ hf _ hFine
  have hCard : (K:ℝ) = (1+26*(ell:ℝ))*(scale:ℝ) := by
    dsimp only [K]
    push_cast
    ring
  rw [hCard,mul_assoc]
  exact mul_le_mul_of_nonneg_left hScale (by positivity)

end OverfullWork.DirectedRobustExpansion
