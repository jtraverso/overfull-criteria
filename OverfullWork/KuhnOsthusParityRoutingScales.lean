module

public import OverfullWork.KuhnOsthusParityAfterChord

@[expose] public section


/-! Choose integral routing thresholds for the parity blocks. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- One strict density margin suffices for the two cluster sizes used
in Lemma 10.5. The ceiling costs at most two units in the route bound. -/
theorem exists_parity_routing_cutoffs (d θ : ℝ) (hθ : 0 < θ) (hd : 2*θ < d)
    (hGap : 28*θ < (d-2*θ)^14*(d-θ)) :
    ∃ N : ℕ, ∀ m : ℕ, 0 < m → N ≤ m →
      ∃ s r : ℕ, 0 < s ∧ 0 < r ∧ (m:ℝ)*θ ≤ (s:ℝ) ∧
        28*((s:ℝ)+1) < (d-2*θ)^14*((d-θ)*(m:ℝ)) ∧
        ∀ ξ : ℝ, ξ ≤ θ → ((2*m:ℕ):ℝ)*ξ ≤ (r:ℝ) ∧
          28*((r:ℝ)+1) < (d-2*ξ)^14*((d-ξ)*((2*m:ℕ):ℝ)) := by
  let g := (d-2*θ)^14*(d-θ)-28*θ
  have hg : 0 < g := sub_pos.mpr hGap
  refine ⟨⌈57/g⌉₊,?_⟩
  intro m hm hN
  have hM : (0:ℝ) < m := by exact_mod_cast hm
  have hN' : 57/g ≤ (m:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hRoom := (div_le_iff₀ hg).mp hN'
  let s := ⌈(m:ℝ)*θ⌉₊
  let r := ⌈((2*m:ℕ):ℝ)*θ⌉₊
  have hs : 0 < s := Nat.ceil_pos.mpr (mul_pos hM hθ)
  have hr : 0 < r := Nat.ceil_pos.mpr (by positivity)
  have hSize : (m:ℝ) ≤ ((2*m:ℕ):ℝ) := by exact_mod_cast (show m ≤ 2*m by omega)
  have hPay (w : ℝ) (hw : (m:ℝ) ≤ w) :
      28*((⌈w*θ⌉₊:ℝ)+1) < (d-2*θ)^14*((d-θ)*w) := by
    have hSmall := Nat.ceil_lt_add_one (mul_nonneg (hM.le.trans hw) hθ.le)
    have hRoom' := hRoom.trans (mul_le_mul_of_nonneg_right hw hg.le)
    dsimp only [g] at hRoom'
    nlinarith only [hRoom',hSmall]
  refine ⟨s,r,hs,hr,Nat.le_ceil _,hPay _ le_rfl,?_⟩
  intro ξ hξ
  have hBase : 0 ≤ d-2*θ := sub_nonneg.mpr hd.le
  have hD : 0 ≤ d-θ := by linarith only [hd,hθ]
  have hPow : (d-2*θ)^14 ≤ (d-2*ξ)^14 := by
    gcongr
  have hTarget : (d-θ)*((2*m:ℕ):ℝ) ≤ (d-ξ)*((2*m:ℕ):ℝ) :=
    mul_le_mul_of_nonneg_right (sub_le_sub_left hξ d) (Nat.cast_nonneg _)
  refine ⟨(mul_le_mul_of_nonneg_left hξ (Nat.cast_nonneg _)).trans (Nat.le_ceil _),?_⟩
  exact (hPay _ hSize).trans_le (mul_le_mul hPow hTarget
    (mul_nonneg hD (Nat.cast_nonneg _)) (pow_nonneg (hBase.trans (by linarith only [hξ])) _))

/-- A positive density admits a tolerance with strict room for the
length-fourteen routes. -/
theorem exists_parity_routing_tolerance (d : ℝ) (hd : 0 < d) :
    ∃ θ : ℝ, 0 < θ ∧ 2*θ < d ∧ 28*θ < (d-2*θ)^14*(d-θ) := by
  let β := d/2
  let θ := min (d/4) (β^15/56)
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hSmall : θ ≤ d/4 := min_le_left _ _
  have hSpend : θ ≤ β^15/56 := min_le_right _ _
  have hLeft : β ≤ d-2*θ := by dsimp only [β]; linarith only [hSmall]
  have hRight : β ≤ d-θ := by dsimp only [β]; linarith only [hSmall,hd]
  have hPower : β^14 ≤ (d-2*θ)^14 := by gcongr
  have hRoom : β^15 ≤ (d-2*θ)^14*(d-θ) := by
    rw [show (15:ℕ) = 14+1 by decide,pow_succ]
    exact mul_le_mul hPower hRight hβ.le (pow_nonneg (hβ.le.trans hLeft) _)
  exact ⟨θ,hθ,by linarith only [hSmall,hd],
    (show 28*θ < β^15 by linarith only [hSpend,pow_pos hβ 15]).trans_le hRoom⟩

end OverfullWork.DirectedRobustExpansion
