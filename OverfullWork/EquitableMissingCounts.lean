module

public import OverfullWork.EquitableRecolouring
public import OverfullWork.WeightedMissingBudget

@[expose] public section


/-! # Missing vertices per color in an equitable multigraph coloring

Exact double counting gives the parity and the factor-two balance of
missing-set sizes. Averaging turns a total missing-incidence bound into
the per-color bound required for CMS MCC-pair processing.
-/
namespace SimpleGraph.MultiGraph.EdgeColoring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 8000000

theorem missing_card_add_twice_mass (C : M.EdgeColoring k) (i : Fin k) :
    (C.missingSet univ i).card+2*C.colourMass i=Fintype.card V := by
  have hh := C.missing_card_add_degree_sum univ i
  rw [card_univ,(C.colourGraph i).sum_degrees_eq_twice_edgeCount] at hh
  exact hh

theorem missing_card_even (C : M.EdgeColoring k) (hV : Even (Fintype.card V)) (i : Fin k) :
    Even (C.missingSet univ i).card := by
  obtain ⟨m,hm⟩ := hV
  have hh := C.missing_card_add_twice_mass i
  exact ⟨m-C.colourMass i,by omega⟩

theorem equitable_missing_balance (C : M.EdgeColoring k) (hC : C.IsEquitable) (i j : Fin k) :
    (C.missingSet univ i).card ≤ (C.missingSet univ j).card+2 := by
  have hi := C.missing_card_add_twice_mass i
  have hj := C.missing_card_add_twice_mass j
  have hc := hC j i
  omega

theorem sum_missing_card_eq (C : M.EdgeColoring k) :
    (∑ i, (C.missingSet univ i).card) = ∑ v, (C.missingPalette v).card := by
  have hh := C.sum_missingWeight univ (fun _ => 1)
  simpa only [missingWeight,missingSet,sum_const,smul_eq_mul,mul_one,one_mul] using hh

theorem equitable_missing_average (C : M.EdgeColoring k) (hC : C.IsEquitable) (i : Fin k) :
    k*(C.missingSet univ i).card ≤ (∑ v, (C.missingPalette v).card)+2*k := by
  have hh := sum_le_sum (s := (univ : Finset (Fin k))) (fun j _ => C.equitable_missing_balance hC i j)
  rw [sum_add_distrib,C.sum_missing_card_eq] at hh
  simpa only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_comm k 2] using hh

theorem equitable_missing_real_bound (C : M.EdgeColoring k) (hC : C.IsEquitable) (R A : ℝ)
    (hk : 0 < k) (hA : 0 ≤ A) (hV : (Fintype.card V:ℝ) ≤ R*(k:ℝ))
    (hTotal : (∑ v, ((C.missingPalette v).card:ℝ)) ≤ (Fintype.card V:ℝ)*A)
    (i : Fin k) : ((C.missingSet univ i).card:ℝ) ≤ R*A+2 := by
  have hcount : (k:ℝ)*((C.missingSet univ i).card:ℝ) ≤
      (∑ v, ((C.missingPalette v).card:ℝ))+2*(k:ℝ) := by
    exact_mod_cast C.equitable_missing_average hC i
  have hVmul := mul_le_mul_of_nonneg_right hV hA
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  nlinarith only [hcount,hTotal,hVmul,hkR]

end SimpleGraph.MultiGraph.EdgeColoring
