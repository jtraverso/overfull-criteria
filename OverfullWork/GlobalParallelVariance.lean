module

public import OverfullWork.ParallelVariance

@[expose] public section


/-! # Variance energy with a parallel budget at every vertex

There is no exceptional row, so the square-range S^2<=m suffices.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_row_square_cubes_le_all_budget (M : MultiGraph V)
    (m D b S : ℕ) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hD : D≤2*m)
    (hbudget : ∀ v,M.parallelExcess v≤b) (hbS : b≤S)
    (hS : 1≤S) (hS2 : S^2≤m) :
    (∑ v : V,(M.rowSquares v)^3)≤128*m^4 := by
  have hSm : S≤m := by
    have hh : S^1≤S^2:=pow_le_pow_right₀ hS (by omega : 1≤2)
    simpa using hh.trans hS2
  have hbprod:=Nat.mul_le_mul (Nat.succ_le_succ hbS) hbS
  have hA : D+(b+1)*b≤4*m:=by nlinarith only [hbprod,hD,hS2,hSm]
  have hrow : ∀ v : V,M.rowSquares v≤4*m := by
    intro v
    have hh:=M.row_squares_le_degree_add_budget v b (hbudget v)
    rw [hreg v] at hh
    exact hh.trans hA
  have hs:=sum_le_sum (s:=univ) (fun v _ => Nat.pow_le_pow_left (hrow v) 3)
  calc
    _ ≤ ∑ _v : V,(4*m)^3:=hs
    _ = (2*m)*(4*m)^3:=by simp only [sum_const,card_univ,hcard,Nat.nsmul_eq_mul]
    _ = _:=by ring

/-- Real form of the energy estimate, with no multiplicity hypothesis. -/
theorem sum_real_row_square_cubes_le_all_budget (M : MultiGraph V)
    (m D b S : ℕ) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hD : D≤2*m)
    (hbudget : ∀ v,M.parallelExcess v≤b) (hbS : b≤S)
    (hS : 1≤S) (hS2 : S^2≤m) :
    (∑ v : V,(∑ w : V,(M.mult s(v,w):ℝ)^2)^3)≤128*(m:ℝ)^4 := by
  simp_rw [M.sum_real_squares_eq]
  exact_mod_cast M.sum_row_square_cubes_le_all_budget m D b S hcard hreg hD hbudget hbS hS hS2

end SimpleGraph.MultiGraph
