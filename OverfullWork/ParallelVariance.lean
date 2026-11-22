module

public import OverfullWork.ParallelBudget
public import OverfullWork.PairedPartition

@[expose] public section


/-! # Squared multiplicities controlled by parallel excess

The squared norm of an ordinary row is degree plus a quadratic excess
term, instead of the maximum multiplicity squared times the order.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def rowSquares (M : MultiGraph V) (v : V) : ℕ :=
  ∑ w : V,(M.mult s(v,w))^2

theorem row_squares_le_degree_add_excess (M : MultiGraph V) (v : V) (μ : ℕ)
    (hmu : ∀ w,M.mult s(v,w)≤μ) :
    M.rowSquares v≤M.degree v+μ*M.parallelExcess v := by
  have hp : ∀ w : V,(M.mult s(v,w))^2≤M.mult s(v,w)+μ*(M.mult s(v,w)-1) := by
    intro w
    have hh:=hmu w
    by_cases hz : M.mult s(v,w)=0
    · simp [hz]
    · have he : M.mult s(v,w)-1+1=M.mult s(v,w):=by omega
      nlinarith only [hh,he]
  have hs:=sum_le_sum (s:=univ) (fun w _ => hp w)
  simpa only [rowSquares,degree_eq_sum_mult,parallelExcess,sum_add_distrib,mul_sum] using hs

theorem row_squares_le_degree_add_budget (M : MultiGraph V) (v : V) (b : ℕ)
    (hbudget : M.parallelExcess v≤b) :
    M.rowSquares v≤M.degree v+(b+1)*b := by
  have hmu : ∀ w,M.mult s(v,w)≤b+1 := by
    intro w
    have hh : M.mult s(v,w)-1≤M.parallelExcess v :=
      single_le_sum (f:=fun w => M.mult s(v,w)-1) (fun _ _ => Nat.zero_le _) (mem_univ w)
    omega
  exact (M.row_squares_le_degree_add_excess v (b+1) hmu).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left (b+1) hbudget) _)

theorem row_squares_le_cap_mul_degree (M : MultiGraph V) (v : V) (μ : ℕ)
    (hmu : ∀ w,M.mult s(v,w)≤μ) :
    M.rowSquares v≤μ*M.degree v := by
  have hs:=sum_le_sum (s:=univ) (fun w _ => Nat.mul_le_mul_right (M.mult s(v,w)) (hmu w))
  simpa only [rowSquares,degree_eq_sum_mult,pow_two,mul_sum] using hs

theorem sum_real_squares_eq (M : MultiGraph V) (v : V) :
    (∑ w : V,(M.mult s(v,w):ℝ)^2)=(M.rowSquares v:ℝ) := by
  simp only [rowSquares,Nat.cast_sum,Nat.cast_pow]

end SimpleGraph.MultiGraph

namespace OverfullWork.PairedPartition
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- Pair differences have no larger squared norm than the original
nonnegative weights. This works for every fixed pairing. -/
theorem pair_difference_squares_le (e : (Fin m×Bool) ≃ V) (w : V → ℝ)
    (hw : ∀ v,0≤w v) :
    (∑ i : Fin m,(w (e (i,true))-w (e (i,false)))^2)≤∑ v : V,(w v)^2 := by
  have hp : ∀ i : Fin m,(w (e (i,true))-w (e (i,false)))^2≤
      (w (e (i,true)))^2+(w (e (i,false)))^2 := by
    intro i
    have hh:=mul_nonneg (hw (e (i,true))) (hw (e (i,false)))
    nlinarith only [hh]
  have he : (∑ i : Fin m,((w (e (i,true)))^2+(w (e (i,false)))^2))=∑ v : V,(w v)^2 := by
    have hh:=e.sum_comp (fun v => (w v)^2)
    simpa only [Fintype.sum_prod_type,Fintype.sum_bool] using hh
  exact (sum_le_sum (s:=univ) (fun i _ => hp i)).trans_eq he

end OverfullWork.PairedPartition

namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exceptional row is charged once, rather than using its cap on
every ordinary row. No regularity assumption is needed for this bound. -/
theorem sum_row_square_cubes_le (M : MultiGraph V) (x : V) (D b μ : ℕ)
    (hdeg : ∀ v,M.degree v≤D) (hbudget : M.HasParallelBudget x b)
    (hcentre : ∀ w,M.mult s(x,w)≤μ) :
    (∑ v : V,(M.rowSquares v)^3)≤
      (Fintype.card V-1)*(D+(b+1)*b)^3+(μ*D)^3 := by
  have hrow : ∀ v∈(univ.erase x : Finset V),M.rowSquares v≤D+(b+1)*b := by
    intro v hv
    have hvx : v≠x:=(mem_erase.mp hv).1
    exact (M.row_squares_le_degree_add_budget v b (hbudget v hvx)).trans
      (Nat.add_le_add_right (hdeg v) _)
  have hcx : M.rowSquares x≤μ*D:=
    (M.row_squares_le_cap_mul_degree x μ hcentre).trans (Nat.mul_le_mul_left μ (hdeg x))
  have hs:=sum_le_sum (s:=univ.erase x) (fun v hv => Nat.pow_le_pow_left (hrow v hv) 3)
  have hx:=Nat.pow_le_pow_left hcx 3
  have he : (∑ v∈univ.erase x,(M.rowSquares v)^3)+(M.rowSquares x)^3=
      ∑ v : V,(M.rowSquares v)^3:=sum_erase_add _ _ (mem_univ x)
  have hc : (univ.erase x : Finset V).card=Fintype.card V-1:=by simp
  simpa only [sum_const,hc,Nat.nsmul_eq_mul,he] using Nat.add_le_add hs hx

/-- A weighted-pairing sixth-moment budget. The right side uses the
ordinary excess and only one exceptional row of cap mu. -/
theorem sum_paired_variance_cubes_le {m : ℕ} (M : MultiGraph V)
    (e : (Fin m×Bool) ≃ V) (x : V) (D b μ : ℕ)
    (hdeg : ∀ v,M.degree v≤D) (hbudget : M.HasParallelBudget x b)
    (hcentre : ∀ w,M.mult s(x,w)≤μ) :
    (∑ v : V,(∑ i : Fin m,
      ((M.mult s(v,e (i,true)):ℝ)-(M.mult s(v,e (i,false)):ℝ))^2)^3)≤
      ((Fintype.card V-1:ℕ):ℝ)*((D+(b+1)*b:ℕ):ℝ)^3+((μ*D:ℕ):ℝ)^3 := by
  have hp : ∀ v : V,(∑ i : Fin m,
      ((M.mult s(v,e (i,true)):ℝ)-(M.mult s(v,e (i,false)):ℝ))^2)≤(M.rowSquares v:ℝ) := by
    intro v
    have hh:=OverfullWork.PairedPartition.pair_difference_squares_le e
      (fun w => (M.mult s(v,w):ℝ)) (fun _ => Nat.cast_nonneg _)
    rwa [M.sum_real_squares_eq v] at hh
  have hs:=sum_le_sum (s:=univ) (fun v _ => pow_le_pow_left₀
    (by positivity : (0:ℝ)≤∑ i : Fin m,
      ((M.mult s(v,e (i,true)):ℝ)-(M.mult s(v,e (i,false)):ℝ))^2) (hp v) 3)
  have hnat:=M.sum_row_square_cubes_le x D b μ hdeg hbudget hcentre
  have hreal : (∑ v : V,(M.rowSquares v:ℝ)^3)≤
      ((Fintype.card V-1:ℕ):ℝ)*((D+(b+1)*b:ℕ):ℝ)^3+((μ*D:ℕ):ℝ)^3 := by
    exact_mod_cast hnat
  exact hs.trans hreal

end SimpleGraph.MultiGraph

namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the dense range with S^3<=m, the total variance-cube budget is
independent of S. The exceptional centre contributes only once. -/
theorem sum_row_square_cubes_le_dense (M : MultiGraph V) (x : V)
    (m D b μ S : ℕ) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hD : D≤2*m)
    (hmu : ∀ e,M.mult e≤μ) (hmuS : μ≤2*S)
    (hbudget : M.HasParallelBudget x b) (hbS : b≤S)
    (hS : 1≤S) (hS3 : S^3≤m) :
    (∑ v : V,(M.rowSquares v)^3)≤192*m^4 := by
  have hS2m : S^2≤m:=(pow_le_pow_right₀ hS (by omega : 2≤3)).trans hS3
  have hSm : S≤m := by
    have hh : S^1≤S^3:=pow_le_pow_right₀ hS (by omega : 1≤3)
    simpa using hh.trans hS3
  have hbprod:=Nat.mul_le_mul (Nat.succ_le_succ hbS) hbS
  have hA : D+(b+1)*b≤4*m:=by nlinarith only [hbprod,hD,hS2m,hSm]
  have hB : μ*D≤4*S*m := by
    have hh:=Nat.mul_le_mul hmuS hD
    nlinarith only [hh]
  have hs:=M.sum_row_square_cubes_le x D b μ (fun v => (hreg v).le)
    hbudget (fun w => hmu s(x,w))
  have hcard' : Fintype.card V-1≤2*m:=by omega
  have hp:=Nat.add_le_add (Nat.mul_le_mul hcard' (Nat.pow_le_pow_left hA 3))
    (Nat.pow_le_pow_left hB 3)
  have hcenter:=Nat.mul_le_mul_right (64*m^3) hS3
  calc
    _ ≤ (Fintype.card V-1)*(D+(b+1)*b)^3+(μ*D)^3:=hs
    _ ≤ (2*m)*(4*m)^3+(4*S*m)^3:=hp
    _ ≤ _:=by nlinarith only [hcenter]

/-- Real version matching the row-squared-weight norm of a variance
partition theorem. -/
theorem sum_real_row_square_cubes_le_dense (M : MultiGraph V) (x : V)
    (m D b μ S : ℕ) (hcard : Fintype.card V=2*m)
    (hreg : M.IsRegularOfDegree D) (hD : D≤2*m)
    (hmu : ∀ e,M.mult e≤μ) (hmuS : μ≤2*S)
    (hbudget : M.HasParallelBudget x b) (hbS : b≤S)
    (hS : 1≤S) (hS3 : S^3≤m) :
    (∑ v : V,(∑ w : V,(M.mult s(v,w):ℝ)^2)^3)≤192*(m:ℝ)^4 := by
  simp_rw [M.sum_real_squares_eq]
  exact_mod_cast M.sum_row_square_cubes_le_dense x m D b μ S hcard hreg hD hmu hmuS hbudget hbS hS hS3

end SimpleGraph.MultiGraph
