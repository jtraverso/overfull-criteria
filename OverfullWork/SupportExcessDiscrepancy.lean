module

public import OverfullWork.CentreControl

@[expose] public section


/-! # Deterministic discrepancy of the parallel excess

Only the simple support is randomized. The entire parallel excess is
paid in L1, avoiding its square in the variance bound.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def supportRow (M : MultiGraph V) (v w : V) : ℝ :=
  if 0<M.mult s(v,w) then 1 else 0

theorem supportRow_bounds (M : MultiGraph V) (v w : V) :
    0≤M.supportRow v w ∧ M.supportRow v w≤1 := by
  unfold supportRow
  split_ifs <;> norm_num

theorem mult_eq_support_add_excess (M : MultiGraph V) (v w : V) :
    (M.mult s(v,w):ℝ)=M.supportRow v w+((M.mult s(v,w)-1:ℕ):ℝ) := by
  unfold supportRow
  by_cases hp : 0<M.mult s(v,w)
  · rw [if_pos hp]
    have hh : M.mult s(v,w)=1+(M.mult s(v,w)-1):=by omega
    exact_mod_cast hh
  · have hz : M.mult s(v,w)=0:=by omega
    simp [hz]

theorem degreeInto_eq_support_add_excess (M : MultiGraph V) (A : Finset V) (v : V) :
    (M.degreeInto A v:ℝ)=(∑ w∈A,M.supportRow v w)+
      ∑ w∈A,((M.mult s(v,w)-1:ℕ):ℝ) := by
  simp only [degreeInto,Nat.cast_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro w _
  exact M.mult_eq_support_add_excess v w

/-- The signed error of the excess is bounded by its total mass, for
any partition, independently of how the signs were selected. -/
theorem degree_discrepancy_le_support_add_excess (M : MultiGraph V) (A : Finset V) (v : V) :
    |(M.degreeInto A v:ℝ)-(M.degreeInto Aᶜ v:ℝ)|≤
      |(∑ w∈A,M.supportRow v w)-(∑ w∈Aᶜ,M.supportRow v w)|+(M.parallelExcess v:ℝ) := by
  let a : ℝ:=∑ w∈A,((M.mult s(v,w)-1:ℕ):ℝ)
  let b : ℝ:=∑ w∈Aᶜ,((M.mult s(v,w)-1:ℕ):ℝ)
  have ha : 0≤a:=sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hb : 0≤b:=sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hab : a+b=(M.parallelExcess v:ℝ) := by
    dsimp [a,b,parallelExcess]
    rw [Nat.cast_sum,sum_add_sum_compl]
  have herr : |a-b|≤(M.parallelExcess v:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [ha,hb,hab]
  rw [M.degreeInto_eq_support_add_excess A v,M.degreeInto_eq_support_add_excess Aᶜ v]
  change |((∑ w∈A,M.supportRow v w)+a)-((∑ w∈Aᶜ,M.supportRow v w)+b)|≤_
  calc
    _ = |((∑ w∈A,M.supportRow v w)-(∑ w∈Aᶜ,M.supportRow v w))+(a-b)|:=by congr 1;ring
    _ ≤ |(∑ w∈A,M.supportRow v w)-(∑ w∈Aᶜ,M.supportRow v w)|+|a-b|:=abs_add_le _ _
    _ ≤ _:=add_le_add le_rfl herr

end SimpleGraph.MultiGraph
