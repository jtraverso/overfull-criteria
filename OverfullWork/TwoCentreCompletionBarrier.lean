module

public import OverfullWork.ParallelBudget
public import OverfullWork.MultigraphExtension

@[expose] public section


/-! # Two large deficit centres obstruct a single-centre parallel budget

These statements concern a loopless multigraph with a specified degree
profile, typically the multigraph of added completion edges. They do not
assert that a particular simple graph realizes this profile. In particular,
no graph-family construction or overfullness claim is assumed here.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All multiplicity incident to u, except the pair xu, must be paid by
the degrees of vertices outside those two centres. -/
theorem degree_le_pair_add_other_degrees (M : MultiGraph V) (x u : V) (hxu : x≠u) :
    M.degree u≤M.mult s(x,u)+∑ v∈(univ.erase x).erase u,M.degree v := by
  have hu : u∈(univ.erase x : Finset V) := mem_erase.mpr ⟨hxu.symm,mem_univ u⟩
  have hloop : M.mult s(u,u)=0 := M.loopless s(u,u) (by simp)
  have hs := sum_erase_add (univ.erase x) (fun v => M.mult s(u,v)) hu
  rw [hloop,Nat.add_zero] at hs
  have hx := sum_erase_add univ (fun v => M.mult s(u,v)) (mem_univ x)
  have hrow : M.degree u=M.mult s(x,u)+∑ v∈(univ.erase x).erase u,M.mult s(u,v) := by
    rw [degree_eq_sum_mult,←hx,←hs,Sym2.eq_swap]
    exact Nat.add_comm _ _
  rw [hrow]
  apply Nat.add_le_add_left
  apply sum_le_sum
  intro v _
  have hv := M.mult_pair_le_degree v u
  rwa [Sym2.eq_swap] at hv

/-- A nearly D-sized deficit at u with at most six units elsewhere
forces nearly D parallel copies between the two centres. -/
theorem two_centre_multiplicity_lower_bound (M : MultiGraph V) (x u : V)
    (hxu : x≠u) (D : ℕ) (hu : D-4≤M.degree u)
    (hother : (∑ v∈(univ.erase x).erase u,M.degree v)≤6) :
    D-10≤M.mult s(x,u) := by
  have hh := M.degree_le_pair_add_other_degrees x u hxu
  omega

theorem two_centre_parallel_excess_lower_bounds (M : MultiGraph V) (x u : V)
    (hxu : x≠u) (D : ℕ) (hu : D-4≤M.degree u)
    (hother : (∑ v∈(univ.erase x).erase u,M.degree v)≤6) :
    D-11≤M.parallelExcess x ∧ D-11≤M.parallelExcess u := by
  have hmult := M.two_centre_multiplicity_lower_bound x u hxu D hu hother
  have hx : M.mult s(x,u)-1≤M.parallelExcess x :=
    single_le_sum (f:=fun v => M.mult s(x,v)-1) (fun _ _ => Nat.zero_le _) (mem_univ u)
  have hu' : M.mult s(u,x)-1≤M.parallelExcess u :=
    single_le_sum (f:=fun v => M.mult s(u,v)-1) (fun _ _ => Nat.zero_le _) (mem_univ x)
  have hswap : M.mult s(u,x)=M.mult s(x,u) := by rw [Sym2.eq_swap]
  rw [hswap] at hu'
  constructor <;> omega

/-- Designating any single exceptional centre leaves a different vertex
whose parallel excess is at least D−11. -/
theorem exists_large_parallel_excess_away_from_any_centre (M : MultiGraph V) (x u : V)
    (hxu : x≠u) (D : ℕ) (hu : D-4≤M.degree u)
    (hother : (∑ v∈(univ.erase x).erase u,M.degree v)≤6) (c : V) :
    ∃ v,v≠c ∧ D-11≤M.parallelExcess v := by
  obtain ⟨hx,hu'⟩ := M.two_centre_parallel_excess_lower_bounds x u hxu D hu hother
  by_cases hxc : x=c
  · refine ⟨u,?_,hu'⟩
    intro huc
    exact hxu (hxc.trans huc.symm)
  · exact ⟨x,hxc,hx⟩

/-- A one-centre budget for this degree profile must itself be linear
in D; changing which vertex is exceptional cannot improve the bound. -/
theorem single_centre_budget_lower_bound (M : MultiGraph V) (x u : V)
    (hxu : x≠u) (D : ℕ) (hu : D-4≤M.degree u)
    (hother : (∑ v∈(univ.erase x).erase u,M.degree v)≤6)
    (c : V) (b : ℕ) (hbudget : M.HasParallelBudget c b) : D-11≤b := by
  obtain ⟨v,hvc,hv⟩ := M.exists_large_parallel_excess_away_from_any_centre x u hxu D hu hother c
  exact hv.trans (hbudget v hvc)

end SimpleGraph.MultiGraph
