module

public import OverfullWork.SupportExcessDiscrepancy
public import OverfullWork.MaximumTwoCore

@[expose] public section


/-! # Isolate a large centre bundle before estimating discrepancy

Only excess away from the centre is charged to the error. This keeps
the estimate useful when a centre bundle has linear multiplicity.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem sum_supportRow_eq_neighboursIn (M : MultiGraph V) (A : Finset V) (v : V) :
    (∑ w ∈ A, M.supportRow v w) = (OverfullWork.PrunedCore.neighboursIn M.supportGraph A v:ℝ) := by
  have hset : ((M.supportGraph.neighborFinset v).filter fun w => w ∈ A) =
      A.filter (fun w => 0 < M.mult s(v,w)) := by
    ext w
    simp only [mem_filter,mem_neighborFinset]
    change (0 < M.mult s(v,w) ∧ w ∈ A) ↔ (w ∈ A ∧ 0 < M.mult s(v,w))
    tauto
  rw [OverfullWork.PrunedCore.neighboursIn,hset,card_eq_sum_ones,Nat.cast_sum]
  simp only [sum_filter,Nat.cast_one,supportRow]

theorem centred_degree_discrepancy (M : MultiGraph V) (A : Finset V) (a v : V) (ha : a ∈ A) :
    |2*(M.degreeInto A v:ℝ)-(M.degree v:ℝ)-((M.mult s(v,a)-1:ℕ):ℝ)| ≤
      |(OverfullWork.PrunedCore.neighboursIn M.supportGraph A v:ℝ)-
        (OverfullWork.PrunedCore.neighboursIn M.supportGraph Aᶜ v:ℝ)|+
      ((∑ w ∈ univ.erase a, (M.mult s(v,w)-1):ℕ):ℝ) := by
  let x : ℝ := ∑ w ∈ A, ((M.mult s(v,w)-1:ℕ):ℝ)
  let y : ℝ := ∑ w ∈ Aᶜ, ((M.mult s(v,w)-1:ℕ):ℝ)
  let e : ℝ := ((M.mult s(v,a)-1:ℕ):ℝ)
  let r : ℝ := ((∑ w ∈ univ.erase a, (M.mult s(v,w)-1):ℕ):ℝ)
  have he : e ≤ x := single_le_sum (f := fun w => ((M.mult s(v,w)-1:ℕ):ℝ))
    (fun _ _ => Nat.cast_nonneg _) ha
  have hy : 0 ≤ y := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hsplit : x+y = e+r := by
    dsimp only [x,y,e,r]
    rw [sum_add_sum_compl,Nat.cast_sum]
    have hh := sum_erase_add univ (fun w => ((M.mult s(v,w)-1:ℕ):ℝ)) (mem_univ a)
    linarith only [hh]
  have herr : |x-y-e| ≤ r := abs_le.mpr ⟨by linarith,by linarith⟩
  have hd := M.degreeInto_add_compl A v
  have hdr : (M.degreeInto A v:ℝ)+(M.degreeInto Aᶜ v:ℝ) = (M.degree v:ℝ) := by exact_mod_cast hd
  have hA := M.degreeInto_eq_support_add_excess A v
  have hAc := M.degreeInto_eq_support_add_excess Aᶜ v
  rw [M.sum_supportRow_eq_neighboursIn] at hA hAc
  change (M.degreeInto A v:ℝ) = _+x at hA
  change (M.degreeInto Aᶜ v:ℝ) = _+y at hAc
  have hid : 2*(M.degreeInto A v:ℝ)-(M.degree v:ℝ)-e =
      ((OverfullWork.PrunedCore.neighboursIn M.supportGraph A v:ℝ)-
        (OverfullWork.PrunedCore.neighboursIn M.supportGraph Aᶜ v:ℝ))+(x-y-e) := by linarith
  change |2*(M.degreeInto A v:ℝ)-(M.degree v:ℝ)-e| ≤ _+r
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add le_rfl herr)

end SimpleGraph.MultiGraph
