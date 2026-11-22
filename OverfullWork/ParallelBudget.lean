module

public import OverfullWork.AvailableNeighbours

@[expose] public section


/-! # Bounded excess multiplicity, stable under deleting copies -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def parallelExcess (M : MultiGraph V) (v : V) : ℕ :=
  ∑ w : V,(M.mult s(v,w)-1)

def HasParallelBudget (M : MultiGraph V) (x : V) (b : ℕ) : Prop :=
  ∀ v,v≠x → M.parallelExcess v≤b

theorem parallelBudget_mono (M N : MultiGraph V) (x : V) (b : ℕ)
    (hle : ∀ e,N.mult e≤M.mult e) (h : M.HasParallelBudget x b) : N.HasParallelBudget x b := by
  intro v hv
  change (∑ w : V,(N.mult s(v,w)-1))≤b
  have hm : (∑ w : V,(M.mult s(v,w)-1))≤b:=h v hv
  exact (sum_le_sum (s:=univ) (fun w _ => Nat.sub_le_sub_right (hle s(v,w)) 1)).trans hm

theorem parallelBudget_of_star (M : MultiGraph V) (x : V)
    (hstar : M.IsStarAt x) (hmu : ∀ e,M.mult e≤2) : M.HasParallelBudget x 3 := by
  intro v hv
  have hp : ∀ w : V,M.mult s(v,w)-1≤ if w=x then 1 else 0 := by
    intro w
    by_cases hw : w=x
    · rw [if_pos hw]
      have h:=hmu s(v,w)
      omega
    · rw [if_neg hw]
      have h:=hstar v w hv hw
      omega
  have h:=sum_le_sum (s:=univ) (fun w _ => hp w)
  have hs : (∑ w : V,if w=x then 1 else 0)=1:=by simp
  rw [hs] at h
  exact h.trans (by omega)

theorem degreeInto_le_neighbours_add_budget (M : MultiGraph V) (S : Finset V)
    (v x : V) (b : ℕ) (h : M.HasParallelBudget x b) (hv : v≠x) :
    M.degreeInto S v≤(M.neighboursInto S v).card+b := by
  have hp : ∀ w∈S,M.mult s(v,w)≤(if 0<M.mult s(v,w) then 1 else 0)+(M.mult s(v,w)-1) := by
    intro w _
    split_ifs <;> omega
  have hs:=sum_le_sum hp
  rw [sum_add_distrib] at hs
  have hcard : (∑ w∈S,if 0<M.mult s(v,w) then 1 else 0)=(M.neighboursInto S v).card := by
    simp only [neighboursInto,card_eq_sum_ones,sum_filter]
  have he : (∑ w∈S,(M.mult s(v,w)-1))≤M.parallelExcess v := by
    change (∑ w∈S,(M.mult s(v,w)-1))≤∑ w : V,(M.mult s(v,w)-1)
    exact sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  rw [hcard] at hs
  exact hs.trans (Nat.add_le_add_left (he.trans (h v hv)) _)

end SimpleGraph.MultiGraph
