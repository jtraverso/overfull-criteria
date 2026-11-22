module

public import OverfullWork.SimpleColouringBridge
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section


/-! # Alternating split of a simple cycle

All non-root vertices receive one edge of each colour. The root may
receive both edges of one colour when the cycle length is odd.
-/
namespace OverfullWork.DeterministicSplit
open SimpleGraph Finset
open scoped Classical
set_option maxHeartbeats 4000000

/-- Index the cyclic edge i--(i+1) by i, including the wrap edge. -/
def cycleIndex (n : ℕ) (u v : Fin (n+3)) : ℕ :=
  if min u.val v.val=0 ∧ max u.val v.val=n+2 then n+2 else min u.val v.val

theorem cycleIndex_symm (n : ℕ) (u v : Fin (n+3)) : cycleIndex n u v=cycleIndex n v u := by
  simp only [cycleIndex,min_comm,max_comm]

theorem cycleIndex_successor (n : ℕ) (v : Fin (n+3)) : cycleIndex n v (v+1)=v.val := by
  by_cases hv : v=Fin.last (n+2)
  · subst v
    simp [cycleIndex]
  · simp only [cycleIndex,Fin.val_add_one,if_neg hv,
      Nat.min_eq_left (Nat.le_succ v.val),Nat.max_eq_right (Nat.le_succ v.val)]
    split_ifs <;> omega

theorem cycleIndex_predecessor (n : ℕ) (v : Fin (n+3)) : cycleIndex n v (v-1)=(v-1).val := by
  have hh:=cycleIndex_successor n (v-1)
  have he : v-1+1=v:=sub_add_cancel _ _
  rw [he] at hh
  exact (cycleIndex_symm n v (v-1)).trans hh

def alternatingCycle (n : ℕ) : SimpleGraph (Fin (n+3)) where
  Adj u v := (cycleGraph (n+3)).Adj u v ∧ cycleIndex n u v%2=0
  symm:=⟨fun u v h => ⟨h.1.symm,by simpa only [cycleIndex_symm] using h.2⟩⟩
  loopless:=⟨fun v h => h.1.ne rfl⟩

instance (n : ℕ) : DecidableRel (alternatingCycle n).Adj:=fun u v =>
  inferInstanceAs (Decidable ((cycleGraph (n+3)).Adj u v ∧ cycleIndex n u v%2=0))

theorem alternatingCycle_le (n : ℕ) : alternatingCycle n≤cycleGraph (n+3) :=fun _ _ h => h.1

theorem alternatingCycle_neighborFinset (n : ℕ) (v : Fin (n+3)) :
    (alternatingCycle n).neighborFinset v=
      ((cycleGraph (n+3)).neighborFinset v).filter (fun w => cycleIndex n v w%2=0) := by
  ext w
  simp only [mem_neighborFinset,mem_filter]
  rfl

theorem alternatingCycle_degree_off_root (n : ℕ) (v : Fin (n+3)) (hv : v≠0) :
    (alternatingCycle n).degree v=1 := by
  have hc : ({v-1,v+1} : Finset (Fin (n+3))).card=2 := by
    have hh:=cycleGraph_degree_three_le (n:=n) (v:=v)
    rw [SimpleGraph.degree,cycleGraph_neighborFinset] at hh
    exact hh
  have hne : v-1≠v+1 := by
    intro he
    simp [he] at hc
  rw [←card_neighborFinset_eq_degree,alternatingCycle_neighborFinset,cycleGraph_neighborFinset,
    card_filter,sum_pair hne]
  simp only [cycleIndex_predecessor,cycleIndex_successor,Fin.coe_sub_one,if_neg hv]
  have hval : v.val≠0:=by intro he;exact hv (Fin.ext he)
  split_ifs <;> omega

/-- Both pieces are actual multigraphs with exact copy sum; the only
possible discrepancy is at the chosen root zero. -/
theorem cycleGraph_even_odd_split (n : ℕ) :
    ∃ A B : MultiGraph (Fin (n+3)),
      A.addCopies B=MultiGraph.ofSimpleGraph (cycleGraph (n+3)) ∧
      (∀ v,v≠0 → A.degree v=B.degree v) ∧
      A.degree 0≤B.degree 0+2 ∧ B.degree 0≤A.degree 0+2 := by
  let M:=MultiGraph.ofSimpleGraph (cycleGraph (n+3))
  let A:=MultiGraph.ofSimpleGraph (alternatingCycle n)
  let B:=M.subtractCopies A
  have hle : ∀ e,A.mult e≤M.mult e := by
    intro e
    induction e using Sym2.inductionOn with
    | hf u v =>
      change (if s(u,v)∈(alternatingCycle n).edgeSet then 1 else 0)≤
        (if s(u,v)∈(cycleGraph (n+3)).edgeSet then 1 else 0)
      simp only [mem_edgeSet]
      have hh : (alternatingCycle n).Adj u v → (cycleGraph (n+3)).Adj u v:=fun h => alternatingCycle_le n h
      split_ifs <;> tauto
  have hM : ∀ v,M.degree v=2 := by
    intro v
    rw [MultiGraph.degree_ofSimpleGraph]
    exact cycleGraph_degree_three_le
  have hsum : ∀ v,B.degree v+A.degree v=2 := by
    intro v
    have hh:=M.degree_subtract_add A hle v
    rw [hM v] at hh
    exact hh
  refine ⟨A,B,M.add_subtract_of_le A hle,?_,?_,?_⟩
  · intro v hv
    have ha : A.degree v=1 := by
      rw [MultiGraph.degree_ofSimpleGraph]
      exact alternatingCycle_degree_off_root n v hv
    have hh:=hsum v
    omega
  · have hh:=hsum 0;omega
  · have hh:=hsum 0;omega

end OverfullWork.DeterministicSplit
