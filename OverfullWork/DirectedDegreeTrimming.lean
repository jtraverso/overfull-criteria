module

public import OverfullWork.DirectedArcSelection

@[expose] public section


/-! Extract an actual exceptional set from a global deleted-arc budget.
Both incoming and outgoing losses are controlled outside the set. -/
namespace OverfullWork.DirectedDegreeTrimming
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 18000000

noncomputable def total (D : Digraph V) : ℕ := ∑ v,inDegree D v

theorem total_eq_out (D : Digraph V) : total D=∑ v,outDegree D v := by
  simp only [total,inDegree,inNeighbours,outDegree,card_filter]
  exact sum_comm

noncomputable def badIn (D : Digraph V) (L : ℕ) : Finset V :=
  univ.filter fun v => L < inDegree D v
noncomputable def badOut (D : Digraph V) (L : ℕ) : Finset V :=
  univ.filter fun v => L < outDegree D v
noncomputable def bad (D : Digraph V) (L : ℕ) : Finset V := badIn D L ∪ badOut D L

theorem badIn_budget (D : Digraph V) (L : ℕ) : (badIn D L).card*(L+1) ≤ total D := by
  calc
    _ = ∑ _v ∈ badIn D L,(L+1) := by simp
    _ ≤ ∑ v ∈ badIn D L,inDegree D v := by
      apply sum_le_sum
      intro v hv
      have hh := (mem_filter.mp hv).2
      omega
    _ ≤ ∑ v,inDegree D v := sum_le_sum_of_subset (subset_univ _)

theorem badOut_budget (D : Digraph V) (L : ℕ) : (badOut D L).card*(L+1) ≤ total D := by
  rw [total_eq_out]
  calc
    _ = ∑ _v ∈ badOut D L,(L+1) := by simp
    _ ≤ ∑ v ∈ badOut D L,outDegree D v := by
      apply sum_le_sum
      intro v hv
      have hh := (mem_filter.mp hv).2
      omega
    _ ≤ ∑ v,outDegree D v := sum_le_sum_of_subset (subset_univ _)

theorem bad_budget (D : Digraph V) (L : ℕ) : (bad D L).card*(L+1) ≤ 2*total D := by
  have hUnion := card_union_le (badIn D L) (badOut D L)
  have hMul := Nat.mul_le_mul_right (L+1) hUnion
  have hIn := badIn_budget D L
  have hOut := badOut_budget D L
  change (bad D L).card*(L+1) ≤ _ at hMul
  nlinarith only [hMul,hIn,hOut]

theorem loss_outside_bad (D : Digraph V) (L : ℕ) (v : V) (hv : v ∉ bad D L) :
    inDegree D v ≤ L ∧ outDegree D v ≤ L := by
  have hIn : ¬L < inDegree D v := fun hh => hv (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hh⟩))
  have hOut : ¬L < outDegree D v := fun hh => hv (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hh⟩))
  omega

theorem exists_exceptional_loss_set (D H : Digraph V) (L B : ℕ)
    (hTotal : total (D\H) ≤ B) :
    ∃ X : Finset V,X.card*(L+1) ≤ 2*B ∧
      ∀ v,v ∉ X → inDegree (D\H) v ≤ L ∧ outDegree (D\H) v ≤ L := by
  refine ⟨bad (D\H) L,?_,loss_outside_bad (D\H) L⟩
  exact (bad_budget (D\H) L).trans (Nat.mul_le_mul_left 2 hTotal)

end OverfullWork.DirectedDegreeTrimming
