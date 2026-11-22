module

public import OverfullWork.CleanedSourceVAL
public import OverfullWork.CriticalCanonicalTripleWitness

@[expose] public section


/-! The degree-sum form of weak VAL suffices for the image inequalities.
No criticality is asserted for the source or its identification. -/
namespace OverfullWork.IndependentSetIdentification
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

theorem centre_bundle_balanced_of_weak_val (G : SimpleGraph V) [DecidableRel G.Adj]
    (hWeak : ∀ u v, G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) (Y : Finset V)
    (hind : G.IsIndepSet (Y:Set V)) (x : Outside Y) :
    2*(graph G Y hind).mult s(none,some x)≤(graph G Y hind).degree none := by
  rw [centre_mult_eq_neighbour_count,degree_none]
  let T:=Y.filter (G.Adj x.val)
  calc
    _ = ∑_y∈T,2 :=by simp [T,Nat.mul_comm]
    _ ≤ ∑y∈T,G.degree y :=by
      apply sum_le_sum
      intro y hy
      have hxy: G.Adj x.val y:=(mem_filter.mp hy).2
      have hh:=hWeak x.val y hxy
      have hx:=G.degree_le_maxDegree x.val
      omega
    _ ≤ _ :=sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _=>Nat.zero_le _)

theorem centre_edge_degree_sum_of_weak_val (G : SimpleGraph V) [DecidableRel G.Adj]
    (hWeak : ∀ u v, G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) (Y : Finset V)
    (hind : G.IsIndepSet (Y:Set V)) (x : Outside Y)
    (hEdge : 0<(graph G Y hind).mult s(none,some x)) :
    G.maxDegree+2≤(graph G Y hind).degree none+(graph G Y hind).degree (some x) := by
  rw [centre_mult_eq_neighbour_count] at hEdge
  obtain ⟨y,hy⟩:=card_pos.mp hEdge
  obtain ⟨hyY,hxy⟩:=mem_filter.mp hy
  have hh:=hWeak x.val y hxy
  have hyDegree:G.degree y≤∑w∈Y,G.degree w:=
    single_le_sum (f:=fun w=>G.degree w) (fun _ _=>Nat.zero_le _) hyY
  rw [degree_none,degree_some]
  omega

theorem image_edge_degree_sum_of_weak_val (G : SimpleGraph V) [DecidableRel G.Adj]
    (hWeak : ∀ u v, G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) (Y : Finset V)
    (hind : G.IsIndepSet (Y:Set V)) (a b : Vertices Y)
    (hEdge : 0<(graph G Y hind).mult s(a,b)) :
    G.maxDegree+2≤(graph G Y hind).degree a+(graph G Y hind).degree b := by
  cases a with
  | none =>
    cases b with
    | none => have hh:=(graph G Y hind).loopless s((none:Vertices Y),none) (by simp);omega
    | some b => exact centre_edge_degree_sum_of_weak_val G hWeak Y hind b hEdge
  | some a =>
    cases b with
    | none =>
      have he:0<(graph G Y hind).mult s(none,some a):=by simpa only [Sym2.eq_swap] using hEdge
      have hh:=centre_edge_degree_sum_of_weak_val G hWeak Y hind a he
      omega
    | some b =>
      rw [mult_some_some] at hEdge
      have hab:G.Adj a.val b.val:=by split_ifs at hEdge with h;exact h;omega
      rw [degree_some,degree_some]
      exact hWeak a.val b.val hab

end OverfullWork.IndependentSetIdentification
