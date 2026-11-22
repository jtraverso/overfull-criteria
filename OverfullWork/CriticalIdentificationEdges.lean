module

public import OverfullWork.IndependentIdentificationInternal
public import Overfull.Degree

@[expose] public section


/-! # Actual critical-edge inequalities after independent identification

The centre bundle is counted exactly from original neighbours. Criticality
then supplies both its balance and the degree-sum inequality on every
edge of the actual image; no multigraph-criticality is assumed.
-/
namespace OverfullWork.IndependentSetIdentification
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem centre_mult_eq_neighbour_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) (x : Outside Y) :
    (graph G Y hind).mult s(none,some x)=(Y.filter (G.Adj x.val)).card := by
  have hImage:=(graph G Y hind).degree_eq_sum_mult (some x)
  rw [degree_some,Fintype.sum_option] at hImage
  simp_rw [mult_some_some] at hImage
  have hOutside:(∑w : Outside Y,(if G.Adj x.val w.val then 1 else 0))=
      ∑w∈Yᶜ,(if G.Adj x.val w then 1 else 0):=
    (sum_subtype Yᶜ (fun v=>mem_compl) (fun w=>if G.Adj x.val w then 1 else 0)).symm
  rw [hOutside,Sym2.eq_swap] at hImage
  have hDegree:G.degree x.val=∑w : V,(if G.Adj x.val w then 1 else 0):=by
    rw [←MultiGraph.degree_ofSimpleGraph,MultiGraph.degree_eq_sum_mult]
    rfl
  have hSplit:=sum_add_sum_compl Y (fun w=>if G.Adj x.val w then (1:ℕ) else 0)
  have hCount:(Y.filter (G.Adj x.val)).card=∑w∈Y,(if G.Adj x.val w then 1 else 0):=card_filter _ _
  omega

theorem centre_bundle_balanced (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (Y : Finset V)
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
      have hh:=Overfull.deg_add hc hxy
      have hx:=G.degree_le_maxDegree x.val
      omega
    _ ≤ _ :=sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _=>Nat.zero_le _)

theorem centre_edge_degree_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (Y : Finset V)
    (hind : G.IsIndepSet (Y:Set V)) (x : Outside Y)
    (hEdge : 0<(graph G Y hind).mult s(none,some x)) :
    G.maxDegree+2≤(graph G Y hind).degree none+(graph G Y hind).degree (some x) := by
  rw [centre_mult_eq_neighbour_count] at hEdge
  obtain ⟨y,hy⟩:=card_pos.mp hEdge
  obtain ⟨hyY,hxy⟩:=mem_filter.mp hy
  have hh:=Overfull.deg_add hc hxy
  have hyDegree:G.degree y≤∑w∈Y,G.degree w:=
    single_le_sum (f:=fun w=>G.degree w) (fun _ _=>Nat.zero_le _) hyY
  rw [degree_none,degree_some]
  omega

theorem image_edge_degree_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (Y : Finset V)
    (hind : G.IsIndepSet (Y:Set V)) (a b : Vertices Y)
    (hEdge : 0<(graph G Y hind).mult s(a,b)) :
    G.maxDegree+2≤(graph G Y hind).degree a+(graph G Y hind).degree b := by
  cases a with
  | none =>
    cases b with
    | none => have hh:=(graph G Y hind).loopless s((none:Vertices Y),none) (by simp);omega
    | some b => exact centre_edge_degree_sum G hc Y hind b hEdge
  | some a =>
    cases b with
    | none =>
      have he:0<(graph G Y hind).mult s(none,some a):=by simpa only [Sym2.eq_swap] using hEdge
      have hh:=centre_edge_degree_sum G hc Y hind a he
      omega
    | some b =>
      rw [mult_some_some] at hEdge
      have hab:G.Adj a.val b.val:=by split_ifs at hEdge with h;exact h;omega
      rw [degree_some,degree_some]
      exact Overfull.deg_add hc hab

end OverfullWork.IndependentSetIdentification
