module

public import OverfullWork.DirectedRobustExpansion

@[expose] public section


/-! Deterministic accounting for GGKLO Lemma 7.3(i).
The saturated set is paid by double counting short-path visits.
Equation (7.2) adds endpoint, short interior, and assigned-block costs
before applying robust expansion to the actual unused reserve. -/
namespace OverfullWork.DirectedReserveUsage

open Finset DirectedRobustExpansion
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

noncomputable def visits (A : I → Finset V) (v : V) : ℕ :=
  ((univ : Finset I).filter (fun i => v ∈ A i)).card

/-- Vertices at the short-path visit cap occupy at most the total
number of short-path visits divided by the cap. -/
theorem saturated_vertices_cost (A : I → Finset V) (cap : ℕ) :
    cap*((univ : Finset V).filter (fun v => cap ≤ visits A v)).card ≤ ∑ i, (A i).card := by
  let S := (univ : Finset V).filter (fun v => cap ≤ visits A v)
  have hLocal : ∀ v ∈ S, cap ≤ visits A v := fun _ hv => (mem_filter.mp hv).2
  have hSum : (∑ v : V, visits A v) = ∑ i, (A i).card := by
    simp only [visits, card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← card_filter, filter_mem_eq_inter, univ_inter]
  change cap*S.card ≤ _
  calc
    _ = ∑ _v ∈ S, cap := by simp [mul_comm]
    _ ≤ ∑ v ∈ S, visits A v := sum_le_sum hLocal
    _ ≤ ∑ v : V, visits A v := sum_le_sum_of_subset (subset_univ _)
    _ = _ := hSum

private theorem degree_of_union_le_sum (H : I → Digraph V) (v : V) :
    inDegree (⨆ i, H i) v + outDegree (⨆ i, H i) v ≤
      ∑ i, (inDegree (H i) v + outDegree (H i) v) := by
  let N := fun i => (univ : Finset V).filter (fun u => (H i).Adj u v)
  let P := fun i => (univ : Finset V).filter (fun u => (H i).Adj v u)
  have hN : (univ : Finset V).filter (fun u => (⨆ i, H i).Adj u v) = univ.biUnion N := by
    ext u
    simp [N, Digraph.iSup_adj]
  have hP : (univ : Finset V).filter (fun u => (⨆ i, H i).Adj v u) = univ.biUnion P := by
    ext u
    simp [P, Digraph.iSup_adj]
  have hn : inDegree (⨆ i, H i) v ≤ ∑ i, inDegree (H i) v := by
    unfold inDegree inNeighbours
    rw [hN]
    exact card_biUnion_le
  have hp : outDegree (⨆ i, H i) v ≤ ∑ i, outDegree (H i) v := by
    unfold outDegree
    rw [hP]
    exact card_biUnion_le
  rw [sum_add_distrib]
  exact Nat.add_le_add hn hp

/-- The per-vertex reserve payment of equation (7.2), with independent
budgets for the endpoints, short-path interiors and assigned blocks. -/
theorem reserve_arc_cost (H : I → Digraph V) (interior block : I → Finset V)
    (endpoint : I → V → ℕ) (b s l : ℕ)
    (hEndpoint : ∀ v, (∑ i, endpoint i v) ≤ b)
    (hInterior : ∀ v, visits interior v ≤ s)
    (hBlock : ∀ v, visits block v ≤ l)
    (hCost : ∀ i v, inDegree (H i) v + outDegree (H i) v ≤ endpoint i v +
      (if v ∈ interior i then 2 else 0) + (if v ∈ block i then 2 else 0)) :
    ∀ v, inDegree (⨆ i, H i) v + outDegree (⨆ i, H i) v ≤ b+2*s+2*l := by
  intro v
  have hCount (A : I → Finset V) : (∑ i, if v ∈ A i then 2 else 0) = 2*visits A v := by
    rw [← sum_filter]
    simp [visits, Nat.mul_comm]
  calc
    _ ≤ ∑ i, (inDegree (H i) v + outDegree (H i) v) := degree_of_union_le_sum H v
    _ ≤ ∑ i, (endpoint i v + (if v ∈ interior i then 2 else 0) +
        (if v ∈ block i then 2 else 0)) := sum_le_sum (fun i _ => hCost i v)
    _ = (∑ i, endpoint i v)+2*visits interior v+2*visits block v := by
      rw [sum_add_distrib, sum_add_distrib, hCount, hCount]
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (hEndpoint v)
      (Nat.mul_le_mul_left 2 (hInterior v))) (Nat.mul_le_mul_left 2 (hBlock v))

/-- Deleting used arcs of bounded indegree retains robust expansion.
The same estimate also applies when the combined directed degree is
bounded by the deletion budget. -/
theorem robust_after_reserve_use (Γ U : Digraph V) (r t d : ℕ)
    (hR : IsRobustAt Γ r t) (hU : ∀ v, inDegree U v ≤ d) :
    IsRobustAt (Γ \ U) (r-d) t := by
  intro S hLo hHi
  have hSub : neighbourhood Γ r S ⊆ neighbourhood (Γ \ U) (r-d) S := by
    intro v hv
    have hCount := (mem_filter.mp hv).2
    let A := S.filter (fun u => Γ.Adj u v)
    let B := univ.filter (fun u => U.Adj u v)
    let C := @Finset.filter V (fun u => (Γ \ U).Adj u v) (fun _ => Classical.propDecidable _) S
    have hEq : A \ B = C := by
      ext u
      simp only [A,B,C,mem_sdiff,mem_filter,mem_univ,true_and,Digraph.sdiff_adj]
      tauto
    have hDiff := card_le_card_sdiff_add_card (s := A) (t := B)
    rw [hEq] at hDiff
    change inNeighbours Γ S v ≤ inNeighbours (Γ \ U) S v+inDegree U v at hDiff
    exact mem_filter.mpr ⟨mem_univ _,by have := hU v; omega⟩
  have hGrow := (hR S hLo hHi).trans (card_le_card hSub)
  exact (Nat.add_le_add_left (Nat.sub_le _ _) _).trans hGrow

end OverfullWork.DirectedReserveUsage
