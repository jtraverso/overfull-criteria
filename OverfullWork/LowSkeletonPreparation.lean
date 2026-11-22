module

public import OverfullWork.PaperLowSkeleton
public import OverfullWork.CriticalLowPartnerProjection

@[expose] public section


/-! # Actual low skeleton and its core representatives

This joins the paper's sparse skeleton with the proved G1-to-projection
bridge. The additional forbidden set is the entire skeleton support;
new representative vertices therefore do not collide with its interior.
The final spanning-layer realization and its iteration remain separate.
-/
namespace OverfullWork.LowSkeletonPreparation
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open scoped Classical
universe u
set_option maxHeartbeats 3000000

noncomputable def nonisolatedVertices {V : Type u} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : Finset V :=
  univ.filter fun v => 0<H.degree v

/-- The actual support has at most twice as many vertices as edges. -/
theorem nonisolatedVertices_card_le_twice_edges {V : Type u} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (nonisolatedVertices H).card≤2*H.edgeFinset.card := by
  classical
  calc
    _ = ∑_v∈nonisolatedVertices H,1 := by simp
    _ ≤ ∑v∈nonisolatedVertices H,H.degree v := sum_le_sum (fun v hv => by
      have hh:=(mem_filter.mp hv).2
      omega)
    _ ≤ ∑v,H.degree v := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun _ _ _ => Nat.zero_le _)
    _ = _ := H.sum_degrees_eq_twice_card_edges

/-- The low skeleton and its injective representative map, including
an actual matching, are both constructed uniformly from criticality.
No skeleton, endpoint selection or projection is an input. -/
theorem above_half_low_skeleton_preparation (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        let U:=exceptions G G.maxDegree (Fintype.card V/(8*q))
        2≤(lowVertices G).card →
        ∃H : SimpleGraph V,
          PaperLowSkeleton.IsSkeleton G H (lowVertices G) ∧
          (∀v∉lowVertices G,H.degree v≤1) ∧
          Nonempty (LowSkeletonProjection.Projection G
            (PaperLowSkeleton.outerLeaves H (lowVertices G)) U (nonisolatedVertices H)) := by
  obtain ⟨q,hq,N,hproj⟩:=CriticalLowPartnerProjection.above_half_low_partner_projection_avoiding.{u} ε hε
  refine ⟨q,hq,N,?_⟩
  intro V _ _ G _ hn hc hdense
  dsimp only
  intro hsize
  obtain ⟨H,hs,hout⟩:=PaperLowSkeleton.exists_low_skeleton_fresh G hc hsize
  refine ⟨H,hs,hout,?_⟩
  have hZ : (nonisolatedVertices H).card≤2*((lowVertices G).card+1) :=
    (nonisolatedVertices_card_le_twice_edges H).trans (Nat.mul_le_mul_left 2 hs.edge_bound)
  exact hproj G hn hc hdense _ _ hs.outer_card_le hZ (fun x hx => hs.outer_neighbour hx)

end OverfullWork.LowSkeletonPreparation
