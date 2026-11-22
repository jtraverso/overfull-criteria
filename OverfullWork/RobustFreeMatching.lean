module

public import OverfullWork.RobustBipartiteHall
public import OverfullWork.GeneralFreeColourMatching
public import OverfullWork.CrossingSupport

@[expose] public section


/-! # Actual available crossing matching after the anchor prescriptions

Apply the robust Hall argument to the surviving opposite-side vertices.
The matching uses available edge copies of the current partial coloring,
and its degree and crossing properties are proved for that same graph.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.BipartiteRobustMargin OverfullWork.PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 24000000

theorem exists_robust_free_matching (P : M.PartialColouring k) (A U B : Finset V) (r cutoff : ℕ)
    (hRobust : IsBipartiteRobustAt M.supportGraph A r cutoff) (hU : U ⊆ A) (hB : B ⊆ Aᶜ)
    (hEqual : U.card=B.card) (hVertexLoss : (Aᶜ\B).card ≤ r)
    (hEdgeLoss : ∀ v ∈ B, (P.graph.crossingSupport A).degree v < r)
    (hMinLeft : ∀ x ∈ U, cutoff ≤ neighboursIn (M.supportGraph\P.graph.crossingSupport A) B x)
    (hMinRight : ∀ y ∈ B, cutoff ≤ neighboursIn (M.supportGraph\P.graph.crossingSupport A) U y) :
    ∃ J : MultiGraph V, (∀ e, J.mult e ≤ P.available.mult e) ∧
      (∀ v, J.degree v=if v ∈ U ∨ v ∈ B then 1 else 0) ∧
      ∀ x y, (x ∈ A ↔ y ∈ A) → J.mult s(x,y)=0 := by
  obtain ⟨f,hf⟩ := OverfullWork.RobustBipartiteHall.exists_matching_after_deletions M.supportGraph
    (P.graph.crossingSupport A) A U B r cutoff hRobust hU hB hEqual hVertexLoss hEdgeLoss hMinLeft hMinRight
  have hDis : Disjoint U B := Finset.disjoint_left.mpr (fun _ hu hb => (mem_compl.mp (hB hb)) (hU hu))
  have hAvailable : ∀ x : ↥U, 0 < P.available.mult s(x.val,(f x).val) := by
    intro x
    have hxA := hU x.property
    have hyA := mem_compl.mp (hB (f x).property)
    exact P.available_crossing_of_support_sdiff A x (f x) (by tauto) (hf x)
  refine ⟨pairingMatching U B hDis f,pairingMatching_le U B hDis f P.available hAvailable,?_,?_⟩
  · intro v
    rw [pairingMatching_degree]
  · intro x y hSame
    change (if s(x,y) ∈ (pairingGraph U B hDis f).edgeSet then 1 else 0)=0
    apply if_neg
    rw [SimpleGraph.mem_edgeSet]
    intro hAdj
    rcases hAdj with ⟨z,rfl,rfl⟩|⟨z,rfl,rfl⟩
    · exact (mem_compl.mp (hB (f z).property)) (hSame.mp (hU z.property))
    · exact (mem_compl.mp (hB (f z).property)) (hSame.mpr (hU z.property))

end SimpleGraph.MultiGraph.PartialColouring
