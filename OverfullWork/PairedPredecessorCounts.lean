module

public import OverfullWork.ColourLayeredPaths

@[expose] public section


/-! # Convert robust-neighbor counts into actual free predecessors

The matching permutation is injective, so distinct neighbor choices
give distinct preceding matching pairs. The surviving support edges
are proved to be available crossing copies of the ambient multigraph.
-/
namespace SimpleGraph.MultiGraph
open SimpleGraph Finset OverfullWork.PrunedCore OverfullWork.RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

theorem crossingSupport_compl (M : MultiGraph V) (A : Finset V) :
    M.crossingSupport Aᶜ=M.crossingSupport A := by
  ext x y
  change (0 < M.mult s(x,y) ∧ ¬(x ∈ Aᶜ ↔ y ∈ Aᶜ)) ↔
    (0 < M.mult s(x,y) ∧ ¬(x ∈ A ↔ y ∈ A))
  simp only [mem_compl]
  tauto

theorem PartialColouring.free_predecessor_count {M : MultiGraph V} {k : ℕ}
    (P : M.PartialColouring k) (A X : Finset V) (τ : Equiv.Perm V)
    (hMateSide : ∀ x ∈ X, τ x ∈ A) (z : V) (hz : z ∉ A) :
    neighboursIn (M.supportGraph\P.graph.crossingSupport A) (X.image τ) z ≤
      (X.filter (fun x => (P.available.crossingSupport A).Adj (τ x) z)).card := by
  rw [neighboursIn_eq_filter_card]
  let N := (X.image τ).filter (fun y => (M.supportGraph\P.graph.crossingSupport A).Adj z y)
  let D := X.filter (fun x => (P.available.crossingSupport A).Adj (τ x) z)
  have hs : N ⊆ D.image τ := by
    intro y hy
    obtain ⟨hyX,hyEdge⟩ := mem_filter.mp hy
    obtain ⟨x,hx,he⟩ := mem_image.mp hyX
    subst y
    have hxA := hMateSide x hx
    have hCross : ¬(z ∈ A ↔ τ x ∈ A) := by tauto
    have hav := P.available_crossing_of_support_sdiff A z (τ x) hCross hyEdge
    have hFree : (P.available.crossingSupport A).Adj (τ x) z := by
      constructor
      · rw [Sym2.eq_swap];exact hav
      · change ¬(τ x ∈ A ↔ z ∈ A)
        tauto
    exact mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,hFree⟩,rfl⟩
  have hh := card_le_card hs
  rw [card_image_of_injective _ τ.injective] at hh
  exact hh

end SimpleGraph.MultiGraph
