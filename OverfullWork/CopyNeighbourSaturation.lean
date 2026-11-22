module

public import OverfullWork.FournierCoreCriterion

@[expose] public section


/-! # Degree saturation of a graph copy -/
namespace SimpleGraph.Copy
open Finset
open scoped Classical
universe u v
variable {W : Type u} {V : Type v} [Fintype W] [Fintype V]
  [DecidableEq W] [DecidableEq V]
  {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]

/-- If a copy preserves the degree of a vertex, it covers all its ambient neighbours. -/
theorem exists_adj_preimage_of_degree_eq (f : Copy H G) (x : W)
    (hdeg : H.degree x = G.degree (f x)) {y : V} (hxy : G.Adj (f x) y) :
    ∃ z : W, H.Adj x z ∧ f z = y := by
  classical
  have hsurj : Function.Surjective (f.mapNeighborSet x) := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective (f.mapNeighborSet x)
      (f.mapNeighborSet x).injective hn
    simp only [card_neighborSet_eq_degree] at hlt
    omega
  obtain ⟨z, hz⟩ := hsurj ⟨y, hxy⟩
  exact ⟨z.val, z.property, congrArg Subtype.val hz⟩

/-- A maximum-degree vertex of a common-maximum-degree copy is saturated. -/
theorem exists_adj_preimage_of_maximum_degree (f : Copy H G)
    (hmax : H.maxDegree = G.maxDegree) (x : W) (hx : H.degree x = H.maxDegree)
    {y : V} (hxy : G.Adj (f x) y) : ∃ z : W, H.Adj x z ∧ f z = y := by
  have hdeg : H.degree x = G.degree (f x) := by
    have hlow := f.degree_le x
    have hupp := G.degree_le_maxDegree (f x)
    omega
  exact f.exists_adj_preimage_of_degree_eq x hdeg hxy

end SimpleGraph.Copy
