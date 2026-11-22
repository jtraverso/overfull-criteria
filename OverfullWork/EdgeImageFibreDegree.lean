module

public import OverfullWork.IndependentSetIdentification

@[expose] public section


/-! Exact degree sums for any loopless image with a specified vertex fibre. -/
namespace OverfullWork.EdgeImage
open SimpleGraph Finset
open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
set_option maxHeartbeats 5000000

theorem degree_of_fibre (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → W)
    (hloop : ∀ u v, G.Adj u v → f u ≠ f v) (w : W) (Y : Finset V)
    (hFibre : ∀ a, f a=w ↔ a ∈ Y) :
    (graph G f hloop).degree w=∑ a ∈ Y, G.degree a := by
  rw [degree_eq]
  have heq : (univ.filter fun e:G.edgeSet => w ∈ Sym2.map f e.val)=
      Y.biUnion (fun y => univ.filter fun e:G.edgeSet => y ∈ e.val) := by
    ext e
    simp only [mem_filter,mem_univ,true_and,mem_biUnion,Sym2.mem_map,hFibre]
    exact ⟨fun ⟨y,hy,hyY⟩ => ⟨y,hyY,hy⟩,fun ⟨y,hyY,hy⟩ => ⟨y,hy,hyY⟩⟩
  have hdis : (↑Y:Set V).PairwiseDisjoint
      (fun y => univ.filter fun e:G.edgeSet => y ∈ e.val) := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro e hey hez
    have hay : e.val ∈ G.incidenceSet y := ⟨e.property,(mem_filter.mp hey).2⟩
    have haz : e.val ∈ G.incidenceSet z := ⟨e.property,(mem_filter.mp hez).2⟩
    have hadj := G.adj_of_mem_incidenceSet hyz hay haz
    exact hloop y z hadj (((hFibre y).mpr hy).trans ((hFibre z).mpr hz).symm)
  rw [heq,card_biUnion hdis]
  exact sum_congr rfl (fun y _ => PairIdentification.source_incidence_card G y)

theorem fibre_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → W) (e : Sym2 W) (A : Finset (Sym2 V))
    (hA : ∀ a ∈ fibre G f e, a.val ∈ A) : (fibre G f e).card ≤ A.card := by
  have hsub : (fibre G f e).image Subtype.val ⊆ A := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    exact hA a ha
  have hh := card_le_card hsub
  rwa [card_image_of_injective _ Subtype.val_injective] at hh

end OverfullWork.EdgeImage
