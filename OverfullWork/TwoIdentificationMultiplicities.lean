module

public import OverfullWork.TwoIndependentIdentifications

@[expose] public section


/-! Exact location and finite bounds for all parallel copies in the two-group image. -/
namespace OverfullWork.TwoIndependentIdentifications
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem mult_inr_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V)) (x y : Outside Z) :
    (graph G Z A hA hind).mult s(Sum.inr x,Sum.inr y) ≤ 1 := by
  change (EdgeImage.fibre G (vertexMap Z A) s(Sum.inr x,Sum.inr y)).card ≤ 1
  have h := EdgeImage.fibre_card_le G (vertexMap Z A) _ {s(x.val,y.val)} (by
    intro e he
    let p := MultiGraph.GeneralCopies.endpoints e.val
    have hp : s(p.1,p.2)=e.val := MultiGraph.GeneralCopies.endpoints_eq e.val
    have hm : s(vertexMap Z A p.1,vertexMap Z A p.2)=s(Sum.inr x,Sum.inr y) := by
      rw [←Sym2.map_mk,hp]
      exact (mem_filter.mp he).2
    rcases Sym2.eq_iff.mp hm with ⟨h1,h2⟩|⟨h1,h2⟩
    · have h1' := (map_eq_inr Z A p.1 x).mp h1
      have h2' := (map_eq_inr Z A p.2 y).mp h2
      exact mem_singleton.mpr (by rw [←hp,h1',h2'])
    · have h1' := (map_eq_inr Z A p.1 y).mp h1
      have h2' := (map_eq_inr Z A p.2 x).mp h2
      exact mem_singleton.mpr (by rw [←hp,h1',h2',Sym2.eq_swap]))
  simpa only [card_singleton] using h

theorem centre_mult_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V))
    (i : Bool) (x : Outside Z) :
    (graph G Z A hA hind).mult s(Sum.inl i,Sum.inr x) ≤ (part Z A i).card := by
  change (EdgeImage.fibre G (vertexMap Z A) s(Sum.inl i,Sum.inr x)).card ≤ _
  apply (EdgeImage.fibre_card_le G (vertexMap Z A) _
    ((part Z A i).image fun y => s(y,x.val)) ?_).trans card_image_le
  intro e he
  let p := MultiGraph.GeneralCopies.endpoints e.val
  have hp : s(p.1,p.2)=e.val := MultiGraph.GeneralCopies.endpoints_eq e.val
  have hm : s(vertexMap Z A p.1,vertexMap Z A p.2)=s(Sum.inl i,Sum.inr x) := by
    rw [←Sym2.map_mk,hp]
    exact (mem_filter.mp he).2
  rcases Sym2.eq_iff.mp hm with ⟨h1,h2⟩|⟨h1,h2⟩
  · have h1' := (map_eq_inl Z A hA p.1 i).mp h1
    have h2' := (map_eq_inr Z A p.2 x).mp h2
    exact mem_image.mpr ⟨p.1,h1',by rw [←hp,h2']⟩
  · have h1' := (map_eq_inr Z A p.1 x).mp h1
    have h2' := (map_eq_inl Z A hA p.2 i).mp h2
    exact mem_image.mpr ⟨p.2,h2',by rw [←hp,h1',Sym2.eq_swap]⟩

theorem mult_centres (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V)) (i j : Bool) :
    (graph G Z A hA hind).mult s(Sum.inl i,Sum.inl j)=0 := by
  change (EdgeImage.fibre G (vertexMap Z A) s(Sum.inl i,Sum.inl j)).card=0
  apply card_eq_zero.mpr
  apply eq_empty_of_forall_notMem
  intro e he
  let p := MultiGraph.GeneralCopies.endpoints e.val
  have hp : s(p.1,p.2)=e.val := MultiGraph.GeneralCopies.endpoints_eq e.val
  have hadj : G.Adj p.1 p.2 := by
    apply (mem_edgeSet G).mp
    rw [hp]
    exact e.property
  have hm : s(vertexMap Z A p.1,vertexMap Z A p.2)=s(Sum.inl i,Sum.inl j) := by
    rw [←Sym2.map_mk,hp]
    exact (mem_filter.mp he).2
  rcases Sym2.eq_iff.mp hm with ⟨h1,h2⟩|⟨h1,h2⟩
  · exact hind (part_subset Z A hA i ((map_eq_inl Z A hA p.1 i).mp h1))
      (part_subset Z A hA j ((map_eq_inl Z A hA p.2 j).mp h2)) hadj.ne hadj
  · exact hind (part_subset Z A hA j ((map_eq_inl Z A hA p.1 j).mp h1))
      (part_subset Z A hA i ((map_eq_inl Z A hA p.2 i).mp h2)) hadj.ne hadj

end OverfullWork.TwoIndependentIdentifications
