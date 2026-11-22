module

public import OverfullWork.CMSRegularizationTwoCentres
public import OverfullWork.TwoIdentificationMultiplicities

@[expose] public section


/-! Retain the full source degree-sum bound for every copy of an
edge incident with either identified vertex. -/
namespace OverfullWork.TwoIndependentIdentifications

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem centre_bundle_weighted_of_weak_val (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V))
    (hWeak : ∀ u ∈ Z, ∀ v, G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v)
    (i : Bool) (x : Outside Z) :
    (G.maxDegree-(graph G Z A hA hind).degree (Sum.inr x)+2)*
        (graph G Z A hA hind).mult s(Sum.inl i,Sum.inr x) ≤
        (graph G Z A hA hind).degree (Sum.inl i) := by
  rw [degree_inr,degree_inl]
  let Y := (part Z A i).filter (G.Adj x.val)
  let f := G.maxDegree-G.degree x.val+2
  have hMult : (graph G Z A hA hind).mult s(Sum.inl i,Sum.inr x) ≤ Y.card := by
    change (EdgeImage.fibre G (vertexMap Z A) s(Sum.inl i,Sum.inr x)).card ≤ _
    apply (EdgeImage.fibre_card_le G (vertexMap Z A) _
      (Y.image fun y => s(y,x.val)) ?_).trans card_image_le
    intro e he
    let p := MultiGraph.GeneralCopies.endpoints e.val
    have hp : s(p.1,p.2)=e.val := MultiGraph.GeneralCopies.endpoints_eq e.val
    have hm : s(vertexMap Z A p.1,vertexMap Z A p.2)=s(Sum.inl i,Sum.inr x) := by
      rw [←Sym2.map_mk,hp]
      exact (mem_filter.mp he).2
    have hAdj : G.Adj p.1 p.2 := (G.mem_edgeSet).mp (hp ▸ e.property)
    rcases Sym2.eq_iff.mp hm with ⟨h1,h2⟩|⟨h1,h2⟩
    · have hy := (map_eq_inl Z A hA p.1 i).mp h1
      have hx := (map_eq_inr Z A p.2 x).mp h2
      have hY : p.1 ∈ Y := mem_filter.mpr ⟨hy,hx ▸ hAdj.symm⟩
      exact mem_image.mpr ⟨p.1,hY,by rw [←hp,hx]⟩
    · have hx := (map_eq_inr Z A p.1 x).mp h1
      have hy := (map_eq_inl Z A hA p.2 i).mp h2
      have hY : p.2 ∈ Y := mem_filter.mpr ⟨hy,hx ▸ hAdj⟩
      exact mem_image.mpr ⟨p.2,hY,by rw [←hp,hx,Sym2.eq_swap]⟩
  calc
    _ ≤ f*Y.card := Nat.mul_le_mul_left f hMult
    _ = ∑ y ∈ Y, f := by rw [sum_const,nsmul_eq_mul]; exact Nat.mul_comm _ _
    _ ≤ ∑ y ∈ Y, G.degree y := by
      apply sum_le_sum
      intro y hy
      obtain ⟨hyPart,hxy⟩ := mem_filter.mp hy
      have hSum := hWeak y (part_subset Z A hA i hyPart) x.val hxy.symm
      have hD := G.degree_le_maxDegree x.val
      change G.maxDegree-G.degree x.val+2 ≤ G.degree y
      omega
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

end OverfullWork.TwoIndependentIdentifications
