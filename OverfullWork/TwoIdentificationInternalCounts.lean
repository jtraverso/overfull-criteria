module

public import OverfullWork.TwoCentreOrdinaryCore
public import OverfullWork.OddCutDeficit

@[expose] public section


/-! The ordinary induced graph of the actual two-group image preserves
the original edges, their counts, and their no-overfull bounds. -/
namespace OverfullWork.TwoIndependentIdentifications
open SimpleGraph Finset OddCutDeficit TwoCentreOrdinaryCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

theorem mult_inr_inr (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V)) (x y : Outside Z) :
    (graph G Z A hA hind).mult s(Sum.inr x,Sum.inr y)=if G.Adj x.val y.val then 1 else 0 := by
  have hle := mult_inr_le G Z A hA hind x y
  change (EdgeImage.fibre G (vertexMap Z A) s(Sum.inr x,Sum.inr y)).card ≤ 1 at hle
  change (EdgeImage.fibre G (vertexMap Z A) s(Sum.inr x,Sum.inr y)).card=_
  by_cases hxy : G.Adj x.val y.val
  · rw [if_pos hxy]
    have hp : 0 < (EdgeImage.fibre G (vertexMap Z A) s(Sum.inr x,Sum.inr y)).card := by
      apply card_pos.mpr
      refine ⟨⟨s(x.val,y.val),hxy⟩,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      simp only [Sym2.map_mk]
      rw [(map_eq_inr Z A x.val x).mpr rfl,(map_eq_inr Z A y.val y).mpr rfl]
    omega
  · rw [if_neg hxy]
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_notMem
    intro e he
    let p := MultiGraph.GeneralCopies.endpoints e.val
    have hp : s(p.1,p.2)=e.val := MultiGraph.GeneralCopies.endpoints_eq e.val
    have hadj : G.Adj p.1 p.2 := by
      apply (mem_edgeSet G).mp
      rw [hp]
      exact e.property
    have hm : s(vertexMap Z A p.1,vertexMap Z A p.2)=s(Sum.inr x,Sum.inr y) := by
      rw [←Sym2.map_mk,hp]
      exact (mem_filter.mp he).2
    rcases Sym2.eq_iff.mp hm with ⟨h1,h2⟩|⟨h1,h2⟩
    · have h1' := (map_eq_inr Z A p.1 x).mp h1
      have h2' := (map_eq_inr Z A p.2 y).mp h2
      exact hxy (by simpa only [h1',h2'] using hadj)
    · have h1' := (map_eq_inr Z A p.1 y).mp h1
      have h2' := (map_eq_inr Z A p.2 x).mp h2
      exact hxy (by simpa only [h1',h2'] using hadj.symm)

theorem ordinary_degree_loss (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V)) (x : Outside Z) :
    G.degree x.val ≤ (ordinary (graph G Z A hA hind)).degree x+Z.card := by
  have hRow := (graph G Z A hA hind).degree_eq_sum_mult (Sum.inr x)
  rw [Fintype.sum_sum_type,Fintype.sum_bool,degree_inr] at hRow
  have hA' := centre_mult_le G Z A hA hind false x
  have hB' := centre_mult_le G Z A hA hind true x
  have hCard := card_sdiff_add_card_eq_card hA
  have hSwapA : (graph G Z A hA hind).mult s(Sum.inr x,Sum.inl false)=
      (graph G Z A hA hind).mult s(Sum.inl false,Sum.inr x) := congrArg _ Sym2.eq_swap
  have hSwapB : (graph G Z A hA hind).mult s(Sum.inr x,Sum.inl true)=
      (graph G Z A hA hind).mult s(Sum.inl true,Sum.inr x) := congrArg _ Sym2.eq_swap
  have hOrd : (∑ w : Outside Z, (graph G Z A hA hind).mult s(Sum.inr x,Sum.inr w))=
      (ordinary (graph G Z A hA hind)).degree x := by
    rw [MultiGraph.degree_eq_sum_mult]
    rfl
  simp only [part,Bool.false_eq_true,if_true,if_false] at hA' hB'
  rw [hOrd,hSwapA,hSwapB] at hRow
  omega

theorem twiceInternal_ordinary (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V)) (T : Finset (Outside Z)) :
    (ordinary (graph G Z A hA hind)).twiceInternal T=
      (MultiGraph.ofSimpleGraph G).twiceInternal (T.image Subtype.val) := by
  rw [MultiGraph.twiceInternal,MultiGraph.twiceInternal,
    sum_image (fun _ _ _ _ h => Subtype.ext h)]
  simp_rw [sum_image (fun _ _ _ _ h => Subtype.ext h),ordinary_mult,mult_inr_inr]
  rfl

theorem no_overfull_ordinary (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hind : G.IsIndepSet (Z:Set V))
    (hNo : ¬G.HasOverfullSubgraph) (T : Finset (Outside Z)) (hOdd : Odd T.card) :
    (ordinary (graph G Z A hA hind)).twiceInternal T ≤ G.maxDegree*(T.card-1) := by
  have hCard : (T.image Subtype.val).card=T.card := card_image_of_injective _ Subtype.val_injective
  have hBound : internalEdges G (T.image Subtype.val) ≤ G.maxDegree*((T.image Subtype.val).card/2) := by
    by_contra h
    exact hNo ⟨T.image Subtype.val,Nat.lt_of_not_ge h⟩
  rw [twiceInternal_ordinary,MultiGraph.twiceInternal_eq,←internalEdges_eq_multigraph]
  obtain ⟨k,hk⟩ := hOdd
  rw [hCard] at hBound
  have hHalf : T.card/2=k := by omega
  have hMinus : T.card-1=2*k := by omega
  rw [hHalf] at hBound
  rw [hMinus]
  nlinarith only [hBound]

end OverfullWork.TwoIndependentIdentifications
