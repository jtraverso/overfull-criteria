module

public import OverfullWork.IndependentSetIdentification
public import OverfullWork.OddCutDeficit

@[expose] public section


/-! # Exact internal counts away from an identified independent set

The image is simple away from its new centre. A subset avoiding that
centre has exactly the internal edges and cardinality of its retained
original vertices. Consequently original no-overfullness supplies all
away-from-centre bounds without any assumption on sets containing it.
-/
namespace OverfullWork.IndependentSetIdentification
open SimpleGraph Finset OddCutDeficit
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

/-- Exact multiplicity between two retained vertices. -/
theorem mult_some_some (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) (x y : Outside Y) :
    (graph G Y hind).mult s(some x,some y)=if G.Adj x.val y.val then 1 else 0 := by
  classical
  have hle : (graph G Y hind).mult s(some x,some y)≤1 :=
    isStarAt G Y hind (some x) (some y) (by simp) (by simp)
  change (EdgeImage.fibre G (vertexMap Y) s(some x,some y)).card≤1 at hle
  change (EdgeImage.fibre G (vertexMap Y) s(some x,some y)).card=_
  by_cases hxy : G.Adj x.val y.val
  · rw [if_pos hxy]
    have hp : 0<(EdgeImage.fibre G (vertexMap Y) s(some x,some y)).card := by
      apply card_pos.mpr
      refine ⟨⟨s(x.val,y.val),hxy⟩,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      simp only [Sym2.map_mk]
      rw [(map_eq_some Y x.val x).mpr rfl,(map_eq_some Y y.val y).mpr rfl]
    omega
  · rw [if_neg hxy]
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_notMem
    intro e he
    let p:=MultiGraph.GeneralCopies.endpoints e.val
    have hp : s(p.1,p.2)=e.val:=MultiGraph.GeneralCopies.endpoints_eq e.val
    have hadj : G.Adj p.1 p.2 := by
      apply (mem_edgeSet G).mp
      rw [hp]
      exact e.property
    have hm : s(vertexMap Y p.1,vertexMap Y p.2)=s(some x,some y) := by
      rw [←Sym2.map_mk,hp]
      exact (mem_filter.mp he).2
    rcases Sym2.eq_iff.mp hm with ⟨h1,h2⟩|⟨h1,h2⟩
    · have h1':=(map_eq_some Y p.1 x).mp h1
      have h2':=(map_eq_some Y p.2 y).mp h2
      exact hxy (by simpa only [h1',h2'] using hadj)
    · have h1':=(map_eq_some Y p.1 y).mp h1
      have h2':=(map_eq_some Y p.2 x).mp h2
      exact hxy (by simpa only [h1',h2'] using hadj.symm)

def outsideVertices (Y : Finset V) (S : Finset (Vertices Y)) : Finset (Outside Y) :=
  univ.filter fun x=>some x∈S

def oldVertices (Y : Finset V) (S : Finset (Vertices Y)) : Finset V :=
  (outsideVertices Y S).image Subtype.val

theorem image_outsideVertices (Y : Finset V) (S : Finset (Vertices Y)) (hnone : none∉S) :
    (outsideVertices Y S).image some=S := by
  ext x
  cases x <;> simp [outsideVertices,hnone]

theorem card_oldVertices (Y : Finset V) (S : Finset (Vertices Y)) (hnone : none∉S) :
    (oldVertices Y S).card=S.card := by
  have hc:=congrArg Finset.card (image_outsideVertices Y S hnone)
  rw [card_image_of_injective _ (Option.some_injective _)] at hc
  rw [oldVertices,card_image_of_injective _ Subtype.val_injective,hc]

/-- The double internal sum preserves every labelled old edge when the
selected image set avoids the merged centre. -/
theorem twiceInternal_away_centre (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V))
    (S : Finset (Vertices Y)) (hnone : none∉S) :
    (graph G Y hind).twiceInternal S=
      (MultiGraph.ofSimpleGraph G).twiceInternal (oldVertices Y S) := by
  conv_lhs => rw [←image_outsideVertices Y S hnone]
  rw [MultiGraph.twiceInternal,
    sum_image (fun a _ b _ h=>Option.some.inj h)]
  simp_rw [sum_image (fun a _ b _ h=>Option.some.inj h),mult_some_some]
  rw [oldVertices,MultiGraph.twiceInternal,sum_image (fun a _ b _ h=>Subtype.ext h)]
  simp_rw [sum_image (fun a _ b _ h=>Subtype.ext h)]
  simp only [MultiGraph.ofSimpleGraph,mem_edgeSet]

/-- Actual edges within an image set avoiding the centre are exactly
the original internal edges on its retained vertices. -/
theorem edgesWithin_away_centre (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V))
    (S : Finset (Vertices Y)) (hnone : none∉S) :
    (graph G Y hind).edgesWithin S=internalEdges G (oldVertices Y S) := by
  have hh:=twiceInternal_away_centre G Y hind S hnone
  rw [MultiGraph.twiceInternal_eq,MultiGraph.twiceInternal_eq,
    ←internalEdges_eq_multigraph] at hh
  omega

/-- No-overfullness is inherited by all image sets away from the centre.
No statement about sets containing the centre is included. -/
theorem no_overfull_away_centre (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) (hno : ¬G.HasOverfullSubgraph)
    (S : Finset (Vertices Y)) (hnone : none∉S) :
    (graph G Y hind).edgesWithin S≤G.maxDegree*(S.card/2) := by
  rw [edgesWithin_away_centre G Y hind S hnone,←card_oldVertices Y S hnone]
  by_contra hnot
  exact hno ⟨oldVertices Y S,Nat.lt_of_not_ge hnot⟩

/-- The odd-set form used in regular even-order star-multigraph tests. -/
theorem twiceInternal_bound_away_centre (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) (hno : ¬G.HasOverfullSubgraph)
    (S : Finset (Vertices Y)) (hodd : Odd S.card) (hnone : none∉S) :
    (graph G Y hind).twiceInternal S≤G.maxDegree*(S.card-1) := by
  have hb:=no_overfull_away_centre G Y hind hno S hnone
  rw [MultiGraph.twiceInternal_eq]
  obtain ⟨k,hk⟩:=hodd
  have hhalf : S.card/2=k := by omega
  have hsub : S.card-1=2*k := by omega
  rw [hhalf] at hb
  rw [hsub]
  nlinarith

end OverfullWork.IndependentSetIdentification
