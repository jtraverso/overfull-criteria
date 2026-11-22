module

public import OverfullWork.TwoColourTrimming

@[expose] public section


/-! # Exact degrees of an attached spanning layer

The attachment contributes degree one exactly at the representative
endpoints. Its disjoint core path cover contributes one there and two
elsewhere in the core. Their union therefore covers the core twice.
-/
namespace OverfullWork.SpanningLayerDegrees
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem disjoint_of_le_residue (G Q K : SimpleGraph V) (hK : K≤G\Q) : Disjoint Q K := by
  apply disjoint_iff_inf_le.mpr
  intro u v ⟨hq,hk⟩
  exact ((hK hk).2 hq).elim

theorem degree_union_of_le_residue (G Q K : SimpleGraph V)
    [DecidableRel Q.Adj] [DecidableRel K.Adj] (hK : K≤G\Q) (v : V) :
    (Q⊔K).degree v=Q.degree v+K.degree v := by
  rw [←card_neighborFinset_eq_degree,neighborFinset_sup,
    card_union_of_disjoint (disjoint_neighborFinset_of_disjoint Q K v
      (disjoint_of_le_residue G Q K hK)),
    card_neighborFinset_eq_degree,card_neighborFinset_eq_degree]

/-- The two complementary degree formulas produce an actual two-cover
of the entire core, and the union stays a graph of maximum degree two. -/
theorem realised_layer_degrees (G Q K : SimpleGraph V)
    [DecidableRel Q.Adj] [DecidableRel K.Adj] (U : Finset V) (E : V → Prop)
    (hQ : Q≤G) (hK : K≤G\Q) (hQdeg : ∀v,Q.degree v≤2)
    (hQcore : ∀v∉U,Q.degree v=if E v then 1 else 0)
    (hKcore : ∀v∉U,K.degree v=if E v then 1 else 2)
    (hKoff : ∀v∈U,K.degree v=0) :
    (Q⊔K)≤G ∧ (∀v,(Q⊔K).degree v≤2) ∧ (∀v∉U,(Q⊔K).degree v=2) := by
  have hdeg:=degree_union_of_le_residue G Q K hK
  refine ⟨sup_le hQ (fun _ _ h => (hK h).1),?_,?_⟩
  · intro v
    rw [hdeg]
    by_cases hv:v∈U
    · rw [hKoff v hv,Nat.add_zero]
      exact hQdeg v
    · rw [hQcore v hv,hKcore v hv]
      split_ifs <;> omega
  · intro v hv
    rw [hdeg,hQcore v hv,hKcore v hv]
    split_ifs <;> omega

/-- Small original degrees on the deleted exceptional set discharge the
top-stratum coverage demand in exact two-colour trimming. -/
theorem maxDegree_residue_of_core_two_cover (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (U : Finset V)
    (hD : 2≤G.maxDegree) (hLG : L≤G)
    (hexception : ∀v∈U,G.degree v+2≤G.maxDegree)
    (hcore : ∀v∉U,L.degree v=2) : (G\L).maxDegree=G.maxDegree-2 := by
  apply TwoColourTrimming.maxDegree_sdiff_of_two_cover G L hD hLG
  intro v hv
  apply hcore
  intro hu
  have hh:=hexception v hu
  omega

theorem critical_residue_of_core_two_cover (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (U : Finset V)
    (hc : Overfull.IsDeltaCritical G) (hD : 2≤G.maxDegree) (hLG : L≤G)
    (hL : L.EdgeColorable 2)
    (hexception : ∀v∈U,G.degree v+2≤G.maxDegree)
    (hcore : ∀v∉U,L.degree v=2) :
    ¬(G\L).EdgeColorable (G\L).maxDegree := by
  apply TwoColourTrimming.critical_residue_not_colourable G L hc hD hLG hL
  intro v hv
  apply hcore
  intro hu
  have hh:=hexception v hu
  omega

end OverfullWork.SpanningLayerDegrees
