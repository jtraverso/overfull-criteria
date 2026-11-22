module

public import OverfullWork.CriticalCorePathPreparation
public import OverfullWork.SpanningLayerDegrees

@[expose] public section


/-! # An actual two-colour degree-lowering layer in the even low case

G1 supplies the uniform scale. The matching, its representatives and the
disjoint spanning core paths are all constructed. Their union is a real
forest, is two-edge-colourable, covers the entire core twice and every
low vertex once. The maximum degree drops by exactly two and a critical
original graph leaves an uncolourable residue. No absence of overfull
sets in that residue is asserted.
-/
namespace OverfullWork.CriticalEvenLowLayer
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open PaperLowSkeleton LowSkeletonProjection PathGraphRealization
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- The resulting layer and the exact degree and colour consequences. -/
structure Certificate (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) where
  layer : SimpleGraph V
  le_original : layer≤G
  acyclic : layer.IsAcyclic
  degree_le_two : ∀v,layer.degree v≤2
  colourable : layer.EdgeColorable 2
  core_two_cover : ∀v∉U,layer.degree v=2
  low_one_cover : ∀w∈lowVertices G,layer.degree w=1
  residual_maxDegree : (G\layer).maxDegree=G.maxDegree-2
  residual_uncolourable : ¬(G\layer).EdgeColorable (G\layer).maxDegree

/-- Every representative occurs in exactly one of the two endpoint
columns of a genuine complete pairing. -/
theorem representative_endpoints {A U Z : Finset V} {G : SimpleGraph V}
    (P : Projection G A U Z) {h : ℕ} (e : (Fin h×Bool)≃A) (z : V) :
    (∃v:A,(P.representative v).val=z) ↔
      ∃i,z=(P.representative (e (i,false))).val ∨ z=(P.representative (e (i,true))).val := by
  constructor
  · rintro ⟨v,rfl⟩
    obtain ⟨⟨i,b⟩,rfl⟩:=e.surjective v
    cases b
    · exact ⟨i,Or.inl rfl⟩
    · exact ⟨i,Or.inr rfl⟩
  · rintro ⟨i,hi|hi⟩
    · exact ⟨e (i,false),hi.symm⟩
    · exact ⟨e (i,true),hi.symm⟩

/-- The finite preparation produces the actual layer, not just the
possibility of a spanning layout. -/
theorem certificate_of_prepared (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) (hc : Overfull.IsDeltaCritical G) (hD : 2≤G.maxDegree)
    (hexception : ∀v∈U,G.degree v+2≤G.maxDegree)
    (s : CriticalCorePathPreparation.EvenPrepared G U k) : Nonempty (Certificate G U) := by
  classical
  let a:=fun i => (s.projection.representative (s.e (i,false))).val
  let b:=fun i => (s.projection.representative (s.e (i,true))).val
  have hab : ∀i,a i≠b i := by
    intro i he
    have he':=s.projection.injective (Subtype.ext he)
    have h:=congrArg Prod.snd (s.e.injective he')
    cases h
  obtain ⟨hLG,hforest,hdeg,hcore⟩:=LowSkeletonLayerGluing.finite_even_gluing G s.M
    (lowVertices G) U (LowSkeletonPreparation.nonisolatedVertices s.M)
    s.skeleton.le_graph s.low_subset s.matching s.skeleton.crosses s.projection
    a b s.paths s.paths_simple s.paths_disjoint s.paths_off s.paths_cover hab
    (representative_endpoints s.projection s.e)
  let L:=(s.M⊔s.projection.matching)⊔pathUnion s.paths
  have hcol : L.EdgeColorable 2:=
    TwoColourTrimming.two_colourable_of_acyclic_and_degree_le_two L hforest hdeg
  have hlow : ∀w∈lowVertices G,L.degree w=1 := by
    intro w hw
    have hQzero : (pathUnion s.paths).degree w=0 :=
      pathUnion_degree_outside s.paths (fun i hi => s.paths_off i w hi (s.low_subset hw))
    have hdis : Disjoint (s.M⊔s.projection.matching) (pathUnion s.paths) := by
      apply disjoint_iff_inf_le.mpr
      intro x y ⟨hQ,hK⟩
      obtain ⟨i,hi⟩:=pathUnion_adj_iff s.paths |>.mp hK
      exact (s.paths_avoid i x y hi hQ).elim
    change ((s.M⊔s.projection.matching)⊔pathUnion s.paths).degree w=1
    rw [←card_neighborFinset_eq_degree,neighborFinset_sup,
      card_union_of_disjoint (disjoint_neighborFinset_of_disjoint _ _ w hdis),
      card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,hQzero,Nat.add_zero]
    exact LowSkeletonAttachmentDegrees.degree_one_on_low s.low_subset s.skeleton.crosses
      s.projection s.low_degree_one hw
  refine ⟨⟨L,hLG,hforest,?_,hcol,?_,?_,?_,?_⟩⟩
  · simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hdeg
  · simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hcore
  · simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hlow
  · simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      SpanningLayerDegrees.maxDegree_residue_of_core_two_cover G L U hD hLG hexception hcore
  · simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      SpanningLayerDegrees.critical_residue_of_core_two_cover G L U hc hD hLG hcol hexception hcore

/-- A complete uniform two-colour trimming step for a positive even low
set. The graph supplies no colouring, matching, projection or paths. -/
theorem above_half_even_low_layer (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        Even (lowVertices G).card → 2≤(lowVertices G).card →
        Nonempty (Certificate G (exceptions G G.maxDegree (Fintype.card V/(8*q)))) := by
  obtain ⟨q,hq,N,hprep⟩:=CriticalCorePathPreparation.above_half_even_core_path_preparation.{u} ε hε
  refine ⟨q,hq,max N (16*q),?_⟩
  intro V _ _ G _ hn hc hdense heven htwo
  have hnN : N≤Fintype.card V := (le_max_left _ _).trans hn
  obtain ⟨_,⟨s⟩⟩:=hprep G hnN hc hdense heven htwo
  have hn16 : 16*q≤Fintype.card V := (le_max_right _ _).trans hn
  have ha : 2≤Fintype.card V/(8*q) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    omega
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hD : 2≤G.maxDegree := by omega
  apply certificate_of_prepared G _ _ hc hD _ s
  intro v hv
  have hh:=(mem_filter.mp hv).2
  omega

end OverfullWork.CriticalEvenLowLayer
