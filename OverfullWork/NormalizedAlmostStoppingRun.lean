module

public import OverfullWork.LocalizedAlmostStoppingRun
public import OverfullWork.CriticalAlmostPairNormalization
public import OverfullWork.DegreeOrderedIndependentCut
public import OverfullWork.IndependentSetIdentification

@[expose] public section


/-! # An actual almost-stop with an independent degree-ordered complement

The heavy-pair move and finite degree-order minimization normalize the
actual terminal cut. Its budget does not increase, its complement cannot
grow, and every endpoint and graph is constructed. Identifying that
independent complement produces an even multigraph with a genuine
colouring pullback. No no-overfull property of that image is assumed or
asserted here.
-/
namespace OverfullWork.NormalizedAlmostStoppingRun
open SimpleGraph Finset OddCutDeficit BoundedCriticalReductionRun
open AlmostStoppingReductionRun
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

structure Certificate (G : SimpleGraph V) [DecidableRel G.Adj] (B K : ℕ) where
  set : Finset V
  odd : Odd set.card
  complement_small : setᶜ.card≤K
  budget : deficitMass G G.maxDegree set+(∑v∈setᶜ,G.degree v)≤G.maxDegree+B
  ordered : ∀y∈setᶜ,∀x∈set,G.degree y≤G.degree x
  light_pairs : ∀y∈setᶜ,∀z∈setᶜ,y≠z → G.degree y+G.degree z<G.maxDegree+2
  independent : G.IsIndepSet (setᶜ:Set V)

/-- Both normalization stages are constructed, and their numerical
invariants refer to the same resulting odd set. -/
theorem exists_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (X : Finset V) (hodd : Odd X.card)
    (B K : ℕ) (hB : B<G.maxDegree+4) (hsmall : Xᶜ.card≤K)
    (hbudget : deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B) :
    Nonempty (Certificate G B K) := by
  obtain ⟨X₁,_,ho₁,hs₁,hb₁,hp₁,_⟩:=
    CriticalAlmostPairNormalization.normalize_odd_set G hc X hodd B hB hbudget
  obtain ⟨X₂,ho₂,hs₂,hd₂,hp₂,hi₂,_,hb₂⟩:=
    DegreeOrderedIndependentCut.exists_ordered_independent_cut G hc X₁ ho₁ hp₁ B hb₁
  exact ⟨⟨X₂,ho₂,hs₂.le.trans (hs₁.trans hsmall),hb₂,hd₂,hp₂,hi₂⟩⟩

noncomputable def Certificate.image {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) :
    MultiGraph (IndependentSetIdentification.Vertices c.setᶜ) :=
  IndependentSetIdentification.graph G c.setᶜ
    (by simpa only [Finset.coe_compl] using c.independent)

theorem Certificate.image_even {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) :
    Even (Fintype.card (IndependentSetIdentification.Vertices c.setᶜ)) := by
  apply IndependentSetIdentification.even_card_vertices
  simpa only [compl_compl] using c.odd

/-- An image colouring would colour the actual current critical graph. -/
theorem Certificate.image_uncolourable {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hc : Overfull.IsDeltaCritical G) :
    ¬Nonempty (c.image.EdgeColoring G.maxDegree) := by
  rintro ⟨C⟩
  exact hc.2.1 (IndependentSetIdentification.colourable_of_identification G c.setᶜ
    (by simpa only [Finset.coe_compl] using c.independent) C)

/-- Every permitted finite run ends at its full budget or at an actual
normalized almost-stop in its current critical copy. -/
theorem above_half_normalized_almost_stopping_run (ε : ℝ) (hε : 0<ε) :
    ∃qR qS qT : ℕ,2≤qR ∧ 2≤qS ∧ 2≤qT ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (hc : Overfull.IsDeltaCritical G) (hno : ¬G.HasOverfullSubgraph),
        2*N+2≤Fintype.card V →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ∀m : ℕ,4*(m:ℝ)≤ε*(Fintype.card V:ℝ) →
        ∃j : ℕ,j≤m ∧ ∃C : CriticalGraph.{u},
          Nonempty (Run (initial G hc hno) C j) ∧
          (j=m ∨ Nonempty (Certificate C.graph (stoppingBudget qR qS C)
            (C.order/(4096*qT^2)+1))) := by
  obtain ⟨qR,qS,qT,hqR,hqS,hqT,N₀,hRun⟩:=
    LocalizedAlmostStoppingRun.above_half_localized_almost_stopping_run.{u} ε hε
  refine ⟨qR,qS,qT,hqR,hqS,hqT,max N₀ 16,?_⟩
  intro V _ _ G _ hc hno hn hdense m hbudget
  obtain ⟨j,hjm,C,⟨p⟩,hEnd⟩:=hRun G hc hno (by omega) hdense m hbudget
  refine ⟨j,hjm,C,⟨p⟩,?_⟩
  rcases hEnd with hEnd|hStop
  · exact Or.inl hEnd
  · right
    obtain ⟨hsize,hd⟩:=run_margins ε hε 16 m p
      (by change 2*16+2≤Fintype.card V;omega) hdense hbudget hjm
    obtain ⟨X,ho,hb,_,_,_,hs⟩:=hStop
    have hnD : C.order≤2*C.graph.maxDegree := by
      have he : 0≤(ε/2)*(C.order:ℝ) := by positivity
      exact_mod_cast (show (C.order:ℝ)≤2*(C.graph.maxDegree:ℝ) by nlinarith only [hd,he])
    have hB : stoppingBudget qR qS C<C.graph.maxDegree+4 :=
      CriticalAlmostPairNormalization.sparse_budget_lt_maxDegree_add_four
        C.graph qR qS hqR hqS hsize hnD
    exact exists_certificate C.graph C.critical X ho _ _ hB hs hb

end OverfullWork.NormalizedAlmostStoppingRun
