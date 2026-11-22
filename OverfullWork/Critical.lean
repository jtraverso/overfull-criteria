module

public import OverfullWork.Gluing
public import Overfull.Basic

@[expose] public section


/-!
# Extraction of a connected maximum-degree critical obstruction

The Vizing upper bound and the predicate `Overfull.IsDeltaCritical` are
reused from the registered sources, with explicit local provenance.
Minimality is first taken on the original vertex type; only afterwards
do we restrict to the effective support, removing all isolated vertices.
-/

namespace OverfullWork.Critical

set_option maxHeartbeats 1000000

open SimpleGraph Finset

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem colourable_of_copy {W : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    (f : Copy H G) {k : ℕ} (hc : G.EdgeColorable k) : H.EdgeColorable k :=
  Colorable.of_hom f.lineGraph.toHom hc

theorem exists_edgeMinimal (G : SimpleGraph V) {k : ℕ} (hG : ¬ G.EdgeColorable k) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ¬ H.EdgeColorable k ∧
      ∀ e ∈ H.edgeSet, (H.deleteEdges {e}).EdgeColorable k := by
  classical
  have hex : ∃ m : ℕ, ∃ H : SimpleGraph V,
      H ≤ G ∧ H.edgeSet.ncard = m ∧ ¬ H.EdgeColorable k :=
    ⟨G.edgeSet.ncard, G, le_rfl, rfl, hG⟩
  obtain ⟨H, hHG, hcard, hnc⟩ := Nat.find_spec hex
  refine ⟨H, hHG, hnc, ?_⟩
  intro e he
  by_contra hbad
  have hlt : (H.deleteEdges {e}).edgeSet.ncard < Nat.find hex := by
    rw [← hcard]
    apply Set.ncard_lt_ncard _ (Set.toFinite _)
    rw [edgeSet_deleteEdges]
    exact Set.sdiff_ssubset_left_iff.mpr ⟨e, he, rfl⟩
  exact Nat.find_min hex hlt
    ⟨H.deleteEdges {e}, (deleteEdges_le _).trans hHG, rfl, hbad⟩

omit [DecidableEq V] in
/-- The only use of Vizing in the degree-preservation argument. -/
theorem maxDegree_eq_of_obstruction {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : H ≤ G) (hnc : ¬ H.EdgeColorable G.maxDegree) :
    H.maxDegree = G.maxDegree := by
  have hmax := maxDegree_mono hle
  by_contra hne
  exact hnc ((LeanPool.Vizing.lineGraph_colorable H).mono (by omega))

omit [Fintype V] [DecidableEq V] in
/-- All endpoints of an edge lie in the same reachable component. -/
theorem edge_component_iff (H : SimpleGraph V) (x : V) (e : H.edgeSet)
    {z : V} (hz : z ∈ (e : Sym2 V)) :
    (∃ w ∈ (e : Sym2 V), H.Reachable x w) ↔ H.Reachable x z := by
  obtain ⟨t, het⟩ := Sym2.mem_iff_exists.mp hz
  have hadj : H.Adj z t := by
    apply (mem_edgeSet H).mp
    rw [← het]
    exact e.property
  constructor
  · rintro ⟨w, hw, hr⟩
    rw [het, Sym2.mem_iff] at hw
    rcases hw with rfl | rfl
    · exact hr
    · exact hr.trans hadj.symm.reachable
  · exact fun hr => ⟨z, hz, hr⟩

/-- Edge-criticality forces all non-isolated vertices into one component.
The proof glues two edge-deleted colourings along a component cut. -/
theorem reachable_on_support_of_edgeCritical (H : SimpleGraph V) {k : ℕ}
    (hnc : ¬ H.EdgeColorable k)
    (hdel : ∀ e ∈ H.edgeSet, (H.deleteEdges {e}).EdgeColorable k)
    {x y : V} (hx : x ∈ H.support) (hy : y ∈ H.support) : H.Reachable x y := by
  classical
  by_contra hxy
  obtain ⟨a, hxa⟩ := H.mem_support.mp hx
  obtain ⟨b, hyb⟩ := H.mem_support.mp hy
  let ex : H.edgeSet := ⟨s(x, a), hxa⟩
  let ey : H.edgeSet := ⟨s(y, b), hyb⟩
  let inside (e : H.edgeSet) : Prop := ∃ z ∈ (e : Sym2 V), H.Reachable x z
  have hex : inside ex := ⟨x, Sym2.mem_mk_left _ _, .refl _⟩
  have hey : ¬ inside ey := by
    intro h
    exact hxy ((edge_component_iff H x ey (Sym2.mem_mk_left _ _)).mp h)
  obtain ⟨Cx⟩ := hdel ex ex.property
  obtain ⟨Cy⟩ := hdel ey ey.property
  have hin (e : H.edgeSet) (h : inside e) :
      (e : Sym2 V) ∈ (H.deleteEdges {(ey : Sym2 V)}).edgeSet := by
    rw [edgeSet_deleteEdges]
    refine ⟨e.property, ?_⟩
    intro heq
    have he : e = ey := Subtype.ext (Set.mem_singleton_iff.mp heq)
    exact hey (he ▸ h)
  have hout (e : H.edgeSet) (h : ¬ inside e) :
      (e : Sym2 V) ∈ (H.deleteEdges {(ex : Sym2 V)}).edgeSet := by
    rw [edgeSet_deleteEdges]
    refine ⟨e.property, ?_⟩
    intro heq
    have he : e = ex := Subtype.ext (Set.mem_singleton_iff.mp heq)
    exact h (he.symm ▸ hex)
  apply hnc
  refine ⟨Coloring.mk (fun e => if h : inside e then Cy ⟨e, hin e h⟩
    else Cx ⟨e, hout e h⟩) ?_⟩
  intro e f hadj
  obtain ⟨hef, z, hze, hzf⟩ := lineGraph_adj_iff_exists.mp hadj
  have hs : inside e ↔ inside f :=
    (edge_component_iff H x e hze).trans (edge_component_iff H x f hzf).symm
  by_cases he : inside e
  · have hf := hs.mp he
    simp only [dif_pos he, dif_pos hf]
    apply Cy.valid
    exact lineGraph_adj_iff_exists.mpr
      ⟨fun hh => hef (Subtype.ext (congrArg
        (fun q : (H.deleteEdges {(ey : Sym2 V)}).edgeSet => (q : Sym2 V)) hh)),
        z, hze, hzf⟩
  · have hf : ¬ inside f := fun h => he (hs.mpr h)
    simp only [dif_neg he, dif_neg hf]
    apply Cx.valid
    exact lineGraph_adj_iff_exists.mpr
      ⟨fun hh => hef (Subtype.ext (congrArg
        (fun q : (H.deleteEdges {(ex : Sym2 V)}).edgeSet => (q : Sym2 V)) hh)),
        z, hze, hzf⟩

omit [Fintype V] [DecidableEq V] in
/-- Restricting to the support preserves edge-colourability in both directions. -/
theorem induce_support_colourable_iff (H : SimpleGraph V) (k : ℕ) :
    (H.induce H.support).EdgeColorable k ↔ H.EdgeColorable k := by
  classical
  let f := (Copy.induce H H.support).toLineGraphEmbedding
  have hsur : Function.Surjective f := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : H.Adj a b := he
      exact ⟨⟨s(⟨a, hab.mem_support_left⟩, ⟨b, hab.mem_support_right⟩), hab⟩, rfl⟩
  constructor
  · rintro ⟨C⟩
    let inv (e : H.edgeSet) := Classical.choose (hsur e)
    have hinv (e : H.edgeSet) : f (inv e) = e := Classical.choose_spec (hsur e)
    refine ⟨Coloring.mk (fun e => C (inv e)) ?_⟩
    intro e g hadj
    apply C.valid
    apply f.map_rel_iff.mp
    simpa only [hinv] using hadj
  · exact colourable_of_copy (Copy.induce H H.support)

theorem connected_induce_support (H : SimpleGraph V) {k : ℕ}
    (hnc : ¬ H.EdgeColorable k)
    (hdel : ∀ e ∈ H.edgeSet, (H.deleteEdges {e}).EdgeColorable k) :
    (H.induce H.support).Connected := by
  classical
  have hne : H.support.Nonempty := by
    by_contra h
    have hbot : H = ⊥ := (support_eq_bot_iff H).mp (Set.not_nonempty_iff_eq_empty.mp h)
    apply hnc
    rw [hbot]
    have hF (e : (⊥ : SimpleGraph V).edgeSet) : False := by simpa using e.property
    refine ⟨Coloring.mk (fun e => (hF e).elim) ?_⟩
    intro e f _
    exact (hF e).elim
  refine { preconnected := ?_, nonempty := hne.to_subtype }
  intro a b
  obtain ⟨p⟩ := reachable_on_support_of_edgeCritical H hnc hdel a.property b.property
  by_cases hab : a.val = b.val
  · cases Subtype.ext hab
    exact Reachable.refl a
  · have hp : ¬ p.Nil := fun h => hab h.eq
    exact ⟨p.induce H.support (fun z hz => mem_support_of_mem_walk_support p hp hz)⟩

/-- A copy also transports the operation of deleting one edge. -/
def deleteEdgeCopy {W : Type v} {A : SimpleGraph W} {B : SimpleGraph V}
    (f : Copy A B) (e : A.edgeSet) :
    Copy (A.deleteEdges {(e : Sym2 W)}) (B.deleteEdges {Sym2.map f (e : Sym2 W)}) where
  toHom := {
    toFun := f
    map_rel' := by
      intro a b hab
      rw [deleteEdges_adj] at hab ⊢
      refine ⟨f.toHom.map_adj hab.1, ?_⟩
      simp only [Set.mem_singleton_iff] at hab ⊢
      intro heq
      apply hab.2
      apply Sym2.map.injective f.injective
      exact heq }
  injective' := f.injective

theorem critical_induce_support (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidablePred (· ∈ H.support)]
    (hnc : ¬ H.EdgeColorable H.maxDegree)
    (hdel : ∀ e ∈ H.edgeSet, (H.deleteEdges {e}).EdgeColorable H.maxDegree) :
    Overfull.IsDeltaCritical (H.induce H.support) := by
  classical
  have hmax : (H.induce H.support).maxDegree = H.maxDegree :=
    maxDegree_induce_of_support_subset (G := H) (s := H.support) subset_rfl
  refine ⟨connected_induce_support H hnc hdel, ?_, ?_⟩
  · change ¬ (H.induce H.support).EdgeColorable (H.induce H.support).maxDegree
    rw [hmax]
    exact fun hc => hnc ((induce_support_colourable_iff H H.maxDegree).mp hc)
  · intro e he
    let f := Copy.induce H H.support
    have hmap : Sym2.map f e ∈ H.edgeSet := f.toHom.map_mem_edgeSet he
    have hc := colourable_of_copy (deleteEdgeCopy f ⟨e, he⟩)
      (hdel (Sym2.map f e) hmap)
    rwa [hmax]

/-- Overfullness at the common maximum degree transports through an injective copy. -/
theorem overfull_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree = G.maxDegree)
    (hof : H.HasOverfullSubgraph) : G.HasOverfullSubgraph := by
  classical
  obtain ⟨S, hS⟩ := hof
  let T := S.image f
  let ES := H.edgeFinset.filter (fun e => e.toFinset ⊆ S)
  let ET := G.edgeFinset.filter (fun e => e.toFinset ⊆ T)
  have hcard : T.card = S.card := card_image_of_injective S f.injective
  have hsub : ES.image (Sym2.map f) ⊆ ET := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    obtain ⟨haE, haS⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_edgeFinset.mpr (f.toHom.map_mem_edgeSet (mem_edgeFinset.mp haE))
    · intro z hz
      have hz' : z ∈ Sym2.map f a := by simpa using hz
      obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.mp hz'
      exact mem_image.mpr ⟨w, haS (by simpa using hw), rfl⟩
  have hecount : ES.card ≤ ET.card := by
    calc
      ES.card = (ES.image (Sym2.map f)).card :=
        (card_image_of_injective ES (Sym2.map.injective f.injective)).symm
      _ ≤ ET.card := card_le_card hsub
  refine ⟨T, ?_⟩
  rw [hcard, ← hmax]
  exact lt_of_lt_of_le hS hecount

theorem no_overfull_of_copy {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree = G.maxDegree)
    (hno : ¬ G.HasOverfullSubgraph) : ¬ H.HasOverfullSubgraph :=
  fun hof => hno (overfull_of_copy f hmax hof)

/-- A connected critical obstruction, bundled with its effective vertex type
and the exact registered CCJS predicate. -/
structure CriticalWitness (G : SimpleGraph V) [DecidableRel G.Adj] where
  vertices : Type u
  [finiteVertices : Fintype vertices]
  [decidableVertices : DecidableEq vertices]
  graph : SimpleGraph vertices
  [decidableAdjacency : DecidableRel graph.Adj]
  embedding : Copy graph G
  maxDegree_eq : graph.maxDegree = G.maxDegree
  critical : Overfull.IsDeltaCritical graph
  no_overfull : ¬ graph.HasOverfullSubgraph
  no_isolates : ∀ w, 0 < graph.degree w
  order_le : Fintype.card vertices ≤ Fintype.card V

attribute [instance] CriticalWitness.finiteVertices CriticalWitness.decidableVertices
  CriticalWitness.decidableAdjacency

/-- Every class-two graph without a Delta-overfull subgraph has a connected
Delta-critical obstruction with the same maximum degree and no isolated vertices. -/
theorem exists_criticalWitness (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnc : ¬ G.EdgeColorable G.maxDegree) (hno : ¬ G.HasOverfullSubgraph) :
    Nonempty (CriticalWitness G) := by
  classical
  obtain ⟨H, hHG, hncH, hdelH⟩ := exists_edgeMinimal G hnc
  have hmaxH : H.maxDegree = G.maxDegree := maxDegree_eq_of_obstruction hHG hncH
  have hclassH : ¬ H.EdgeColorable H.maxDegree := by rwa [hmaxH]
  have hcritH : ∀ e ∈ H.edgeSet, (H.deleteEdges {e}).EdgeColorable H.maxDegree := by
    simpa only [hmaxH] using hdelH
  let K := H.induce H.support
  let f : Copy K G := (Copy.ofLE H G hHG).comp (Copy.induce H H.support)
  have hmaxK : K.maxDegree = G.maxDegree :=
    (maxDegree_induce_of_support_subset (G := H) (s := H.support) subset_rfl).trans hmaxH
  refine ⟨{
    vertices := H.support
    graph := K
    embedding := f
    maxDegree_eq := hmaxK
    critical := critical_induce_support H hclassH hcritH
    no_overfull := no_overfull_of_copy f hmaxK hno
    no_isolates := ?_
    order_le := Fintype.card_le_of_injective Subtype.val Subtype.val_injective }⟩
  intro w
  change 0 < (H.induce H.support).degree w
  rw [degree_induce_support]
  exact (H.degree_pos_iff_mem_support w.val).mpr w.property

omit [DecidableEq V] in
/-- The density hypothesis of the Overfull conjecture survives extraction. -/
theorem CriticalWitness.density {G : SimpleGraph V} [DecidableRel G.Adj]
    (w : CriticalWitness G) (hdeg : 3 * G.maxDegree > Fintype.card V) :
    3 * w.graph.maxDegree > Fintype.card w.vertices := by
  have horder := w.order_le
  rw [w.maxDegree_eq]
  omega

omit [DecidableEq V] in
/-- A witness is not overfull even as a whole graph. -/
theorem CriticalWitness.not_overfull {G : SimpleGraph V} [DecidableRel G.Adj]
    (w : CriticalWitness G) : ¬ Overfull.IsOverfull w.graph := by
  intro hof
  apply w.no_overfull
  refine ⟨univ, ?_⟩
  simpa [Overfull.IsOverfull] using hof

/-- The hard direction of the Overfull conjecture, with the strict threshold. -/
def HardDirection : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    3 * H.maxDegree > Fintype.card W →
    ¬ H.HasOverfullSubgraph → H.EdgeColorable H.maxDegree

/-- The remaining research problem after extraction: critical graphs in the
strict density range must contain a Delta-overfull subgraph. This is a
proposition to be proved, not an imported theorem or a new axiom. -/
def CriticalCase : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    Overfull.IsDeltaCritical H →
    3 * H.maxDegree > Fintype.card W → H.HasOverfullSubgraph

/-- Exact reduction of the hard direction to connected Delta-critical graphs.
No fan lemma or decomposition hypothesis is assumed by this equivalence. -/
theorem hardDirection_iff_criticalCase : HardDirection.{u} ↔ CriticalCase.{u} := by
  constructor
  · intro hall W _ _ H _ hcrit hdeg
    by_contra hno
    exact hcrit.2.1 (hall W H hdeg hno)
  · intro hcritical W _ _ H _ hdeg hno
    by_contra hnc
    obtain ⟨w⟩ := exists_criticalWitness H hnc hno
    exact w.no_overfull (hcritical w.vertices w.graph w.critical (w.density hdeg))

#print axioms maxDegree_eq_of_obstruction
#print axioms connected_induce_support
#print axioms critical_induce_support
#print axioms no_overfull_of_copy
#print axioms exists_criticalWitness
#print axioms CriticalWitness.density
#print axioms CriticalWitness.not_overfull
#print axioms hardDirection_iff_criticalCase

end OverfullWork.Critical
