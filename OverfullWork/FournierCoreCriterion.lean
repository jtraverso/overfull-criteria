module

public import OverfullWork.MaximumCoreDegree
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section


/-! # Fournier's maximum-core criterion through critical extraction

This is a formal interface to a known structural class-one criterion.
No density, order, degree-gap, or absence-of-overfull hypothesis is used.
-/
namespace OverfullWork.FournierCore
open SimpleGraph Finset
open scoped Classical
set_option maxHeartbeats 4000000
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A critical copy without an overfullness field. It can be extracted
from every class-two graph, including graphs which are themselves overfull. -/
structure CriticalCopy (G : SimpleGraph V) [DecidableRel G.Adj] where
  vertices : Type u
  [finiteVertices : Fintype vertices]
  [decidableVertices : DecidableEq vertices]
  graph : SimpleGraph vertices
  [decidableAdjacency : DecidableRel graph.Adj]
  embedding : Copy graph G
  maxDegree_eq : graph.maxDegree=G.maxDegree
  critical : Overfull.IsDeltaCritical graph
  no_isolates : ∀ w,0<graph.degree w

attribute [instance] CriticalCopy.finiteVertices CriticalCopy.decidableVertices CriticalCopy.decidableAdjacency

theorem exists_criticalCopy (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnc : ¬G.EdgeColorable G.maxDegree) : Nonempty (CriticalCopy G) := by
  classical
  obtain ⟨H,hHG,hncH,hdelH⟩:=Critical.exists_edgeMinimal G hnc
  have hmaxH : H.maxDegree=G.maxDegree:=Critical.maxDegree_eq_of_obstruction hHG hncH
  have hclassH : ¬H.EdgeColorable H.maxDegree:=by rwa [hmaxH]
  have hcritH : ∀ e∈H.edgeSet,(H.deleteEdges {e}).EdgeColorable H.maxDegree:=by
    simpa only [hmaxH] using hdelH
  let K:=H.induce H.support
  let f : Copy K G:=(Copy.ofLE H G hHG).comp (Copy.induce H H.support)
  have hmaxK : K.maxDegree=G.maxDegree:=
    (maxDegree_induce_of_support_subset (G:=H) (s:=H.support) subset_rfl).trans hmaxH
  refine ⟨{ vertices := H.support
            graph := K
            embedding := f
            maxDegree_eq := hmaxK
            critical := Critical.critical_induce_support H hclassH hcritH
            no_isolates := ?_ }⟩
  intro w
  change 0<(H.induce H.support).degree w
  rw [degree_induce_support]
  exact (H.degree_pos_iff_mem_support w.val).mpr w.property

/-- Every nonempty induced subgraph of the maximum-degree core has a
vertex with at most one neighbour inside it. -/
def CoreOneDegenerate (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ T : Finset V,T.Nonempty → (∀ v∈T,G.degree v=G.maxDegree) →
    ∃ v∈T,((G.neighborFinset v).filter fun z => z∈T).card≤1

/-- The one-degenerate maximum-degree core criterion, without any
large-order or density hypothesis. -/
theorem edgeColourable_of_core_one_degenerate (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcore : CoreOneDegenerate G) : G.EdgeColorable G.maxDegree := by
  by_contra hnc
  obtain ⟨w⟩:=exists_criticalCopy G hnc
  haveI : Nonempty w.vertices:=w.critical.1.nonempty
  let T:=(univ : Finset w.vertices).filter fun x => w.graph.degree x=w.graph.maxDegree
  let S:=T.image w.embedding
  obtain ⟨x,hx⟩:=w.graph.exists_maximal_degree_vertex
  have hxT : x∈T:=mem_filter.mpr ⟨mem_univ x,hx.symm⟩
  have hS : S.Nonempty:=⟨w.embedding x,mem_image.mpr ⟨x,hxT,rfl⟩⟩
  have hSD : ∀ v∈S,G.degree v=G.maxDegree := by
    intro v hv
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hv
    have hzD:=(mem_filter.mp hz).2
    have hl:=w.embedding.degree_le z
    have hu:=G.degree_le_maxDegree (w.embedding z)
    have he:=w.maxDegree_eq
    omega
  obtain ⟨v,hv,hsmall⟩:=hcore S hS hSD
  obtain ⟨z,hz,rfl⟩:=mem_image.mp hv
  let N:=(w.graph.neighborFinset z).filter fun y => w.graph.degree y=w.graph.maxDegree
  have hlarge : 2≤N.card:=Gate8J2C.critical_maximumNeighbours_ge_two w.graph w.critical w.no_isolates z
  have hsub : N.image w.embedding⊆(G.neighborFinset (w.embedding z)).filter fun y => y∈S := by
    intro y hy
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hy
    obtain ⟨haN,haD⟩:=mem_filter.mp ha
    apply mem_filter.mpr
    refine ⟨(mem_neighborFinset G _ _).mpr (w.embedding.toHom.map_adj ((mem_neighborFinset w.graph _ _).mp haN)),?_⟩
    exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ a,haD⟩,rfl⟩
  have hcard:=card_le_card hsub
  have hinj : Function.Injective (fun a : w.vertices => w.embedding a):=fun _ _ he => w.embedding.injective he
  rw [card_image_of_injective N hinj] at hcard
  omega

/-- Every nonempty finite forest contains a vertex of degree at most one. -/
theorem exists_degree_le_one_of_acyclic (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hacyclic : G.IsAcyclic) : ∃ v, G.degree v ≤ 1 := by
  classical
  let x : V := Classical.choice inferInstance
  let c := G.connectedComponentMk x
  have hx : x ∈ c.supp := by simp [c]
  rcases subsingleton_or_nontrivial c with hc | hc
  · haveI := hc
    refine ⟨x, ?_⟩
    have hz : G.degree x = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hp
      obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp hp
      have hy : y ∈ c.supp := c.mem_supp_of_adj_mem_supp hx hxy
      have he : (⟨x, hx⟩ : c) = ⟨y, hy⟩ := Subsingleton.elim _ _
      exact hxy.ne (congrArg Subtype.val he)
    omega
  · haveI := hc
    obtain ⟨v, hv⟩ := (hacyclic.isTree_connectedComponent c).exists_vert_degree_one_of_nontrivial
    refine ⟨v.val, ?_⟩
    have he : c.toSimpleGraph.degree v = G.degree v.val := by
      calc
        c.toSimpleGraph.degree v = (G.induce c.supp).degree v := by
          unfold SimpleGraph.degree
          congr 1
          ext y
          change (y ∈ c.toSimpleGraph.neighborFinset v ↔
            y ∈ (G.induce c.supp).neighborFinset v)
          constructor <;> intro hy
          · have hy' : G.Adj v.val y.val := (mem_neighborFinset c.toSimpleGraph v y).mp hy
            exact (mem_neighborFinset (G.induce c.supp) v y).mpr hy'
          · have hy' : G.Adj v.val y.val := (mem_neighborFinset (G.induce c.supp) v y).mp hy
            exact (mem_neighborFinset c.toSimpleGraph v y).mpr hy'

        _ = G.degree v.val := G.degree_induce_of_neighborSet_subset (fun y hy =>
          c.mem_supp_of_adj_mem_supp v.property hy)
    omega

/-- A forest maximum-degree core is one-degenerate. -/
theorem core_one_degenerate_of_acyclic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hforest : (G.induce {v | G.degree v = G.maxDegree}).IsAcyclic) :
    CoreOneDegenerate G := by
  classical
  intro T hT hmax
  let H := G.induce (T : Set V)
  haveI : Nonempty (T : Set V) := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  let f : H →g G.induce {v | G.degree v = G.maxDegree} :=
    { toFun := fun v => ⟨v.val, hmax v.val v.property⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : {v | G.degree v = G.maxDegree} => z.val) hab
  have hH : H.IsAcyclic := hforest.comap f hf
  obtain ⟨v, hv⟩ := exists_degree_le_one_of_acyclic H hH
  refine ⟨v.val, v.property, ?_⟩
  have hec' : H.degree v = ((G.neighborFinset v.val).filter (fun z => z ∈ T)).card := by
    calc
      H.degree v = ((H.neighborFinset v).map (.subtype (· ∈ (T : Set V)))).card := by simp
      _ = ((G.neighborFinset v.val).filter (fun z => z ∈ T)).card := by
        congr 1
        ext z
        simp [H]

  omega

/-- Fournier's forest-core criterion: a simple graph whose maximum-degree
vertices induce an acyclic graph has a proper edge-colouring with Δ colours. -/
theorem edgeColourable_of_acyclic_maximum_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (hforest : (G.induce {v | G.degree v = G.maxDegree}).IsAcyclic) :
    G.EdgeColorable G.maxDegree :=
  edgeColourable_of_core_one_degenerate G (core_one_degenerate_of_acyclic G hforest)

end OverfullWork.FournierCore
