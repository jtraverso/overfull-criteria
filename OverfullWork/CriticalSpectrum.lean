module

public import OverfullWork.Critical
public import Overfull.Lemma25

@[expose] public section


/-! # A colouring-free interface to the CCJS degree dichotomy and VAL

The missing-edge colouring required by CCJS is constructed from criticality.
The conclusions constrain a critical obstruction; they do not exclude it.
-/
namespace OverfullWork.Gate8J
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem critical_minDegree_ge_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) :
    2≤G.minDegree := by
  haveI : Nonempty V:=hcrit.1.nonempty
  apply G.le_minDegree_of_forall_le_degree
  intro v
  obtain ⟨u,hu⟩:=(G.degree_pos_iff_exists_adj v).mp (hactive v)
  have h:=Overfull.deg_add hcrit hu
  have hh:=G.degree_le_maxDegree u
  omega

theorem exists_minimum_maximum_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) :
    ∃ a b,G.degree a=G.minDegree ∧ G.Adj a b ∧ G.degree b=G.maxDegree := by
  haveI : Nonempty V:=hcrit.1.nonempty
  obtain ⟨a,ha⟩:=G.exists_minimal_degree_vertex
  obtain ⟨z,haz⟩:=(G.degree_pos_iff_exists_adj a).mp (hactive a)
  obtain ⟨b,hab,_,hb⟩:=Overfull.exists_maxdeg_nbr hcrit haz
  exact ⟨a,b,ha.symm,hab,hb⟩

/-- A maximum-degree neighbour of a minimum-degree vertex has at least
Delta-delta+1 other neighbours of maximum degree. -/
theorem minimum_edge_maximum_neighbours (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) {a b : V}
    (ha : G.degree a=G.minDegree) (hab : G.Adj a b) :
    G.maxDegree-G.minDegree+1≤
      ((G.neighborFinset b).filter fun z => z≠a ∧ G.degree z=G.maxDegree).card := by
  have h:=Overfull.val_crit hcrit hab.symm
  have hm:=(G.minDegree_le_degree a).trans (G.degree_le_maxDegree a)
  rw [ha] at h
  omega

/-- The CCJS forbidden interval, with no colouring left as an input. -/
theorem minimum_edge_degree_dichotomy (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) {a b : V}
    (ha : G.degree a=G.minDegree) (hab : G.Adj a b)
    (hb : G.degree b=G.maxDegree) (hmin : 2≤G.minDegree)
    {v : V} (hva : v≠a) (hlo : G.degree v+G.minDegree≤G.maxDegree) :
    G.degree v+G.maxDegree+5<Fintype.card V+2*G.minDegree := by
  obtain ⟨c,hcm⟩:=Overfull.exists_colMinus_of_colorable hab
    (hcrit.2.2 s(a,b) ((mem_edgeSet G).mpr hab))
  by_contra hn
  exact Overfull.degree_dichotomy hcrit hcm hb (by omega) hva (by omega) (by omega)

/-- Low-degree vertices in this range cannot be adjacent to the chosen
minimum-degree vertex. This conclusion does not require a Kempe colouring. -/
theorem minimum_nonadjacent_of_degree_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) {a v : V}
    (ha : G.degree a=G.minDegree) (hlo : G.degree v+G.minDegree≤G.maxDegree) :
    ¬G.Adj a v := by
  intro hadj
  have h:=Overfull.deg_add hcrit hadj
  omega

/-- A reusable package of the local restrictions around a minimum edge. -/
theorem exists_minimum_edge_spectrum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) :
    2≤G.minDegree ∧ ∃ a b,
      G.degree a=G.minDegree ∧ G.Adj a b ∧ G.degree b=G.maxDegree ∧
      G.maxDegree-G.minDegree+1≤
        ((G.neighborFinset b).filter fun z => z≠a ∧ G.degree z=G.maxDegree).card ∧
      (∀ v,v≠a → G.degree v+G.minDegree≤G.maxDegree →
        G.degree v+G.maxDegree+5<Fintype.card V+2*G.minDegree) ∧
      ∀ v,G.degree v+G.minDegree≤G.maxDegree → ¬G.Adj a v := by
  have hmin:=critical_minDegree_ge_two G hcrit hactive
  obtain ⟨a,b,ha,hab,hb⟩:=exists_minimum_maximum_edge G hcrit hactive
  exact ⟨hmin,a,b,ha,hab,hb,minimum_edge_maximum_neighbours G hcrit ha hab,
    fun _ hv hl => minimum_edge_degree_dichotomy G hcrit ha hab hb hmin hv hl,
    fun _ hl => minimum_nonadjacent_of_degree_sum G hcrit ha hl⟩

end OverfullWork.Gate8J
