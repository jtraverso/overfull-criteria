module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import OverfullWork.SimpleColouringBridge

@[expose] public section


/-! # Ambient graphs realized by actual paths

The graph consists exactly of the edges of the given walk. Pathhood
proves its endpoint and internal degrees, and its acyclicity; no graph
realization or degree profile is supplied as an additional input.
-/
namespace OverfullWork.PathGraphRealization
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

def pathGraph (p : G.Walk u v) : SimpleGraph V := p.toSubgraph.spanningCoe

theorem le_original (p : G.Walk u v) : pathGraph p≤G := p.toSubgraph.spanningCoe_le

theorem mem_support_of_adj (p : G.Walk u v) {a b : V}
    (hab : (pathGraph p).Adj a b) : a∈p.support :=
  Walk.mem_support_of_adj_toSubgraph hab

theorem degree_outside (p : G.Walk u v) {w : V} (hw : w∉p.support) :
    (pathGraph p).degree w=0 := by
  rw [←card_neighborFinset_eq_degree,card_eq_zero]
  apply eq_empty_of_forall_notMem
  intro z hz
  exact hw (mem_support_of_adj p ((mem_neighborFinset _ _ _).mp hz))

theorem degree_start (p : G.Walk u v) (hp : p.IsPath) (huv : u≠v) :
    (pathGraph p).degree u=1 := by
  have hn : ¬p.Nil := Walk.not_nil_of_ne huv
  have hset := hp.neighborSet_toSubgraph_startpoint hn
  have hfin : (pathGraph p).neighborFinset u={p.snd} := by
    ext w
    simp only [mem_neighborFinset,mem_singleton]
    exact Set.ext_iff.mp hset w
  rw [←card_neighborFinset_eq_degree,hfin,card_singleton]

theorem degree_end (p : G.Walk u v) (hp : p.IsPath) (huv : u≠v) :
    (pathGraph p).degree v=1 := by
  have hset := hp.neighborSet_toSubgraph_endpoint (Walk.not_nil_of_ne huv)
  have hfin : (pathGraph p).neighborFinset v={p.penultimate} := by
    ext w
    simp only [mem_neighborFinset,mem_singleton]
    exact Set.ext_iff.mp hset w
  rw [←card_neighborFinset_eq_degree,hfin,card_singleton]

theorem degree_internal (p : G.Walk u v) (hp : p.IsPath) {w : V}
    (hw : w∈p.support) (hwu : w≠u) (hwv : w≠v) :
    (pathGraph p).degree w=2 := by
  obtain ⟨i,hi,hil⟩:=Walk.mem_support_iff_exists_getVert.mp hw
  have hi0 : i≠0 := by intro h;subst i;simp only [Walk.getVert_zero] at hi;exact hwu hi.symm
  have hit : i<p.length := by
    by_contra hh
    have he : i=p.length := by omega
    subst i
    simp only [Walk.getVert_length] at hi
    exact hwv hi.symm
  have hset := hp.neighborSet_toSubgraph_internal hi0 hit
  have hfin : (pathGraph p).neighborFinset w={p.getVert (i-1),p.getVert (i+1)} := by
    ext z
    simp only [mem_neighborFinset,mem_insert,mem_singleton]
    rw [←hi]
    exact Set.ext_iff.mp hset z
  have hne : p.getVert (i-1)≠p.getVert (i+1) := by
    intro he
    have hh:=hp.getVert_injOn (by simp only [Set.mem_ofPred_eq];omega)
      (by simp only [Set.mem_ofPred_eq];omega) he
    omega
  rw [←card_neighborFinset_eq_degree,hfin,card_pair hne]

theorem degree_le_two (p : G.Walk u v) (hp : p.IsPath) (w : V) :
    (pathGraph p).degree w≤2 := by
  by_cases hw : w∈p.support
  · by_cases hwu : w=u
    · subst w
      by_cases huv : u=v
      · subst v
        have he : p=Walk.nil := (Walk.isPath_iff_nil.mp hp).eq_nil
        subst p
        have hz : (pathGraph (Walk.nil : G.Walk u u)).neighborFinset u=∅ := by
          apply eq_empty_of_forall_notMem
          intro z hz
          exact (mem_neighborFinset _ _ _).mp hz
        rw [←card_neighborFinset_eq_degree,hz]
        simp
      · rw [degree_start p hp huv];omega
    · by_cases hwv : w=v
      · subst w;rw [degree_end p hp (fun he => hwu he.symm)];omega
      · rw [degree_internal p hp hw hwu hwv]
  · rw [degree_outside p hw];omega

theorem isAcyclic (p : G.Walk u v) (hp : p.IsPath) : (pathGraph p).IsAcyclic := by
  induction p with
  | nil =>
    change (⊥ : SimpleGraph V).IsAcyclic
    exact isAcyclic_bot
  | @cons a b c hab p ih =>
    obtain ⟨hp',ha⟩:=Walk.cons_isPath_iff hab p |>.mp hp
    have he : pathGraph (Walk.cons hab p)=pathGraph p⊔edge a b := by
      ext z w
      simp only [pathGraph,Walk.toSubgraph,Subgraph.sup_spanningCoe,sup_adj,
        Subgraph.spanningCoe_adj,subgraphOfAdj_adj,edge_adj]
      grind [Sym2.eq_iff,hab.ne]
    rw [he]
    exact (ih hp').sup_edge_of_not_reachable
      (not_reachable_of_left_degree_zero hab.ne (degree_outside p ha))

section Family
variable {I : Type*} [Fintype I] {a b : I → V}

def pathUnion (P : ∀i,G.Walk (a i) (b i)) : SimpleGraph V := ⨆i,pathGraph (P i)

theorem pathUnion_le_original (P : ∀i,G.Walk (a i) (b i)) : pathUnion P≤G :=
  iSup_le (fun i => le_original (P i))

theorem pathUnion_adj_iff (P : ∀i,G.Walk (a i) (b i)) {z w : V} :
    (pathUnion P).Adj z w ↔ ∃i,(pathGraph (P i)).Adj z w := iSup_adj

theorem pathUnion_adj_iff_of_mem_support (P : ∀i,G.Walk (a i) (b i))
    (hdis : ∀i j,i≠j → ∀z,z∈(P i).support → z∉(P j).support)
    (i : I) {z w : V} (hz : z∈(P i).support) :
    (pathUnion P).Adj z w ↔ (pathGraph (P i)).Adj z w := by
  constructor
  · intro h
    obtain ⟨j,hj⟩:=pathUnion_adj_iff P |>.mp h
    have hij : i=j := by
      by_contra hn
      exact hdis i j hn z hz (mem_support_of_adj (P j) hj)
    subst j
    exact hj
  · exact fun h => pathUnion_adj_iff P |>.mpr ⟨i,h⟩

theorem degree_eq_of_mem_support (P : ∀i,G.Walk (a i) (b i))
    (hdis : ∀i j,i≠j → ∀z,z∈(P i).support → z∉(P j).support)
    (i : I) {z : V} (hz : z∈(P i).support) :
    (pathUnion P).degree z=(pathGraph (P i)).degree z := by
  have he : (pathUnion P).neighborFinset z=(pathGraph (P i)).neighborFinset z := by
    ext w
    simp only [mem_neighborFinset]
    exact pathUnion_adj_iff_of_mem_support P hdis i hz
  exact congrArg Finset.card he

theorem pathUnion_degree_outside (P : ∀i,G.Walk (a i) (b i)) {z : V}
    (hz : ∀i,z∉(P i).support) : (pathUnion P).degree z=0 := by
  rw [←card_neighborFinset_eq_degree,card_eq_zero]
  apply eq_empty_of_forall_notMem
  intro w hw
  obtain ⟨i,hi⟩:=pathUnion_adj_iff P |>.mp ((mem_neighborFinset _ _ _).mp hw)
  exact hz i (mem_support_of_adj (P i) hi)

theorem pathUnion_degree_le_two (P : ∀i,G.Walk (a i) (b i)) (hp : ∀i,(P i).IsPath)
    (hdis : ∀i j,i≠j → ∀z,z∈(P i).support → z∉(P j).support) (z : V) :
    (pathUnion P).degree z≤2 := by
  by_cases hz : ∃i,z∈(P i).support
  · obtain ⟨i,hi⟩:=hz
    rw [degree_eq_of_mem_support P hdis i hi]
    exact degree_le_two (P i) (hp i) z
  · rw [pathUnion_degree_outside P (by simpa only [not_exists] using hz)]
    omega

theorem pathUnion_degree_start (P : ∀i,G.Walk (a i) (b i)) (hp : ∀i,(P i).IsPath)
    (hdis : ∀i j,i≠j → ∀z,z∈(P i).support → z∉(P j).support)
    (i : I) (hi : a i≠b i) : (pathUnion P).degree (a i)=1 := by
  rw [degree_eq_of_mem_support P hdis i (P i).start_mem_support]
  exact degree_start (P i) (hp i) hi

theorem pathUnion_degree_end (P : ∀i,G.Walk (a i) (b i)) (hp : ∀i,(P i).IsPath)
    (hdis : ∀i j,i≠j → ∀z,z∈(P i).support → z∉(P j).support)
    (i : I) (hi : a i≠b i) : (pathUnion P).degree (b i)=1 := by
  rw [degree_eq_of_mem_support P hdis i (P i).end_mem_support]
  exact degree_end (P i) (hp i) hi

theorem pathUnion_degree_internal (P : ∀i,G.Walk (a i) (b i)) (hp : ∀i,(P i).IsPath)
    (hdis : ∀i j,i≠j → ∀z,z∈(P i).support → z∉(P j).support)
    (hcover : ∀z,∃i,z∈(P i).support) (z : V)
    (ha : ∀i,z≠a i) (hb : ∀i,z≠b i) : (pathUnion P).degree z=2 := by
  obtain ⟨i,hi⟩:=hcover z
  rw [degree_eq_of_mem_support P hdis i hi]
  exact degree_internal (P i) (hp i) hi (ha i) (hb i)

/-- A disjoint spanning path family has exactly the requested degree
profile: one at each prescribed end and two everywhere else. -/
theorem pathUnion_degree_eq (P : ∀i,G.Walk (a i) (b i)) (hp : ∀i,(P i).IsPath)
    (hdis : ∀i j,i≠j → ∀z,z∈(P i).support → z∉(P j).support)
    (hcover : ∀z,∃i,z∈(P i).support) (hab : ∀i,a i≠b i) (z : V) :
    (pathUnion P).degree z=if ∃i,z=a i ∨ z=b i then 1 else 2 := by
  by_cases hz : ∃i,z=a i ∨ z=b i
  · rw [if_pos hz]
    obtain ⟨i,hi⟩:=hz
    rcases hi with rfl|rfl
    · exact pathUnion_degree_start P hp hdis i (hab i)
    · exact pathUnion_degree_end P hp hdis i (hab i)
  · rw [if_neg hz]
    exact pathUnion_degree_internal P hp hdis hcover z
      (fun i he => hz ⟨i,Or.inl he⟩) (fun i he => hz ⟨i,Or.inr he⟩)

theorem walk_edges_in_one_path (P : ∀i,G.Walk (a i) (b i))
    (hdis : ∀i j,i≠j → ∀z,z∈(P i).support → z∉(P j).support)
    (i : I) {z w : V} (p : (pathUnion P).Walk z w) (hz : z∈(P i).support) :
    ∀e∈p.edges,e∈(pathGraph (P i)).edgeSet := by
  induction p with
  | nil => simp
  | @cons z w t hzw p ih =>
    have hedge := (pathUnion_adj_iff_of_mem_support P hdis i hz).mp hzw
    have hw : w∈(P i).support := mem_support_of_adj (P i) hedge.symm
    intro e he
    simp only [Walk.edges_cons,List.mem_cons] at he
    rcases he with rfl|he
    · exact hedge
    · exact ih hw e he

theorem pathUnion_isAcyclic (P : ∀i,G.Walk (a i) (b i)) (hp : ∀i,(P i).IsPath)
    (hdis : ∀i j,i≠j → ∀z,z∈(P i).support → z∉(P j).support) :
    (pathUnion P).IsAcyclic := by
  intro z c hc
  obtain ⟨i,hi⟩:=pathUnion_adj_iff P |>.mp (c.adj_snd hc.not_nil)
  have hz : z∈(P i).support := mem_support_of_adj (P i) hi
  have he := walk_edges_in_one_path P hdis i c hz
  exact isAcyclic (P i) (hp i) (c.transfer (pathGraph (P i)) he) (hc.transfer he)

end Family
end OverfullWork.PathGraphRealization
