module

public import OverfullWork.PaperPairExtensionPreservation

@[expose] public section


/-! # Induced edge counts for the exchange in CMS Claim 4.5

The insert/erase identities count actual induced edges. They support the
paper's final (1,1) exchange without assuming an edge-count comparison.
-/
namespace OverfullWork.InducedEdgeExchange
open SimpleGraph Finset OddCutDeficit
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

theorem row_sum_eq_neighbours (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (v : V) :
    (∑w∈S,(MultiGraph.ofSimpleGraph H).mult s(v,w))=(Plantholt.nbIn H S v).card := by
  have hEq:Plantholt.nbIn H S v=S.filter (H.Adj v):=by
    ext w
    simp only [Plantholt.nbIn,mem_filter,mem_neighborFinset]
    tauto
  rw [hEq,card_eq_sum_ones,sum_filter]
  simp only [MultiGraph.ofSimpleGraph,mem_edgeSet]

omit [Fintype V] in
theorem twice_internal_insert (M : MultiGraph V) (S : Finset V) (v : V) (hv : v∉S) :
    M.twiceInternal (insert v S)=M.twiceInternal S+2*(∑w∈S,M.mult s(v,w)) := by
  have hSym:(∑w∈S,M.mult s(w,v))=∑w∈S,M.mult s(v,w):=by
    apply sum_congr rfl
    intro w _
    rw [Sym2.eq_swap]
  unfold MultiGraph.twiceInternal
  rw [sum_insert hv]
  simp_rw [sum_insert hv]
  rw [M.loopless s(v,v) (by simp),Nat.zero_add,sum_add_distrib,hSym]
  omega

theorem internal_edges_insert (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (v : V) (hv : v∉S) :
    internalEdges H (insert v S)=internalEdges H S+(Plantholt.nbIn H S v).card := by
  have hCount:=twice_internal_insert (MultiGraph.ofSimpleGraph H) S v hv
  rw [MultiGraph.twiceInternal_eq,MultiGraph.twiceInternal_eq,
    ←internalEdges_eq_multigraph,←internalEdges_eq_multigraph,row_sum_eq_neighbours] at hCount
  omega

theorem inside_erase_self (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (v : V) : Plantholt.nbIn H (S.erase v) v=Plantholt.nbIn H S v := by
  ext w
  simp only [Plantholt.nbIn,mem_filter,mem_neighborFinset,mem_erase]
  constructor
  · exact fun h=>⟨h.1,h.2.2⟩
  · intro h
    exact ⟨h.1,(H.ne_of_adj h.1).symm,h.2⟩

theorem internal_edges_erase_add (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (v : V) (hv : v∈S) :
    internalEdges H (S.erase v)+(Plantholt.nbIn H S v).card=internalEdges H S := by
  have hCount:=internal_edges_insert H (S.erase v) v (notMem_erase v S)
  rw [insert_erase hv,inside_erase_self] at hCount
  exact hCount.symm

theorem internal_edges_exchange (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (u v : V) (hu : u∈S) (hv : v∉S) :
    internalEdges H (insert v (S.erase u))+(Plantholt.nbIn H S u).card=
      internalEdges H S+(Plantholt.nbIn H (S.erase u) v).card := by
  have hv':v∉S.erase u:=fun h=>hv (mem_erase.mp h).2
  have hInsert:=internal_edges_insert H (S.erase u) v hv'
  have hErase:=internal_edges_erase_add H S u hu
  omega

theorem inside_degree_erase_add (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (u v : V) (hu : u∈S) :
    (Plantholt.nbIn H (S.erase u) v).card+(if H.Adj v u then 1 else 0)=
      (Plantholt.nbIn H S v).card := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel H.Adj)
    (fun a b=>Classical.propDecidable (H.Adj a b)))
  have hEq:Plantholt.nbIn H (S.erase u) v=(Plantholt.nbIn H S v).erase u:=by
    ext w
    simp only [Plantholt.nbIn,mem_filter,mem_neighborFinset,mem_erase]
    tauto
  rw [hEq]
  by_cases hAdj:H.Adj v u
  · have huN:u∈Plantholt.nbIn H S v:=mem_filter.mpr
      ⟨(mem_neighborFinset H v u).mpr hAdj,hu⟩
    rw [if_pos hAdj,card_erase_of_mem huN]
    have hp:0<(Plantholt.nbIn H S v).card:=card_pos.mpr ⟨u,huN⟩
    omega
  · have huN:u∉Plantholt.nbIn H S v:=by
      intro hh
      exact hAdj ((mem_neighborFinset H v u).mp (mem_filter.mp hh).1)
    rw [if_neg hAdj,erase_eq_of_notMem huN,Nat.add_zero]

theorem inside_degree_eq_of_neighbours_inside (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (v : V) (hInside : ∀w,H.Adj v w → w∈S) :
    (Plantholt.nbIn H S v).card=H.degree v := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel H.Adj)
    (fun a b=>Classical.propDecidable (H.Adj a b)))
  have hEq:Plantholt.nbIn H S v=H.neighborFinset v:=by
    unfold Plantholt.nbIn
    apply filter_eq_self.mpr
    intro w hw
    exact hInside w ((mem_neighborFinset H v w).mp hw)
  rw [hEq,card_neighborFinset_eq_degree]

theorem inside_degree_add_outside_edge_le (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (u v : V) (hv : v∉S) :
    (Plantholt.nbIn H S u).card+(if H.Adj u v then 1 else 0)≤H.degree u := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel H.Adj)
    (fun a b=>Classical.propDecidable (H.Adj a b)))
  by_cases hAdj:H.Adj u v
  · rw [if_pos hAdj]
    have hvN:v∉Plantholt.nbIn H S u:=by intro hh;exact hv (mem_filter.mp hh).2
    have hSub:insert v (Plantholt.nbIn H S u)⊆H.neighborFinset u:=by
      intro w hw
      rcases mem_insert.mp hw with he|hw
      · exact he.symm ▸ (mem_neighborFinset H u v).mpr hAdj
      · exact (mem_filter.mp hw).1
    have hc:=card_le_card hSub
    rw [card_insert_of_notMem hvN,card_neighborFinset_eq_degree] at hc
    omega
  · rw [if_neg hAdj,Nat.add_zero]
    exact (card_le_card (filter_subset _ _)).trans (by rw [card_neighborFinset_eq_degree])

/-- The final exchange in Claim 4.5: an outside vertex with all its
neighbours inside S can replace a lower-degree vertex without losing
induced edges. The comparison is proved from the actual neighbourhoods. -/
theorem exchange_internal_edges_mono (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (u v : V) (hu : u∈S) (hv : v∉S)
    (hDegree : H.degree u≤H.degree v) (hInside : ∀w,H.Adj v w → w∈S) :
    internalEdges H S ≤ internalEdges H (insert v (S.erase u)) := by
  have hExchange:=internal_edges_exchange H S u v hu hv
  have hSplit:=inside_degree_erase_add H S u v hu
  have hOutside:=inside_degree_add_outside_edge_le H S u v hv
  rw [inside_degree_eq_of_neighbours_inside H S v hInside] at hSplit
  have hSym:(if H.Adj v u then 1 else 0)=(if H.Adj u v then 1 else 0):=by
    simp only [H.adj_comm]
  rw [hSym] at hSplit
  omega

theorem exchange_transfers_overfull (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (u v : V) (hu : u∈S) (hv : v∉S)
    (hDegree : H.degree u≤H.degree v) (hInside : ∀w,H.Adj v w → w∈S)
    (hOdd : Odd S.card) (hOF : H.maxDegree*(S.card/2) < internalEdges H S) :
    Odd (insert v (S.erase u)).card ∧
      H.maxDegree*((insert v (S.erase u)).card/2) < internalEdges H (insert v (S.erase u)) := by
  have hv':v∉S.erase u:=fun hh=>hv (mem_erase.mp hh).2
  have hCard:(insert v (S.erase u)).card=S.card:=by
    rw [card_insert_of_notMem hv',card_erase_of_mem hu]
    have hp:0<S.card:=card_pos.mpr ⟨u,hu⟩
    omega
  have hMon:=exchange_internal_edges_mono H S u v hu hv hDegree hInside
  rw [hCard]
  exact ⟨hOdd,hOF.trans_le hMon⟩

end OverfullWork.InducedEdgeExchange
