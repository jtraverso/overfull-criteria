module

public import OverfullWork.WeakVALSmallCentreExclusion
public import OverfullWork.SecondLowTerminalExclusion

@[expose] public section


/-! A degree-sum-violating edge lies in no common-Delta critical copy.
Deleting this actual edge preserves the palette obstruction and Delta. -/
namespace OverfullWork.WeakVALSingleEdgeDeletion
open SimpleGraph Finset
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
attribute [-instance] SimpleGraph.instDecidableRelAdjDeleteEdgesOfDecidablePredSym2MemSetOfDecidableEq
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

theorem colourable_iff_delete (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    (hBad : G.degree u+G.degree v ≤ G.maxDegree+1) :
    G.EdgeColorable G.maxDegree ↔ (G.deleteEdges {s(u,v)}).EdgeColorable G.maxDegree := by
  apply CriticalCapture.colourable_iff_of_critical_capture (deleteEdges_le _)
  intro c
  let f : c.graph →g G.deleteEdges {s(u,v)} :=
    { toFun := c.embedding
      map_rel' := by
        intro a b hab
        refine deleteEdges_adj.mpr ⟨c.embedding.toHom.map_adj hab,?_⟩
        intro he
        have he' : s(c.embedding a,c.embedding b)=s(u,v) := by simpa using he
        have hVal := Overfull.deg_add c.critical hab
        have hA := c.embedding.degree_le a
        have hB := c.embedding.degree_le b
        have hMax := c.maxDegree_eq
        rcases Sym2.eq_iff.mp he' with ⟨ha,hb⟩|⟨ha,hb⟩
        · rw [ha] at hA;rw [hb] at hB;omega
        · rw [ha] at hA;rw [hb] at hB;omega }
  exact ⟨f.toCopy c.embedding.injective⟩

theorem degree_delete_add (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (hEdge : G.Adj u v) (w : V) :
    (G.deleteEdges {s(u,v)}).degree w+(if w=u ∨ w=v then 1 else 0)=G.degree w := by
  have hLe : edge u v ≤ G := by
    intro a b hab
    rw [edge_adj] at hab
    rcases hab.1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hEdge
    · exact hEdge.symm
  have hEq : G.deleteEdges {s(u,v)}=G\edge u v := by
    ext a b
    simp only [deleteEdges_adj,sdiff_adj,edge_adj,Set.mem_singleton_iff,Sym2.eq_iff]
    have hh : G.Adj a b → a ≠ b := fun h => h.ne
    tauto
  have hId := MaximumMatching.degree_sdiff_add_of_le G (edge u v) hLe w
  have hEdgeDegree := DegreeTwoRealization.degree_edge_exact u v w hEdge.ne
  simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hId hEdgeDegree ⊢
  rw [hEq]
  omega

theorem preserved_obstruction (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    (hBad : G.degree u+G.degree v ≤ G.maxDegree+1)
    (hNC : ¬G.EdgeColorable G.maxDegree) (hNo : ¬G.HasOverfullSubgraph) :
    (G.deleteEdges {s(u,v)}).maxDegree=G.maxDegree ∧
    ¬(G.deleteEdges {s(u,v)}).EdgeColorable (G.deleteEdges {s(u,v)}).maxDegree ∧
    ¬(G.deleteEdges {s(u,v)}).HasOverfullSubgraph := by
  have hNCPalette : ¬(G.deleteEdges {s(u,v)}).EdgeColorable G.maxDegree :=
    fun h => hNC ((colourable_iff_delete G u v hBad).mpr h)
  have hMax := Critical.maxDegree_eq_of_obstruction (deleteEdges_le (G:=G) _) hNCPalette
  exact ⟨hMax,by rwa [hMax],Critical.no_overfull_of_copy (Copy.ofLE _ G (deleteEdges_le _)) hMax hNo⟩

end OverfullWork.WeakVALSingleEdgeDeletion
