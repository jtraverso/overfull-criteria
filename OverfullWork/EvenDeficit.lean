module

public import OverfullWork.Gate8D
public import OverfullWork.DegreeTwoRealization

@[expose] public section


/-! # Even-order deficit balance from vertex-deleted overfull tests -/
namespace OverfullWork.EvenDeficit
open SimpleGraph Finset
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem total_even (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hcard : Fintype.card V=2*m) :
    Even (∑ v : V,(G.maxDegree-G.degree v)) := by
  have hh:=MultigraphExtension.total_deficit_identity G
  rw [G.sum_degrees_eq_twice_card_edges,hcard] at hh
  have hprod : 2*m*G.maxDegree=2*(m*G.maxDegree):=by ring
  rw [hprod] at hh
  exact ⟨m*G.maxDegree-G.edgeFinset.card,by omega⟩

/-- Only the sets obtained by deleting a vertex are used in this step. -/
theorem balanced_of_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1≤m) (hcard : Fintype.card V=2*m)
    (hno : ¬G.HasOverfullSubgraph) (v : V) :
    2*(G.maxDegree-G.degree v)≤∑ w : V,(G.maxDegree-G.degree w) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b => Classical.propDecidable (G.Adj a b)))
  let S:=(univ : Finset V).erase v
  have hS : S.card=2*m-1:=by simp [S,hcard]
  have he : Plantholt.eIn G S≤G.maxDegree*(S.card/2) := by
    by_contra hn
    apply hno
    refine ⟨S,?_⟩
    rw [←MultigraphExtension.eIn_eq_edge_filter G S]
    exact Nat.lt_of_not_ge hn
  have hhalf : S.card/2=m-1:=by omega
  rw [hhalf] at he
  have heq:=Plantholt.eIn_erase_add G v
  have htotal:=MultigraphExtension.total_deficit_identity G
  rw [G.sum_degrees_eq_twice_card_edges,hcard] at htotal
  have hprod : 2*m*G.maxDegree=2*(G.maxDegree*(m-1))+2*G.maxDegree := by
    have hsplit : m=(m-1)+1:=by omega
    conv_lhs => rw [hsplit]
    ring
  rw [hprod] at htotal
  have hdeg:=G.degree_le_maxDegree v
  change Plantholt.eIn G S+G.degree v=G.edgeFinset.card at heq
  omega

theorem simple_or_exception (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1≤m) (hcard : Fintype.card V=2*m)
    (hgap : G.maxDegree-G.minDegree≤2) (hno : ¬G.HasOverfullSubgraph) :
    (∃ J : SimpleGraph V,∀ v,J.degree v=G.maxDegree-G.degree v) ∨
      ∃ u v : V,u≠v ∧ ∀ w,G.maxDegree-G.degree w=if w=u ∨ w=v then 2 else 0 := by
  apply DegreeTwoRealization.exists_simple_or_exception
  · intro v
    have hh:=G.minDegree_le_degree v
    omega
  · exact total_even G m hcard
  · exact balanced_of_no_overfull G m hm hcard hno

end OverfullWork.EvenDeficit
