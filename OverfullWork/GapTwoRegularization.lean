module

public import OverfullWork.DeficitCompletion
public import OverfullWork.AlternatingFive

@[expose] public section


/-! # Regularization of odd degree-gap-two graphs below the edge bound

The old-vertex additions are a simple graph of maximum degree two.
They may overlap G; the resulting parallel excess is bounded explicitly.
-/
namespace OverfullWork.MultigraphExtension
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_bounded_parallel_extension (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hcard : Fintype.card V+1=2*m) (hgap : G.maxDegree-G.minDegree≤2)
    (hedge : 2*G.edgeFinset.card≤G.maxDegree*(Fintype.card V-1))
    (hD : 6≤G.maxDegree) :
    ∃ M : MultiGraph (Option V),M.IsRegularOfDegree G.maxDegree ∧
      (∀ e,M.mult e≤2) ∧ M.HasParallelBudget none 3 ∧
      ∀ u v,G.Adj u v → 1≤M.mult s(some u,some v) := by
  classical
  let D:=G.maxDegree
  let a : V → ℕ:=fun v => D-G.degree v
  let cap:=D*(m-1)
  let q:=cap-G.edgeFinset.card
  have hm : 1≤m:=by omega
  have hn : Fintype.card V=2*(m-1)+1:=by omega
  have htwocap : 2*cap=D*(Fintype.card V-1) := by
    rw [hn]
    simp only [Nat.add_sub_cancel]
    dsimp [cap]
    ring
  have hsplit : Fintype.card V*D=2*cap+D := by
    rw [hn]
    dsimp [cap]
    ring
  have hcap : G.edgeFinset.card≤cap := by
    change 2*G.edgeFinset.card≤D*(Fintype.card V-1) at hedge
    rw [←htwocap] at hedge
    omega
  have hq : G.edgeFinset.card+q=cap:=Nat.add_sub_of_le hcap
  have ha : ∀ v,a v≤2 := by
    intro v
    have hmin:=G.minDegree_le_degree v
    dsimp [a,D]
    omega
  have htotal : (∑ v : V,a v)=2*q+D := by
    have hh:=total_deficit_identity G
    rw [G.sum_degrees_eq_twice_card_edges] at hh
    change 2*G.edgeFinset.card+(∑ v : V,a v)=Fintype.card V*D at hh
    omega
  obtain ⟨J,hJcap,hJq⟩:=CapacityPacking.exists_packing a ha q (by rw [htotal];change 2*q+6≤2*q+D;omega)
  let B:=(MultiGraph.ofSimpleGraph G).addCopies (MultiGraph.ofSimpleGraph J)
  have hBdeg : ∀ v,B.degree v=G.degree v+J.degree v := by
    intro v
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_ofSimpleGraph,MultiGraph.degree_ofSimpleGraph]
  have hBupper : ∀ v,B.degree v≤D := by
    intro v
    rw [hBdeg]
    have hh:=hJcap v
    have hg:=G.degree_le_maxDegree v
    dsimp [a,D] at *
    omega
  have hBdef : ∀ v,D-B.degree v≤2 := by
    intro v
    have hh:=ha v
    rw [hBdeg]
    dsimp [a] at hh
    omega
  have hBcount : B.edgeCount=cap := by
    rw [MultiGraph.edgeCount_addCopies,MultiGraph.edgeCount_ofSimpleGraph,MultiGraph.edgeCount_ofSimpleGraph]
    rw [←Saturation.edges_ncard J,hJq]
    exact hq
  have hBsum : (∑ v : V,(D-B.degree v))=D := by
    have hh:=B.total_deficit_of_bounded D hBupper
    rw [B.sum_degrees_eq_twice_edgeCount,hBcount] at hh
    omega
  have hBmu : ∀ e,B.mult e≤2 := by
    intro e
    change (if e∈G.edgeSet then 1 else 0)+(if e∈J.edgeSet then 1 else 0)≤2
    split_ifs <;> omega
  have hBparallel : ∀ v,B.parallelExcess v≤2 := by
    intro v
    have hp : ∀ w,B.mult s(v,w)-1≤(MultiGraph.ofSimpleGraph J).mult s(v,w) := by
      intro w
      change (if s(v,w)∈G.edgeSet then 1 else 0)+(if s(v,w)∈J.edgeSet then 1 else 0)-1≤
        (if s(v,w)∈J.edgeSet then 1 else 0)
      split_ifs <;> omega
    have hs:=sum_le_sum (s:=univ) (fun w _ => hp w)
    rw [←MultiGraph.degree_eq_sum_mult,MultiGraph.degree_ofSimpleGraph] at hs
    exact hs.trans ((hJcap v).trans (ha v))
  refine ⟨B.deficitExtension D,B.deficitExtension_regular D hBupper hBsum,
    B.deficitExtension_multiplicity D hBmu hBdef,B.deficitExtension_parallel_budget D hBdef hBparallel,?_⟩
  intro u v huv
  rw [MultiGraph.deficitExtension_mult]
  change 1≤(MultiGraph.ofSimpleGraph G).mult s(u,v)+(MultiGraph.ofSimpleGraph J).mult s(u,v)
  have hg : (MultiGraph.ofSimpleGraph G).mult s(u,v)=1 := by
    simp only [MultiGraph.ofSimpleGraph,SimpleGraph.mem_edgeSet,if_pos huv]
  rw [hg]
  omega

/-- Restriction needs only original-edge containment, not a particular
one-point multiplicity formula. -/
theorem edgeColourable_of_regularized_colouring (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : MultiGraph (Option V)) {k : ℕ} (C : M.EdgeColoring k)
    (hcontains : ∀ u v,G.Adj u v → 1≤M.mult s(some u,some v)) : G.EdgeColorable k := by
  classical
  have hc : ∀ e∈(OddOrder.pointExtend G ∅).edgeSet,1≤M.mult e := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      cases u with
      | none => cases v <;> simp [OddOrder.pointExtend] at he
      | some u =>
        cases v with
        | none => simp [OddOrder.pointExtend] at he
        | some v => exact hcontains u v he
  have hcol:=MultiGraph.edgeColourable_of_contained M (OddOrder.pointExtend G ∅) hc C
  exact Critical.colourable_of_copy (OddOrder.intoExtension G ∅) hcol

end OverfullWork.MultigraphExtension
