module

public import OverfullWork.ClassTwoMatchingRound

@[expose] public section


/-! # Exact budget transport through a fixed-core cleanup

The budget is the paper's deficiency on X when its complement is
independent. Equal induced cores at equal maximum degree therefore have
equal budgets. Degree loss at a core vertex is bounded by the size of
the complement. No criticality or residual no-overfullness is needed.
-/
namespace OverfullWork.FixedCoreBudgetTransport
open SimpleGraph Finset OddCutDeficit MatchingOddDeficiency
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem inside_neighbours_eq (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (X : Finset V) (hCore : H.induce (X:Set V)=G.induce (X:Set V))
    (v : V) (hv : v∈X) : Plantholt.nbIn H X v=Plantholt.nbIn G X v := by
  have hAdj:∀w∈X,H.Adj v w ↔ G.Adj v w:=by
    intro w hw
    have he:=congrArg (fun J : SimpleGraph (X:Set V)=>J.Adj ⟨v,hv⟩ ⟨w,hw⟩) hCore
    exact iff_of_eq he
  ext w
  simp only [Plantholt.nbIn,mem_filter,mem_neighborFinset]
  by_cases hw:w∈X
  · exact and_congr_left (fun _=>hAdj w hw)
  · simp [hw]

theorem internal_edges_eq (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (X : Finset V) (hCore : H.induce (X:Set V)=G.induce (X:Set V)) :
    internalEdges H X=internalEdges G X := by
  have hG:=sum_inside_degrees G X
  have hH:=sum_inside_degrees H X
  have hSum:=sum_congr (s₁:=X) (s₂:=X) rfl (fun v hv=>congrArg Finset.card (inside_neighbours_eq G H X hCore v hv))
  omega

theorem degree_le_degree_add_complement (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (X : Finset V) (hCore : H.induce (X:Set V)=G.induce (X:Set V))
    (v : V) (hv : v∈X) : G.degree v≤H.degree v+Xᶜ.card := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b=>Classical.propDecidable (G.Adj a b)))
  cases (Subsingleton.elim (inferInstance : DecidableRel H.Adj)
    (fun a b=>Classical.propDecidable (H.Adj a b)))
  have hSub:G.neighborFinset v⊆Plantholt.nbIn G X v∪Xᶜ:=by
    intro w hw
    by_cases hwX:w∈X
    · exact mem_union_left _ (mem_filter.mpr ⟨hw,hwX⟩)
    · exact mem_union_right _ (mem_compl.mpr hwX)
  have hCount:=(card_le_card hSub).trans (card_union_le _ _)
  rw [card_neighborFinset_eq_degree,←inside_neighbours_eq G H X hCore v hv] at hCount
  have hInside:(Plantholt.nbIn H X v).card≤H.degree v:=by
    exact (card_le_card (filter_subset _ _)).trans (by rw [card_neighborFinset_eq_degree])
  omega

omit [Fintype V] [DecidableEq V] in
theorem independent_of_le (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (Y : Finset V) (hInd : G.IsIndepSet (Y:Set V)) (hLe : H≤G) :
    H.IsIndepSet (Y:Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hab hAdj
  exact hInd ha hb hab (hLe hAdj)

theorem budget_eq_of_fixed_core (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (X : Finset V) (hCore : H.induce (X:Set V)=G.induce (X:Set V))
    (hMax : H.maxDegree=G.maxDegree)
    (hGInd : G.IsIndepSet (↑(Xᶜ):Set V)) (hHInd : H.IsIndepSet (↑(Xᶜ):Set V)) :
    deficitMass H H.maxDegree X+(∑w∈Xᶜ,H.degree w)=
      deficitMass G G.maxDegree X+(∑w∈Xᶜ,G.degree w) := by
  have hG:=internal_cut_deficit_identity G G.maxDegree G.degree_le_maxDegree X
  have hH:=internal_cut_deficit_identity H H.maxDegree H.degree_le_maxDegree X
  rw [cut_eq_complementary_degree_sum G X hGInd] at hG
  rw [cut_eq_complementary_degree_sum H X hHInd,hMax,internal_edges_eq G H X hCore] at hH
  rw [hMax]
  omega

/-- A different minimum anchor does not spoil the high-degree bound:
if the old anchor is no longer minimum, the new minimum was already
one of the high vertices, and hence the old anchor is high as well. -/
theorem high_degrees_away_from_minimum (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (x a : V) (ha : a∈X) (b : ℕ)
    (hHigh : ∀v∈X,v≠x → G.maxDegree≤G.degree v+b)
    (hMin : ∀v∈X,G.degree a≤G.degree v) :
    ∀v∈X,v≠a → G.maxDegree≤G.degree v+b := by
  intro v hv hva
  by_cases hvx:v=x
  · subst v
    by_cases hax:a=x
    · exact (hva hax.symm).elim
    · have hh:=hHigh a ha hax
      have hm:=hMin x hv
      omega
  · exact hHigh v hv hvx

end OverfullWork.FixedCoreBudgetTransport
