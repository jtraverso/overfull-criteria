module

public import OverfullWork.ClassTwoRoundBudget

@[expose] public section


/-! # Constructed matching and cleanup without source criticality

The source is only class two. The input consists of actual cut geometry
and the local inequalities restored by Algorithm 2. The light-pair bound
and two active complementary vertices are explicit requirements; they
are not inferred automatically for the output of a previous round.
No no-overfull preservation is assumed or asserted in this constructor.
-/
namespace OverfullWork.ClassTwoCleanupRound
open SimpleGraph Finset OddCutDeficit ClassTwoMatchingRound
open PaperTopDegreeMatching
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem residue_complement_nonmaximum (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hNonmax : ∀w∈Xᶜ,G.degree w<G.maxDegree)
    (hPairs : ∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2)
    {x y z : V} (hD : 4≤G.maxDegree) (hTop : IsTopPair G Xᶜ y z)
    (r : CoreRound G X x y z) :
    ∀w∈Xᶜ,(G\r.matching).degree w<(G\r.matching).maxDegree := by
  have hLight:=hPairs y hTop.left_mem z hTop.right_mem hTop.ne
  have hZY:=hTop.maximum z hTop.right_mem
  have hSecond:G.degree z+2≤G.maxDegree:=by omega
  intro w hw
  have hSum:(G\r.matching).degree w+r.matching.degree w=G.degree w:=by
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original w
  rw [r.complementary_degrees w hw] at hSum
  rw [r.residual_maxDegree]
  by_cases hSelected:w=y ∨ w=z
  · rw [if_pos hSelected] at hSum
    have hOld:=hNonmax w hw
    omega
  · rw [if_neg hSelected] at hSum
    have hWZ:=hTop.second w hw (fun he=>hSelected (Or.inl he))
    omega

structure CleanRound (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) where
  anchor : V
  left : V
  right : V
  anchor_mem : anchor∈X
  anchor_nonmaximum : G.degree anchor<G.maxDegree
  top : IsTopPair G Xᶜ left right
  round : CoreRound G X anchor left right
  source_independent : G.IsIndepSet (↑(Xᶜ):Set V)
  graph : SimpleGraph V
  deletion : MaximumNeighbourCleanup.DeletionRun Xᶜ (G\round.matching) graph
  le_residue : graph≤G\round.matching
  maximum : graph.maxDegree=G.maxDegree-1
  uncolourable : ¬graph.EdgeColorable graph.maxDegree
  core : graph.induce (X:Set V)=(G\round.matching).induce (X:Set V)
  complement_nonmaximum : ∀w∈Xᶜ,graph.degree w<graph.maxDegree
  maximum_neighbour_inequality : ∀w∈Xᶜ,∀v,graph.Adj w v →
    graph.maxDegree+1 ≤ graph.degree w+PrunedCore.neighboursIn graph (MaximumNeighbourCleanup.maximumVertices graph) v
  hall : ∀w∈Xᶜ,∀v,graph.Adj w v → PrunedCore.neighboursIn graph Xᶜ v<graph.degree w
  weak_VAL : ∀w∈Xᶜ,∀v,graph.Adj w v → graph.maxDegree+2≤graph.degree w+graph.degree v

theorem exists_clean_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNC : ¬G.EdgeColorable G.maxDegree) (X : Finset V) (hOdd : Odd X.card)
    (hInd : G.IsIndepSet (↑(Xᶜ):Set V))
    (hHall : ∀w∈Xᶜ,∀v,G.Adj w v → PrunedCore.neighboursIn G Xᶜ v<G.degree w)
    (hNonmax : ∀w∈Xᶜ,G.degree w<G.maxDegree)
    (hPairs : ∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2)
    (hD : 4≤G.maxDegree) (x : V) (hx : x∈X) (hxD : G.degree x<G.maxDegree) (b : ℕ)
    (hHigh : ∀v∈X,v≠x → G.maxDegree≤G.degree v+b)
    (hMargin : Fintype.card V+2*b+Xᶜ.card+3≤2*G.maxDegree)
    (hActive : 2≤(Xᶜ.filter fun w=>0<G.degree w).card) :
    ∃s : CleanRound G X,s.anchor=x := by
  classical
  have hTwo:2≤Xᶜ.card:=hActive.trans (card_le_card (filter_subset _ _))
  obtain ⟨y,z,hTop⟩:=exists_top_pair G Xᶜ hTwo
  obtain ⟨hyPos,hzPos⟩:=ClassTwoHallMatching.top_pair_positive G Xᶜ hTop hActive
  obtain ⟨r⟩:=ClassTwoMatchingRound.exists_round G hNC X hOdd hInd hHall hNonmax
    x hx hxD b hHigh hMargin y z hTop.left_mem hTop.right_mem hTop.ne hyPos hzPos
  have hNonmaxR:=residue_complement_nonmaximum G X hNonmax hPairs hD hTop r
  obtain ⟨H,hRun,hLe,hMax,hNC',hCore,hNonmaxH,hFinal,hHallH,hValH⟩:=
    MaximumNeighbourCleanup.exists_cleanup_ready (G\r.matching) r.residual_uncolourable Xᶜ hNonmaxR
  have hX:((↑(Xᶜ):Set V)ᶜ)=(X:Set V):=by
    ext v
    simp only [Set.mem_compl_iff,mem_coe,mem_compl,not_not]
  rw [hX] at hCore
  exact ⟨⟨x,y,z,hx,hxD,hTop,r,hInd,H,hRun,hLe,hMax.trans r.residual_maxDegree,
    hNC',hCore,hNonmaxH,hFinal,hHallH,hValH⟩,rfl⟩

theorem CleanRound.budget_drop_three {G : SimpleGraph V} [DecidableRel G.Adj]
    {X : Finset V} (s : CleanRound G X) :
    (deficitMass s.graph s.graph.maxDegree X+(∑w∈Xᶜ,s.graph.degree w))+3=
      deficitMass G G.maxDegree X+(∑w∈Xᶜ,G.degree w) := by
  have hMax:s.graph.maxDegree=(G\s.round.matching).maxDegree:=by
    have hr:(G\s.round.matching).maxDegree=G.maxDegree-1:=by
      simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
        ←Nat.card_eq_fintype_card] using s.round.residual_maxDegree
    exact s.maximum.trans hr.symm
  exact s.round.cleaned_budget_drop_three s.anchor_mem s.anchor_nonmaximum
    s.top.left_mem s.top.right_mem s.top.ne s.source_independent s.le_residue s.core hMax

theorem CleanRound.budget_bound_improves_two {G : SimpleGraph V} [DecidableRel G.Adj]
    {X : Finset V} (s : CleanRound G X) (B : ℕ)
    (hBudget : deficitMass G G.maxDegree X+(∑w∈Xᶜ,G.degree w)≤G.maxDegree+B) :
    (deficitMass s.graph s.graph.maxDegree X+(∑w∈Xᶜ,s.graph.degree w))+2≤s.graph.maxDegree+B := by
  have hDrop:=s.budget_drop_three
  have hMax:=s.maximum
  have hPos:G.degree s.anchor<G.maxDegree:=s.anchor_nonmaximum
  omega

/-- Complete Algorithm 2 on an already constructed round. The output
retains that same matching and anchor; it is not a new assumed step. -/
theorem exists_cleanup_for_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hInd : G.IsIndepSet (↑(Xᶜ):Set V))
    (hNonmax : ∀w∈Xᶜ,G.degree w<G.maxDegree)
    (hPairs : ∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2)
    (hD : 4≤G.maxDegree) {x y z : V} (hx : x∈X) (hxD : G.degree x<G.maxDegree)
    (hTop : IsTopPair G Xᶜ y z) (r : CoreRound G X x y z) :
    ∃s : CleanRound G X,s.anchor=x ∧ s.round.matching=r.matching := by
  classical
  have hNonmaxR:=residue_complement_nonmaximum G X hNonmax hPairs hD hTop r
  obtain ⟨H,hRun,hLe,hMax,hNC,hCore,hNonmaxH,hFinal,hHall,hVal⟩:=
    MaximumNeighbourCleanup.exists_cleanup_ready (G\r.matching) r.residual_uncolourable Xᶜ hNonmaxR
  have hX:((↑(Xᶜ):Set V)ᶜ)=(X:Set V):=by
    ext v
    simp only [Set.mem_compl_iff,mem_coe,mem_compl,not_not]
  rw [hX] at hCore
  exact ⟨⟨x,y,z,hx,hxD,hTop,r,hInd,H,hRun,hLe,hMax.trans r.residual_maxDegree,
    hNC,hCore,hNonmaxH,hFinal,hHall,hVal⟩,rfl,rfl⟩

end OverfullWork.ClassTwoCleanupRound
