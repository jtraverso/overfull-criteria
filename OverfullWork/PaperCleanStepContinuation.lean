module

public import OverfullWork.ClassTwoPairBoundTransport

@[expose] public section


/-! # Continuing from the actual globally safe first cleaned graph

Hall, class two and nonmaximum complementary degrees are taken from the
constructed output, not replaced by residual criticality. Induced-core
preservation bounds each core degree loss. A new minimum anchor is
constructed and the next actual matching is obtained, or an explicit
stopping alternative is returned. No second-residue no-overfull theorem
or repeated-operation theorem is asserted here.
-/
namespace OverfullWork.PaperFirstRoundAboveHalf
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open ClassTwoMatchingRound FixedCoreBudgetTransport PaperTopDegreeMatching
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem CleanStep.budget_drop_three {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x : V} (s : CleanStep G c x)
    (hx : x∈c.set) (hxD : G.degree x<G.maxDegree) :
    (deficitMass s.graph s.graph.maxDegree c.set+(∑w∈c.setᶜ,s.graph.degree w))+3=
      deficitMass G G.maxDegree c.set+(∑w∈c.setᶜ,G.degree w) := by
  let r:=CoreRound.ofRound s.round
  have hMax:s.graph.maxDegree=(G\r.matching).maxDegree:=by
    have hr:(G\r.matching).maxDegree=G.maxDegree-1:=by
      simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
        ←Nat.card_eq_fintype_card] using r.residual_maxDegree
    exact s.maximum.trans hr.symm
  have hInd:G.IsIndepSet (↑(c.setᶜ):Set V):=by simpa only [coe_compl] using c.independent
  exact r.cleaned_budget_drop_three hx hxD s.top.left_mem s.top.right_mem s.top.ne
    hInd s.le_residue s.core hMax

theorem CleanStep.budget_bound_improves_two {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x : V} (s : CleanStep G c x)
    (hx : x∈c.set) (hxD : G.degree x<G.maxDegree) :
    (deficitMass s.graph s.graph.maxDegree c.set+(∑w∈c.setᶜ,s.graph.degree w))+2≤s.graph.maxDegree+B := by
  have hDrop:=s.budget_drop_three hx hxD
  have hMax:=s.maximum
  have hBudget:=c.budget
  omega

theorem CleanStep.core_high_degrees {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x : V} (s : CleanStep G c x)
    (hx : x∈c.set) (hLarge : G.degree x<(∑w∈c.setᶜ,G.degree w)) :
    ∀v∈c.set,v≠x → s.graph.maxDegree≤s.graph.degree v+(B+K) := by
  intro v hv hvx
  have hHigh:=PaperTwoCoreRoundPreservation.round_other_degree_lower G c hx hLarge s.round hv hvx
  have hLoss:=degree_le_degree_add_complement (G\s.round.matching) s.graph c.set s.core v hv
  have hY:=c.complement_small
  have hRMax:(G\s.round.matching).maxDegree=G.maxDegree-1:=by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using s.round.residual_maxDegree
  have hMax:=s.maximum
  omega

theorem CleanStep.exists_minimum_anchor {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x : V} (s : CleanStep G c x)
    (hx : x∈c.set) (hLarge : G.degree x<(∑w∈c.setᶜ,G.degree w)) :
    ∃a∈c.set,(∀v∈c.set,s.graph.degree a≤s.graph.degree v) ∧
      ∀v∈c.set,v≠a → s.graph.maxDegree≤s.graph.degree v+(B+K) := by
  obtain ⟨a,ha,hMin⟩:=c.set.exists_min_image (fun v=>s.graph.degree v) ⟨x,hx⟩
  exact ⟨a,ha,hMin,high_degrees_away_from_minimum s.graph c.set x a ha (B+K)
    (s.core_high_degrees hx hLarge) hMin⟩

theorem CleanStep.exists_next_matching {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x : V} (s : CleanStep G c x)
    (hx : x∈c.set) (hLarge : G.degree x<(∑w∈c.setᶜ,G.degree w))
    (a : V) (ha : a∈c.set) (hMin : ∀v∈c.set,s.graph.degree a≤s.graph.degree v)
    (haD : s.graph.degree a<s.graph.maxDegree)
    (hActive : 2≤(c.setᶜ.filter fun w=>0<s.graph.degree w).card)
    (hMargin : Fintype.card V+2*(B+K)+c.setᶜ.card+3≤2*s.graph.maxDegree) :
    ∃y z,IsTopPair s.graph c.setᶜ y z ∧ Nonempty (CoreRound s.graph c.set a y z) := by
  classical
  have hTwo:2≤c.setᶜ.card:=hActive.trans (card_le_card (filter_subset _ _))
  obtain ⟨y,z,hTop⟩:=exists_top_pair s.graph c.setᶜ hTwo
  obtain ⟨hyPos,hzPos⟩:=ClassTwoHallMatching.top_pair_positive s.graph c.setᶜ hTop hActive
  have hIndG:G.IsIndepSet (↑(c.setᶜ):Set V):=by simpa only [coe_compl] using c.independent
  have hInd: s.graph.IsIndepSet (↑(c.setᶜ):Set V):=
    independent_of_le G s.graph c.setᶜ hIndG (s.le_residue.trans sdiff_le)
  have hHigh:=high_degrees_away_from_minimum s.graph c.set x a ha (B+K)
    (s.core_high_degrees hx hLarge) hMin
  exact ⟨y,z,hTop,ClassTwoMatchingRound.exists_round s.graph s.uncolourable c.set c.odd
    hInd s.hall s.complement_nonmaximum a ha haD (B+K) hHigh hMargin y z
    hTop.left_mem hTop.right_mem hTop.ne hyPos hzPos⟩

/-- The next matching is constructed from the SAME actual cleaned
graph. Stop tests are exactly stated on that graph, including the
active complement rather than its possibly isolated ambient vertices. -/
theorem CleanStep.stopping_or_next_matching {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x : V} (s : CleanStep G c x)
    (hx : x∈c.set) (hLarge : G.degree x<(∑w∈c.setᶜ,G.degree w))
    (hMargin : Fintype.card V+2*(B+K)+c.setᶜ.card+3≤2*s.graph.maxDegree) :
    ∃a∈c.set,(∀v∈c.set,s.graph.degree a≤s.graph.degree v) ∧
      ((c.setᶜ.filter fun w=>0<s.graph.degree w).card≤1 ∨
       (∑w∈c.setᶜ,s.graph.degree w)≤s.graph.degree a ∨
       (∃v∈c.set,v≠a ∧ s.graph.degree v≤s.graph.maxDegree-s.graph.degree a) ∨
       (∀v∈c.set,s.graph.degree v=s.graph.maxDegree) ∨
       ∃y z,IsTopPair s.graph c.setᶜ y z ∧ Nonempty (CoreRound s.graph c.set a y z)) := by
  obtain ⟨a,ha,hMin,_⟩:=s.exists_minimum_anchor hx hLarge
  refine ⟨a,ha,hMin,?_⟩
  by_cases hFew:(c.setᶜ.filter fun w=>0<s.graph.degree w).card≤1
  · exact Or.inl hFew
  right
  by_cases hSmall:(∑w∈c.setᶜ,s.graph.degree w)≤s.graph.degree a
  · exact Or.inl hSmall
  right
  by_cases hLow:∃v∈c.set,v≠a ∧ s.graph.degree v≤s.graph.maxDegree-s.graph.degree a
  · exact Or.inl hLow
  right
  by_cases haMax:s.graph.degree a=s.graph.maxDegree
  · left
    intro v hv
    have hLo:=hMin v hv
    have hHi:=s.graph.degree_le_maxDegree v
    omega
  · right
    exact s.exists_next_matching hx hLarge a ha hMin
      (lt_of_le_of_ne (s.graph.degree_le_maxDegree a) haMax) (by omega) hMargin

theorem CleanStep.light_pairs {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x : V} (s : CleanStep G c x)
    (hD : 0<G.maxDegree) (hB : B≤G.maxDegree+1) :
    ∀u∈c.setᶜ,∀v∈c.setᶜ,u≠v → s.graph.degree u+s.graph.degree v<s.graph.maxDegree+2 := by
  have hTotal:(∑w∈c.setᶜ,G.degree w)≤2*G.maxDegree+1:=by have hb:=c.budget;omega
  let r:=CoreRound.ofRound s.round
  intro u hu v hv huv
  have hPair:=r.light_pairs_after_round s.top hD c.light_pairs hTotal u hu v hv huv
  have hULe:=s.graph.degree_le_of_le s.le_residue (v:=u)
  have hVLe:=s.graph.degree_le_of_le s.le_residue (v:=v)
  have hMax:=s.maximum
  have hRMax:=s.round.residual_maxDegree
  change (G\s.round.matching).degree u+(G\s.round.matching).degree v<
    (G\s.round.matching).maxDegree+2 at hPair
  simp only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
    ←Nat.card_eq_fintype_card] at hPair hULe hVLe hMax hRMax ⊢
  omega

/-- Continue through a second ACTUAL cleanup, or return a stated stop.
No-overfullness of the second cleaned graph is still a separate task. -/
theorem CleanStep.stopping_or_next_clean_round {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x : V} (s : CleanStep G c x)
    (hx : x∈c.set) (hLarge : G.degree x<(∑w∈c.setᶜ,G.degree w))
    (hMargin : Fintype.card V+2*(B+K)+c.setᶜ.card+3≤2*s.graph.maxDegree)
    (hB : B≤G.maxDegree+1) (hD : 4≤s.graph.maxDegree) :
    ∃a∈c.set,(∀v∈c.set,s.graph.degree a≤s.graph.degree v) ∧
      ((c.setᶜ.filter fun w=>0<s.graph.degree w).card≤1 ∨
       (∑w∈c.setᶜ,s.graph.degree w)≤s.graph.degree a ∨
       (∃v∈c.set,v≠a ∧ s.graph.degree v≤s.graph.maxDegree-s.graph.degree a) ∨
       (∀v∈c.set,s.graph.degree v=s.graph.maxDegree) ∨
       ∃t : ClassTwoCleanupRound.CleanRound s.graph c.set,t.anchor=a) := by
  obtain ⟨a,ha,hMin,hCases⟩:=s.stopping_or_next_matching hx hLarge hMargin
  refine ⟨a,ha,hMin,?_⟩
  rcases hCases with hFew|hSmall|hLow|hMax|hRound
  · exact Or.inl hFew
  · exact Or.inr (Or.inl hSmall)
  · exact Or.inr (Or.inr (Or.inl hLow))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hMax)))
  · obtain ⟨y,z,hTop,⟨r⟩⟩:=hRound
    have hA:=r.anchor_degree_eq ha
    have hBound:=(s.graph\r.matching).degree_le_maxDegree a
    have hMaxR:=r.residual_maxDegree
    have haD:s.graph.degree a<s.graph.maxDegree:=by
      simp only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
        ←Nat.card_eq_fintype_card] at hA hBound hMaxR hD ⊢
      omega
    have hPos:0<G.maxDegree:=by have hh:=s.maximum;omega
    have hIndG:G.IsIndepSet (↑(c.setᶜ):Set V):=by simpa only [coe_compl] using c.independent
    have hInd:s.graph.IsIndepSet (↑(c.setᶜ):Set V):=
      independent_of_le G s.graph c.setᶜ hIndG (s.le_residue.trans sdiff_le)
    obtain ⟨t,hta,_⟩:=ClassTwoCleanupRound.exists_cleanup_for_round s.graph c.set hInd
      s.complement_nonmaximum (s.light_pairs hPos hB) hD ha haD hTop r
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t,hta⟩)))

end OverfullWork.PaperFirstRoundAboveHalf
