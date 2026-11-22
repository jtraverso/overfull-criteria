module

public import OverfullWork.JointCutNormalization
public import OverfullWork.ClassTwoGlobalNoOverfull

@[expose] public section


/-! # A globally safe normalized class-two step

After a genuine matching/cleanup round, joint normalization restores
both degree order and full maximum-neighbour readiness. The core may
change, so this is a normalized variant, not a claim to have retained
the fixed-core history in CMS Operation 4.2. All source and target graphs,
cuts, matchings and no-overfull proofs are constructed explicitly.
-/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset OddCutDeficit MatchingOddDeficiency NormalizedAlmostStoppingRun
open CleanedSourceVAL FixedCoreBudgetTransport
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
set_option maxHeartbeats 10000000

structure State (V : Type*) [Fintype V] [DecidableEq V] (B K : ℕ) where
  graph : SimpleGraph V
  cut : Certificate graph B K
  ready : IsReady graph cut.setᶜ
  uncolourable : ¬graph.EdgeColorable graph.maxDegree
  no_overfull : ¬graph.HasOverfullSubgraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def Margins {B K : ℕ} (s : State V B K) : Prop :=
  Fintype.card V+2*B+K+3≤2*s.graph.maxDegree ∧
  Fintype.card V+B+K+5≤2*s.graph.maxDegree ∧
  4*(B+K+2)+1≤s.graph.maxDegree

def Terminal {B K : ℕ} (s : State V B K) : Prop :=
  (∀x∈s.cut.set,(∑y∈s.cut.setᶜ,s.graph.degree y)≤s.graph.degree x) ∨
  ((∀v∈s.cut.set,s.graph.degree v=s.graph.maxDegree) ∧
    s.graph.maxDegree<(∑y∈s.cut.setᶜ,s.graph.degree y)) ∨
  ∃x∈s.cut.set,(∀v∈s.cut.set,s.graph.degree x≤s.graph.degree v) ∧
    s.graph.degree x<(∑y∈s.cut.setᶜ,s.graph.degree y) ∧
    ∃v∈s.cut.set,v≠x ∧ s.graph.degree v≤s.graph.maxDegree-s.graph.degree x ∧
      s.graph.IsIndepSet (↑(insert x s.cut.setᶜ):Set V)

structure Step {B K : ℕ} (s : State V B K) where
  round : ClassTwoCleanupRound.CleanRound s.graph s.cut.set
  round_no_overfull : ¬round.graph.HasOverfullSubgraph
  next : State V (B-2) K
  budget_parameter_positive : 2≤B
  next_le_round : next.graph≤round.graph
  maximum : next.graph.maxDegree+1=s.graph.maxDegree
  complement_card : next.cut.setᶜ.card=s.cut.setᶜ.card
  budget_decreases :
    (deficitMass next.graph next.graph.maxDegree next.cut.set+
      (∑v∈next.cut.setᶜ,next.graph.degree v))+3≤
      deficitMass s.graph s.graph.maxDegree s.cut.set+(∑v∈s.cut.setᶜ,s.graph.degree v)

theorem exists_step {B K : ℕ} (s : State V B K) (hM : Margins s)
    (x : V) (hx : x∈s.cut.set) (hxD : s.graph.degree x<s.graph.maxDegree)
    (hLarge : s.graph.degree x<(∑v∈s.cut.setᶜ,s.graph.degree v))
    (hNonstop : ∀v∈s.cut.set,v≠x → s.graph.maxDegree<s.graph.degree x+s.graph.degree v) :
    Nonempty (Step s) := by
  rcases hM with ⟨hMatch,hDense,hSmall⟩
  have hY:=s.cut.complement_small
  obtain ⟨r,_,hNoH⟩:=ClassTwoGlobalNoOverfull.exists_safe_clean_round s.graph s.uncolourable s.cut
    s.ready s.no_overfull x hx hxD hLarge hNonstop (by omega) hDense hSmall
  have hIndH:r.graph.IsIndepSet (↑(s.cut.setᶜ):Set V):=
    independent_of_le s.graph r.graph s.cut.setᶜ r.source_independent (r.le_residue.trans sdiff_le)
  have hLower:r.graph.maxDegree≤deficitMass r.graph r.graph.maxDegree s.cut.set+
      (∑v∈s.cut.setᶜ,r.graph.degree v):=by
    have hh:=(no_overfull_iff_odd_cut_deficit r.graph).mp hNoH s.cut.set s.cut.odd
    rw [cut_eq_complementary_degree_sum r.graph s.cut.set hIndH] at hh
    omega
  have hImproved:=r.budget_bound_improves_two B s.cut.budget
  have hB:2≤B:=by omega
  have hBudgetH:deficitMass r.graph r.graph.maxDegree s.cut.set+
      (∑v∈s.cut.setᶜ,r.graph.degree v)≤r.graph.maxDegree+(B-2):=by omega
  have hTotal:(∑v∈s.cut.setᶜ,s.graph.degree v)≤2*s.graph.maxDegree+1:=by
    have hb:=s.cut.budget
    omega
  have hPairsH:=r.light_pairs s.cut.light_pairs hTotal
  obtain ⟨H,hLe,hMax,hNC,hNo,c,hCard,hReady,hBudget⟩:=
    JointCutNormalization.exists_joint_normalization r.graph r.uncolourable hNoH s.cut.set s.cut.odd
      (B-2) K hY hIndH r.complement_nonmaximum hPairsH hBudgetH
  let t : State V (B-2) K:=⟨H,c,hReady,hNC,hNo⟩
  have hMaxStep:t.graph.maxDegree+1=s.graph.maxDegree:=by
    have hr:=r.maximum
    change H.maxDegree+1=s.graph.maxDegree
    omega
  have hDrop:=r.budget_drop_three
  have hBudgetStep:(deficitMass t.graph t.graph.maxDegree t.cut.set+
      (∑v∈t.cut.setᶜ,t.graph.degree v))+3≤
      deficitMass s.graph s.graph.maxDegree s.cut.set+(∑v∈s.cut.setᶜ,s.graph.degree v):=by
    change (deficitMass H H.maxDegree c.set+(∑v∈c.setᶜ,H.degree v))+3≤_
    omega
  exact ⟨⟨r,hNoH,t,hB,hLe,hMaxStep,hCard,hBudgetStep⟩⟩

theorem enlarged_independent_of_second_low (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hReady : IsReady G c.setᶜ)
    {x v : V} (hx : x∈c.set) (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y))
    (hv : v∈c.set) (hvx : v≠x) (hLow : G.degree v≤G.maxDegree-G.degree x)
    (hSmall : 2*B<G.maxDegree+2) : G.IsIndepSet (↑(insert x c.setᶜ):Set V) := by
  have hBound:=LargeCentreCriticalGeometry.anchor_degree_add_excess_le G c hx hLarge hv hvx hLow
  have hxB:G.degree x≤B:=by omega
  have hYB:∀y∈c.setᶜ,G.degree y≤B:=by intro y hy;exact (c.ordered y hy x hx).trans hxB
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hab hAdj
  rcases mem_insert.mp ha with he|ha
  · subst a
    rcases mem_insert.mp hb with he|hb
    · exact hab he.symm
    · have hVal:=weak_VAL G c.setᶜ hReady b hb x hAdj.symm
      have hB:=hYB b hb
      omega
  · rcases mem_insert.mp hb with he|hb
    · subst b
      have hVal:=weak_VAL G c.setᶜ hReady a ha x hAdj
      have hB:=hYB a ha
      omega
    · exact c.independent (mem_compl.mp ha) (mem_compl.mp hb) hab hAdj

theorem terminal_or_step {B K : ℕ} (s : State V B K) (hM : Margins s) :
    Terminal s ∨ Nonempty (Step s) := by
  have hNonempty:s.cut.set.Nonempty:=by
    apply card_pos.mp
    obtain ⟨k,hk⟩:=s.cut.odd
    omega
  obtain ⟨x,hx,hMin⟩:=s.cut.set.exists_min_image (fun v=>s.graph.degree v) hNonempty
  by_cases hSmall:(∑y∈s.cut.setᶜ,s.graph.degree y)≤s.graph.degree x
  · left
    exact Or.inl (fun v hv=>hSmall.trans (hMin v hv))
  have hLarge:s.graph.degree x<(∑y∈s.cut.setᶜ,s.graph.degree y):=by omega
  by_cases hxMax:s.graph.degree x=s.graph.maxDegree
  · left
    apply Or.inr ∘ Or.inl
    refine ⟨?_,by rwa [hxMax] at hLarge⟩
    intro v hv
    have hLo:=hMin v hv
    have hHi:=s.graph.degree_le_maxDegree v
    omega
  have hxD:s.graph.degree x<s.graph.maxDegree:=lt_of_le_of_ne (s.graph.degree_le_maxDegree x) hxMax
  by_cases hLow:∃v∈s.cut.set,v≠x ∧ s.graph.degree v≤s.graph.maxDegree-s.graph.degree x
  · obtain ⟨v,hv,hvx,hLow⟩:=hLow
    have hB:2*B<s.graph.maxDegree+2:=by have hh:=hM.2.2;omega
    left
    exact Or.inr (Or.inr ⟨x,hx,hMin,hLarge,v,hv,hvx,hLow,
      enlarged_independent_of_second_low s.graph s.cut s.ready hx hLarge hv hvx hLow hB⟩)
  · right
    apply exists_step s hM x hx hxD hLarge
    intro v hv hvx
    have hNot:¬s.graph.degree v≤s.graph.maxDegree-s.graph.degree x:=by
      intro hh
      exact hLow ⟨v,hv,hvx,hh⟩
    have hBound:=s.graph.degree_le_maxDegree x
    omega

theorem Step.le {B K : ℕ} {s : State V B K} (p : Step s) : p.next.graph≤s.graph :=
  p.next_le_round.trans (p.round.le_residue.trans sdiff_le)

theorem Step.margins {B K : ℕ} {s : State V B K} (p : Step s) (hM : Margins s) : Margins p.next := by
  have hB:=p.budget_parameter_positive
  have hMax:=p.maximum
  rcases hM with ⟨h₁,h₂,h₃⟩
  unfold Margins
  omega

end OverfullWork.NormalizedClassTwoStep
