module

public import OverfullWork.NormalizedClassTwoIteration

@[expose] public section


/-! # A constructed terminal normalized reduction above one half

The sparse scale and order threshold precede the original graph.
The normalized certificate, initial ready class-two state, safe run and
terminal state are all constructed. Canonical candidates and exceptional
terminal geometries are retained; no factorization is assumed.
-/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 10000000

theorem State.image_uncolourable {B K : ℕ} (s : State V B K) :
    ¬Nonempty (s.cut.image.EdgeColoring s.graph.maxDegree) := by
  rintro ⟨C⟩
  have hInd:s.graph.IsIndepSet (↑(s.cut.setᶜ):Set V):=by
    simpa only [coe_compl] using s.cut.independent
  exact s.uncolourable (IndependentSetIdentification.colourable_of_identification
    s.graph s.cut.setᶜ hInd C)

theorem terminal_candidate_or_exceptional {B K : ℕ} (s : State V B K)
    (hM : Margins s) (hT : Terminal s) :
    Nonempty (NormalizedCanonicalCandidate.Candidate s.cut) ∨
    ((∀v∈s.cut.set,s.graph.degree v=s.graph.maxDegree) ∧
      s.graph.maxDegree<(∑y∈s.cut.setᶜ,s.graph.degree y)) ∨
    ∃x∈s.cut.set,(∀v∈s.cut.set,s.graph.degree x≤s.graph.degree v) ∧
      s.graph.degree x<(∑y∈s.cut.setᶜ,s.graph.degree y) ∧
      ∃v∈s.cut.set,v≠x ∧ s.graph.degree v≤s.graph.maxDegree-s.graph.degree x ∧
        s.graph.IsIndepSet (↑(insert x s.cut.setᶜ):Set V) := by
  rcases hT with hSmall|hMaximum|hLow
  · left
    apply NormalizedCanonicalCandidate.exists_candidate s.graph s.cut s.no_overfull _ hSmall
    have hMatch:=hM.1
    have hY:=s.cut.complement_small
    have hCard:=card_add_card_compl s.cut.set
    omega
  · exact Or.inr (Or.inl hMaximum)
  · exact Or.inr (Or.inr hLow)

theorem above_half_terminal_fork (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        let k:=Fintype.card V/(4096*Q^2)
        (∃r : CriticalTwoColourReduction.Reduction G,
          (∑v:V,(2-r.layer.degree v))≤2*k+2 ∧ ¬(G\r.layer).HasOverfullSubgraph) ∨
        (∃c : Certificate G (6*k+6) (k+1),Nonempty (NormalizedCanonicalCandidate.Candidate c)) ∨
        ∃s : State V (6*k+6) (k+1),s.graph≤G ∧ s.graph.maxDegree=G.maxDegree ∧
          ∃C : ℕ,∃t : State V C (k+1),∃j : ℕ,Run s t j ∧ Terminal t ∧ Margins t ∧
            C+2*j=6*k+6 ∧ t.graph.maxDegree+j=G.maxDegree ∧ t.graph≤G := by
  obtain ⟨Q,hQ,NM,hMargins⟩:=PaperFirstRoundAboveHalf.uniform_margins ε hε
  obtain ⟨NF,hFork⟩:=FlexibleAlmostReduction.above_half_normalized_fork_at_budget.{u} ε hε Q hQ
  refine ⟨Q,hQ,max NM NF,?_⟩
  intro V _ _ G _ hn hc hdense hNo
  dsimp only
  have hnM:NM≤Fintype.card V:=by omega
  have hnF:NF≤Fintype.card V:=by omega
  have hBounds:=hMargins (Fintype.card V) G.maxDegree hnM hdense
  dsimp only at hBounds
  rcases hFork G hnF hc hdense hNo with hCert|hReduction
  · obtain ⟨c⟩:=hCert
    right
    by_cases hSmall:∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x
    · left
      refine ⟨c,NormalizedCanonicalCandidate.exists_candidate G c hNo ?_ hSmall⟩
      have hY:=c.complement_small
      have hCard:=card_add_card_compl c.set
      omega
    · right
      push Not at hSmall
      obtain ⟨x,hx,hLarge⟩:=hSmall
      have hNonmax:=CriticalIndependentPairMatching.complement_nonmaximum G hc c hx hLarge
      have hInd:G.IsIndepSet (↑(c.setᶜ):Set V):=by simpa only [coe_compl] using c.independent
      obtain ⟨H,hLe,hMax,hNC,hNoH,c',_,hReady,_⟩:=
        JointCutNormalization.exists_joint_normalization G hc.2.1 hNo c.set c.odd
          _ _ c.complement_small hInd hNonmax c.light_pairs c.budget
      let s : State V (6*(Fintype.card V/(4096*Q^2))+6) (Fintype.card V/(4096*Q^2)+1):=
        ⟨H,c',hReady,hNC,hNoH⟩
      have hM:Margins s:=by
        unfold Margins
        change Fintype.card V+2*(6*(Fintype.card V/(4096*Q^2))+6)+(Fintype.card V/(4096*Q^2)+1)+3≤2*H.maxDegree ∧ _
        rw [hMax]
        exact ⟨hBounds.1,hBounds.2.1,hBounds.2.2⟩
      obtain ⟨C,t,j,hRun,hT,hMT,hBudget,hDegree,hLeT⟩:=exists_terminal_run s hM
      refine ⟨s,hLe,hMax,C,t,j,hRun,hT,hMT,hBudget,?_,hLeT.trans hLe⟩
      simpa only [s,hMax] using hDegree
  · left
    obtain ⟨r,hMissing,hNoR⟩:=hReduction
    refine ⟨r,hMissing,?_⟩
    have transport (d₁ d₂ : DecidableRel (G\r.layer).Adj) :
        (¬@SimpleGraph.HasOverfullSubgraph V _ _ (G\r.layer) d₁) →
        ¬@SimpleGraph.HasOverfullSubgraph V _ _ (G\r.layer) d₂:=by
      cases Subsingleton.elim d₁ d₂
      exact id
    exact transport _ _ hNoR

end OverfullWork.NormalizedClassTwoStep
