module

public import OverfullWork.PaperRoundGlobalPreservation

@[expose] public section


/-! # Uniform above-half margins for a globally safe first round

The free sparse scale is chosen before the graph. The finite margins in
the complete first-round preservation proof are discharged uniformly.
An actual second low vertex remains an explicit terminal alternative.
-/
namespace OverfullWork.PaperFirstRoundAboveHalf
open SimpleGraph Finset NormalizedAlmostStoppingRun LargeCentreMatchingStep
open PaperTopDegreeMatching PaperRoundGlobalPreservation
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem uniform_margins (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀n D : ℕ,N≤n →
      ((1:ℝ)/2+ε)*(n:ℝ)≤(D:ℝ) →
      let k:=n/(4096*Q^2)
      n+2*(6*k+6)+(k+1)+3≤2*D ∧
      n+(6*k+6)+(k+1)+5≤2*D ∧
      4*((6*k+6)+(k+1)+2)+1≤D := by
  obtain ⟨Q,hQ⟩:=exists_nat_gt (max (2:ℝ) (1/ε))
  have hQR:(2:ℝ)≤(Q:ℝ):=(le_max_left _ _).trans hQ.le
  have hQN:2≤Q:=by exact_mod_cast hQR
  have hQε:1≤ε*(Q:ℝ):=by
    have hh:1/ε<(Q:ℝ):=(le_max_right _ _).trans_lt hQ
    have ht:=(div_lt_iff₀ hε).mp hh
    nlinarith only [ht]
  obtain ⟨NE,hNE⟩:=exists_nat_gt (16/ε)
  refine ⟨Q,hQN,max 148 NE,?_⟩
  intro n D hn hdense
  dsimp only
  let k:=n/(4096*Q^2)
  have hk:4096*Q^2*k≤n:=Nat.mul_div_le n (4096*Q^2)
  have hkR:(4096:ℝ)*(Q:ℝ)^2*(k:ℝ)≤(n:ℝ):=by exact_mod_cast hk
  have hCoeff:(13:ℝ)≤ε*(4096*(Q:ℝ)^2):=by
    have hh:=mul_le_mul_of_nonneg_left hQε (show 0≤4096*(Q:ℝ) by positivity)
    nlinarith only [hh,hQR]
  have hThirteen:13*(k:ℝ)≤ε*(n:ℝ):=by
    have h₁:=mul_le_mul_of_nonneg_right hCoeff (Nat.cast_nonneg k : (0:ℝ)≤(k:ℝ))
    have h₂:=mul_le_mul_of_nonneg_left hkR hε.le
    nlinarith only [h₁,h₂]
  have hnE:NE≤n:=by omega
  have hSixteen:(16:ℝ)≤ε*(n:ℝ):=by
    have hh:16/ε<(n:ℝ):=hNE.trans_le (by exact_mod_cast hnE)
    have ht:=(div_lt_iff₀ hε).mp hh
    nlinarith only [ht]
  have hNumeric:n+13*k+16≤2*D:=by
    exact_mod_cast (show (n:ℝ)+13*(k:ℝ)+16≤2*(D:ℝ) by
      nlinarith only [hdense,hThirteen,hSixteen])
  have hDen:112≤4096*Q^2:=by nlinarith only [hQN]
  have h112:112*k≤n:=(Nat.mul_le_mul_right k hDen).trans hk
  have hSmall:28*k+37≤D:=by omega
  change n+2*(6*k+6)+(k+1)+3≤2*D ∧
    n+(6*k+6)+(k+1)+5≤2*D ∧ 4*((6*k+6)+(k+1)+2)+1≤D
  omega

/-- The data in a safe first round includes the globally no-overfull
cleaned graph itself, its class-two obstruction, and restored Hall/VAL.
The source certificate and the actual matching are retained together. -/
structure CleanStep (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (x : V) where
  left : V
  right : V
  top : IsTopPair G c.setᶜ left right
  round : Round G c x left right
  graph : SimpleGraph V
  deletion : MaximumNeighbourCleanup.DeletionRun c.setᶜ (G\round.matching) graph
  le_residue : graph≤G\round.matching
  maximum : graph.maxDegree=G.maxDegree-1
  uncolourable : ¬graph.EdgeColorable graph.maxDegree
  no_overfull : ¬graph.HasOverfullSubgraph
  core : graph.induce (c.set:Set V)=(G\round.matching).induce (c.set:Set V)
  complement_nonmaximum : ∀w∈c.setᶜ,graph.degree w<graph.maxDegree
  hall : ∀w∈c.setᶜ,∀v,graph.Adj w v → PrunedCore.neighboursIn graph c.setᶜ v<graph.degree w
  weak_VAL : ∀w∈c.setᶜ,∀v,graph.Adj w v → graph.maxDegree+2≤graph.degree w+graph.degree v

theorem exists_clean_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    (x : V) (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hxD : G.degree x<G.maxDegree) (hNo : ¬G.HasOverfullSubgraph)
    (hNonstop : ∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v)
    (hMargin : Fintype.card V+2*B+c.setᶜ.card+3≤2*G.maxDegree)
    (hDense : Fintype.card V+B+K+5≤2*G.maxDegree)
    (hSmall : 4*(B+K+2)+1≤G.maxDegree) : Nonempty (CleanStep G c x) := by
  classical
  obtain ⟨y,z,hTop,r,H,hRun,hLe,hMax,hNC,hNoH,hCore,hNonmax,hHall,hVal⟩:=
    exists_round_cleaned_no_overfull G hc c x hx hLarge hxD hNo hNonstop hMargin hDense hSmall
  exact ⟨⟨y,z,hTop,r,H,hRun,hLe,hMax,hNC,hNoH,hCore,hNonmax,hHall,hVal⟩⟩

/-- For every fixed positive above-half margin, all finite numerical
conditions are discharged. The second-low-core alternative is explicit;
the input must still be a critical source, as required by the proof. -/
theorem above_half_second_low_or_clean_step (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        let k:=Fintype.card V/(4096*Q^2)
        ∀(c : Certificate G (6*k+6) (k+1)) (x : V),x∈c.set →
          G.degree x<(∑w∈c.setᶜ,G.degree w) → G.degree x<G.maxDegree →
          (∃v∈c.set,v≠x ∧ G.degree v≤G.maxDegree-G.degree x) ∨
          Nonempty (CleanStep G c x) := by
  obtain ⟨Q,hQ,N,hMargins⟩:=uniform_margins ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro V _ _ G _ hn hc hdense hNo
  dsimp only
  intro c x hx hLarge hxD
  have hBounds:=hMargins (Fintype.card V) G.maxDegree hn hdense
  dsimp only at hBounds
  by_cases hNonstop:∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v
  · right
    apply exists_clean_step G hc c x hx hLarge hxD hNo hNonstop
    · have hY:=c.complement_small
      omega
    · exact hBounds.2.1
    · exact hBounds.2.2
  · left
    push Not at hNonstop
    obtain ⟨v,hv,hvx,hPair⟩:=hNonstop
    exact ⟨v,hv,hvx,by omega⟩

/-- An unconditional constructed fork for the original critical graph.
All alternatives are data, including the globally safe cleaned step.
Neither a normalized certificate nor a no-overfull residue is supplied
by the caller. The terminal alternatives are retained, not eliminated. -/
theorem above_half_constructed_fork (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        let k:=Fintype.card V/(4096*Q^2)
        (∃r : CriticalTwoColourReduction.Reduction G,
          (∑v:V,(2-r.layer.degree v))≤2*k+2 ∧ ¬(G\r.layer).HasOverfullSubgraph) ∨
        ∃c : Certificate G (6*k+6) (k+1),
          Nonempty (NormalizedCanonicalCandidate.Candidate c) ∨
          ((∀v∈c.set,G.degree v=G.maxDegree) ∧ G.maxDegree<(∑y∈c.setᶜ,G.degree y)) ∨
          (∃x∈c.set,∃v∈c.set,v≠x ∧
            G.degree x<(∑y∈c.setᶜ,G.degree y) ∧ G.degree x<G.maxDegree ∧
            G.degree v≤G.maxDegree-G.degree x ∧
            G.IsIndepSet (↑(insert x c.setᶜ):Set V)) ∨
          (∃x∈c.set,Nonempty (CleanStep G c x)) := by
  obtain ⟨Q,hQ,NM,hMargins⟩:=uniform_margins ε hε
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
    refine ⟨c,?_⟩
    have hMargin:Fintype.card V+2*(6*(Fintype.card V/(4096*Q^2))+6)+c.setᶜ.card+3≤2*G.maxDegree:=by
      have hY:=c.complement_small
      omega
    have hGap:c.set.card+(6*(Fintype.card V/(4096*Q^2))+6)+2*c.setᶜ.card≤2*G.maxDegree+2:=by
      have hCard:=card_add_card_compl c.set
      omega
    by_cases hMin:∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x
    · exact Or.inl (NormalizedCanonicalCandidate.exists_candidate G c hNo hGap hMin)
    · right
      push Not at hMin
      obtain ⟨x,hx,hMinimum,hLarge⟩:=LargeCentreCriticalGeometry.exists_minimum_large_anchor G c hMin
      by_cases hxMax:G.degree x=G.maxDegree
      · left
        refine ⟨?_,?_⟩
        · intro v hv
          have hLo:=hMinimum v hv
          have hHi:=G.degree_le_maxDegree v
          omega
        · simpa only [hxMax] using hLarge
      · right
        have hxD:G.degree x<G.maxDegree:=lt_of_le_of_ne (G.degree_le_maxDegree x) hxMax
        by_cases hNonstop:∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v
        · right
          exact ⟨x,hx,exists_clean_step G hc c x hx hLarge hxD hNo hNonstop
            hMargin hBounds.2.1 hBounds.2.2⟩
        · left
          push Not at hNonstop
          obtain ⟨v,hv,hvx,hPair⟩:=hNonstop
          have hLow:G.degree v≤G.maxDegree-G.degree x:=by omega
          have hB:2*(6*(Fintype.card V/(4096*Q^2))+6)<G.maxDegree+2:=by omega
          exact ⟨x,hx,v,hv,hvx,hLarge,hxD,hLow,
            LargeCentreCriticalGeometry.enlarged_complement_independent G hc c hx hLarge hv hvx hLow hB⟩
  · left
    obtain ⟨r,hMissing,hNoR⟩:=hReduction
    refine ⟨r,hMissing,?_⟩
    have transport (d₁ d₂ : DecidableRel (G\r.layer).Adj) :
        (¬@SimpleGraph.HasOverfullSubgraph V _ _ (G\r.layer) d₁) →
        ¬@SimpleGraph.HasOverfullSubgraph V _ _ (G\r.layer) d₂:=by
      cases Subsingleton.elim d₁ d₂
      exact id
    exact transport _ _ hNoR

end OverfullWork.PaperFirstRoundAboveHalf
