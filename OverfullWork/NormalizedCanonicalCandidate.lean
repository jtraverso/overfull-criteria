module

public import OverfullWork.FlexibleAlmostReduction
public import OverfullWork.ConditionalIndependentIdentificationNoOverfull
public import OverfullWork.OrderedCanonicalTransport

@[expose] public section


/-! # An actual canonical candidate from the small-centre stopping branch

The normalized cut supplies an independent complement. In the branch
where its total degree does not exceed any core degree, identifying it
preserves the source maximum degree and no-overfullness. Sorting and
canonical completion are then actual constructions. The resulting
regular completion is not asserted to be factorable or no-overfull.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

structure Candidate {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) where
  degree_le : ∀v,c.image.degree v≤G.maxDegree
  degree_attained : ∃v,c.image.degree v=G.maxDegree
  no_overfull : ¬c.image.HasOverfullSubset G.maxDegree
  pairIndex : ℕ
  coordinates : (Fin (pairIndex+1)×Bool) ≃ IndependentSetIdentification.Vertices c.setᶜ
  ordered_pair : ∀i : Fin (pairIndex+1),
    c.image.degree (coordinates (i,false))≤c.image.degree (coordinates (i,true))
  ordered_next : ∀i j : Fin (pairIndex+1),i.val<j.val →
    c.image.degree (coordinates (i,true))≤c.image.degree (coordinates (j,false))
  completion : CanonicalRegularization.Completion
    (OrderedCanonicalTransport.reindex c.image coordinates) G.maxDegree

/-- No-overfullness of the identified image is proved from the original
graph and the finite gap, rather than supplied as a candidate hypothesis. -/
theorem exists_candidate (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hno : ¬G.HasOverfullSubgraph)
    (hGap : c.set.card+B+2*c.setᶜ.card≤2*G.maxDegree+2)
    (hMin : ∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) :
    Nonempty (Candidate c) := by
  have hInd:G.IsIndepSet (↑(c.setᶜ):Set V):=by
    simpa only [Finset.coe_compl] using c.independent
  have hOdd:Odd c.setᶜᶜ.card:=by simpa only [compl_compl] using c.odd
  have hMinimum:∀x,x∉c.setᶜ → (∑y∈c.setᶜ,G.degree y)≤G.degree x:=by
    intro x hx
    exact hMin x (by simpa only [mem_compl,not_not] using hx)
  have hNoImage:¬c.image.HasOverfullSubset G.maxDegree:=by
    apply ConditionalIndependentIdentification.actual_image_no_overfull
      G c.setᶜ hInd hno hOdd B hMinimum
    · simpa only [compl_compl] using c.budget
    · simpa only [compl_compl] using hGap
  obtain ⟨hDegree,hAttained⟩:=
    ConditionalIndependentIdentification.actual_image_has_maximum_degree G c.setᶜ hInd hOdd hMinimum
  obtain ⟨n,hn⟩:=c.odd
  have hCard:Fintype.card (IndependentSetIdentification.Vertices c.setᶜ)=2*(n+1):=by
    rw [IndependentSetIdentification.card_vertices,compl_compl,hn]
    omega
  obtain ⟨e,hPair,hOrder,⟨C⟩⟩:=OrderedCanonicalTransport.exists_ordered_completion
    c.image G.maxDegree n hCard hDegree hNoImage
  exact ⟨⟨hDegree,hAttained,hNoImage,n,e,hPair,hOrder,C⟩⟩

/-- For every fixed above-half margin, the finite gap is discharged.
The remaining alternatives are an actual compatible layer, an actual
canonical candidate, or an explicit core vertex below the merged degree.
This does not eliminate either terminal branch. -/
theorem above_half_candidate_or_large_centre (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        let k:=Fintype.card V/(4096*Q^2)
        (∃r : CriticalTwoColourReduction.Reduction G,
          (∑v:V,(2-r.layer.degree v))≤2*k+2 ∧
          ¬(G\r.layer).HasOverfullSubgraph) ∨
        (∃c : Certificate G (6*k+6) (k+1),Nonempty (Candidate c)) ∨
        (∃c : Certificate G (6*k+6) (k+1),
          c.set.card+(6*k+6)+2*c.setᶜ.card≤2*G.maxDegree+2 ∧
          ∃x∈c.set,G.degree x<(∑y∈c.setᶜ,G.degree y)) := by
  obtain ⟨Q,hQ,N,hFork⟩:=FlexibleAlmostReduction.above_half_normalized_fork_with_gap.{u} ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro V _ _ G _ hn hc hdense hno
  dsimp only
  rcases hFork G hn hc hdense hno with ⟨c,hGap⟩|hReduction
  · by_cases hMin:∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x
    · exact Or.inr (Or.inl ⟨c,exists_candidate G c hno hGap hMin⟩)
    · push Not at hMin
      exact Or.inr (Or.inr ⟨c,hGap,hMin⟩)
  · exact Or.inl hReduction

end OverfullWork.NormalizedCanonicalCandidate
