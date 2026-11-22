module

public import OverfullWork.CompletionOffCentreBudget

@[expose] public section


/-! # Pin the actual identified centre at the first ordered coordinate

Sorting may leave equal-degree vertices in any order. Swap the first
coordinate with the real centre, prove every ordered degree unchanged,
then construct a fresh actual canonical completion of that ordered base.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 8000000

theorem Candidate.first_degree_le (p : Candidate c) (v : Fin (p.pairIndex+1)×Bool) :
    p.orderedBase.degree (0,false)≤p.orderedBase.degree v := by
  obtain ⟨i,b⟩:=v
  by_cases hi:i.val=0
  · have hi0:i=0:=Fin.ext hi
    subst i
    cases b
    · exact le_refl _
    · simpa only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex] using p.ordered_pair 0
  · apply p.ordered_pair_mono
    change 0 < i.val
    omega

theorem Candidate.exists_centred (p : Candidate c)
    (hMin : ∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) :
    ∃p' : Candidate c,p'.centre=(0,false) := by
  let first : Fin (p.pairIndex+1)×Bool:=(0,false)
  have hEqual:p.orderedBase.degree first=p.orderedBase.degree p.centre:=
    (p.first_degree_le p.centre).antisymm (p.centre_min_of_source_min hMin first)
  have hImage:c.image.degree (p.coordinates first)=c.image.degree (p.coordinates p.centre):=by
    simpa only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex] using hEqual
  let e: (Fin (p.pairIndex+1)×Bool) ≃ IndependentSetIdentification.Vertices c.setᶜ:=
    (Equiv.swap first p.centre).trans p.coordinates
  have hDegrees:∀v,c.image.degree (e v)=c.image.degree (p.coordinates v):=by
    intro v
    change c.image.degree (p.coordinates (Equiv.swap first p.centre v))=_
    by_cases hv:v=first
    · subst v
      rw [Equiv.swap_apply_left]
      exact hImage.symm
    · by_cases hc:v=p.centre
      · rw [hc,Equiv.swap_apply_right]
        exact hImage
      · rw [Equiv.swap_apply_of_ne_of_ne hv hc]
  have hFirst:e first=none:=by
    change p.coordinates (Equiv.swap first p.centre first)=none
    rw [Equiv.swap_apply_left]
    exact p.coordinates.apply_symm_apply none
  have hPair:∀i : Fin (p.pairIndex+1),c.image.degree (e (i,false))≤c.image.degree (e (i,true)):=by
    intro i
    rw [hDegrees,hDegrees]
    exact p.ordered_pair i
  have hNext:∀i j : Fin (p.pairIndex+1),i.val<j.val →
      c.image.degree (e (i,true))≤c.image.degree (e (j,false)):=by
    intro i j hij
    rw [hDegrees,hDegrees]
    exact p.ordered_next i j hij
  obtain ⟨C⟩:=CanonicalNoOverfullCompletion.exists_completion_of_no_overfull
    (OrderedCanonicalTransport.reindex c.image e) G.maxDegree
    (by intro v;rw [OrderedCanonicalTransport.degree_reindex];exact p.degree_le _)
    (by simpa only [OrderedCanonicalTransport.degree_reindex] using hPair)
    (by simpa only [OrderedCanonicalTransport.degree_reindex] using hNext)
    (OrderedCanonicalTransport.no_overfull_reindex c.image e G.maxDegree p.no_overfull)
  let p' : Candidate c:=
    {degree_le:=p.degree_le,degree_attained:=p.degree_attained,no_overfull:=p.no_overfull,
      pairIndex:=p.pairIndex,coordinates:=e,ordered_pair:=hPair,ordered_next:=hNext,completion:=C}
  refine ⟨p',?_⟩
  change e.symm none=first
  exact e.injective ((e.apply_symm_apply none).trans hFirst.symm)

/-- A source minimum is an actual branch hypothesis, not an assumption
about a sorting convention. The endpoint constructs the pinned candidate. -/
theorem exists_centred_candidate (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hNo : ¬G.HasOverfullSubgraph)
    (hGap : c.set.card+B+2*c.setᶜ.card≤2*G.maxDegree+2)
    (hMin : ∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) :
    ∃p : Candidate c,p.centre=(0,false) := by
  obtain ⟨p⟩:=exists_candidate G c hNo hGap hMin
  exact p.exists_centred hMin

end OverfullWork.NormalizedCanonicalCandidate
