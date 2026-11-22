module

public import OverfullWork.PaperTwoCoreRoundPreservation

@[expose] public section


/-! # Global no-overfull preservation for an actual first matching round

The source is critical. Its normalized core has small deficit outside
the anchor. Explicit above-half and small-budget margins exclude three
or more omissions; the preceding modules handle zero, one and two.
The source nonstopping inequality is retained, and a failure returns an
actual second low core vertex. This is not an iteration on critical
residues, nor a terminal factorization theorem.
-/
namespace OverfullWork.PaperRoundGlobalPreservation
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open LargeCentreMatchingStep PaperTopDegreeMatching PaperPairExtensionPreservation
open PaperOneCoreRoundPreservation PaperTwoCoreRoundPreservation PaperSmallCutGeometry
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem round_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hxD : G.degree x<G.maxDegree) (hTop : IsTopPair G c.setᶜ y z)
    (r : Round G c x y z) (hNo : ¬G.HasOverfullSubgraph)
    (hNonstop : ∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v)
    (hDense : Fintype.card V+B+K+5≤2*G.maxDegree)
    (hSmall : 4*(B+K+2)+1≤G.maxDegree) :
    ¬(G\r.matching).HasOverfullSubgraph := by
  let R:=G\r.matching
  have hDrop:R.maxDegree=G.maxDegree-1:=by
    simpa only [R,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  have hD:4≤G.maxDegree:=by omega
  have hB:B≤G.maxDegree:=by omega
  rintro ⟨S,hOver⟩
  change R.maxDegree*(S.card/2) < internalEdges R S at hOver
  have hOdd:Odd S.card:=by
    by_contra hn
    have hEven:=Nat.not_odd_iff_even.mp hn
    exact (not_lt_of_ge (even_internal_bound R R.maxDegree R.degree_le_maxDegree S hEven)) hOver
  have hAtMost:(c.set\S).card≤2:=by
    apply overfull_omits_at_most_two R c.set x B K c.complement_small
    · intro v hv hvx
      exact round_other_degree_lower G c hx hLarge r hv hvx
    · omega
    · omega
    · exact hOdd
    · exact hOver
  have hBound:internalEdges R S≤R.maxDegree*(S.card/2):=by
    by_cases hZero:(c.set\S).card=0
    · have hIn:c.set⊆S:=sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hZero)
      have hBase:=core_supersets_nonoverfull G c hx hLarge hxD hTop r hD hB hNo S hOdd hIn
      have transport (d₁ d₂ : DecidableRel R.Adj) :
          (@internalEdges V _ _ R d₁ S≤@SimpleGraph.maxDegree V R _ d₁*(S.card/2)) →
          (@internalEdges V _ _ R d₂ S≤@SimpleGraph.maxDegree V R _ d₂*(S.card/2)):=by
        cases Subsingleton.elim d₁ d₂
        exact id
      exact transport _ _ hBase
    · by_cases hOne:(c.set\S).card=1
      · exact one_omission_nonoverfull_after_cleanup G R hc c hx hLarge hD hB hTop r le_rfl rfl S hOdd hOne
      · exact two_omission_round_nonoverfull G hc c hx hLarge hxD r hNonstop
          (by omega) S hOdd (by omega)
  exact (not_lt_of_ge hBound) hOver

/-- Global preservation in the same cleaned graph, proved from the
source and the constructed round. No residue no-overfull premise. -/
theorem round_no_overfull_after_cleanup (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hxD : G.degree x<G.maxDegree) (hTop : IsTopPair G c.setᶜ y z)
    (r : Round G c x y z) (hNo : ¬G.HasOverfullSubgraph)
    (hNonstop : ∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v)
    (hDense : Fintype.card V+B+K+5≤2*G.maxDegree)
    (hSmall : 4*(B+K+2)+1≤G.maxDegree)
    (hLe : H≤G\r.matching) (hMax : H.maxDegree=(G\r.matching).maxDegree) :
    ¬H.HasOverfullSubgraph := by
  have hR:=round_no_overfull G hc c hx hLarge hxD hTop r hNo hNonstop hDense hSmall
  apply Critical.no_overfull_of_copy (Copy.ofLE H (G\r.matching) hLe) hMax
  exact hR

/-- A genuine matching-removal and Algorithm 2 cleanup with global
no-overfull preservation, retaining the source nonstopping inequality. -/
theorem exists_round_cleaned_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    (x : V) (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hxD : G.degree x<G.maxDegree) (hNo : ¬G.HasOverfullSubgraph)
    (hNonstop : ∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v)
    (hMargin : Fintype.card V+2*B+c.setᶜ.card+3≤2*G.maxDegree)
    (hDense : Fintype.card V+B+K+5≤2*G.maxDegree)
    (hSmall : 4*(B+K+2)+1≤G.maxDegree) :
    ∃y z,IsTopPair G c.setᶜ y z ∧ ∃r : Round G c x y z,∃H : SimpleGraph V,
      MaximumNeighbourCleanup.DeletionRun c.setᶜ (G\r.matching) H ∧
      H≤G\r.matching ∧ H.maxDegree=G.maxDegree-1 ∧ ¬H.EdgeColorable H.maxDegree ∧
      ¬H.HasOverfullSubgraph ∧
      H.induce (c.set:Set V)=(G\r.matching).induce (c.set:Set V) ∧
      (∀w∈c.setᶜ,H.degree w<H.maxDegree) ∧
      (∀w∈c.setᶜ,∀v,H.Adj w v → PrunedCore.neighboursIn H c.setᶜ v<H.degree w) ∧
      (∀w∈c.setᶜ,∀v,H.Adj w v → H.maxDegree+2≤H.degree w+H.degree v) := by
  classical
  obtain ⟨y,z,hTop,⟨r⟩⟩:=exists_top_round G hc c x hx hLarge hxD hMargin
  obtain ⟨H,hRun,hLe,hMax,hNC,hCore,hNonmax,hHall,hVal⟩:=
    exists_post_round_cleanup G hc c hx hLarge (by omega) hTop r
  have hRMax:(G\r.matching).maxDegree=G.maxDegree-1:=by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  exact ⟨y,z,hTop,r,H,hRun,hLe,hMax,hNC,
    round_no_overfull_after_cleanup G H hc c hx hLarge hxD hTop r hNo hNonstop hDense hSmall
      hLe (hMax.trans hRMax.symm),hCore,hNonmax,hHall,hVal⟩

/-- Failure of the degree condition is returned as an actual second
low core vertex, exactly the branch requiring two-centre treatment. -/
theorem second_low_vertex_or_safe_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    (x : V) (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hxD : G.degree x<G.maxDegree) (hNo : ¬G.HasOverfullSubgraph)
    (hMargin : Fintype.card V+2*B+c.setᶜ.card+3≤2*G.maxDegree)
    (hDense : Fintype.card V+B+K+5≤2*G.maxDegree)
    (hSmall : 4*(B+K+2)+1≤G.maxDegree) :
    (∃v∈c.set,v≠x ∧ G.degree v≤G.maxDegree-G.degree x) ∨
    ∃y z,IsTopPair G c.setᶜ y z ∧ ∃r : Round G c x y z,∃H : SimpleGraph V,
      MaximumNeighbourCleanup.DeletionRun c.setᶜ (G\r.matching) H ∧
      H≤G\r.matching ∧ H.maxDegree=G.maxDegree-1 ∧ ¬H.EdgeColorable H.maxDegree ∧
      ¬H.HasOverfullSubgraph ∧
      H.induce (c.set:Set V)=(G\r.matching).induce (c.set:Set V) ∧
      (∀w∈c.setᶜ,H.degree w<H.maxDegree) ∧
      (∀w∈c.setᶜ,∀v,H.Adj w v → PrunedCore.neighboursIn H c.setᶜ v<H.degree w) ∧
      (∀w∈c.setᶜ,∀v,H.Adj w v → H.maxDegree+2≤H.degree w+H.degree v) := by
  by_cases hNonstop:∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v
  · exact Or.inr (exists_round_cleaned_no_overfull G hc c x hx hLarge hxD hNo hNonstop hMargin hDense hSmall)
  · left
    push Not at hNonstop
    obtain ⟨v,hv,hvx,hPair⟩:=hNonstop
    exact ⟨v,hv,hvx,by omega⟩

end OverfullWork.PaperRoundGlobalPreservation
