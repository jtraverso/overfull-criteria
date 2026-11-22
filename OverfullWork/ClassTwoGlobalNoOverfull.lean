module

public import OverfullWork.ClassTwoSmallOmissions

@[expose] public section


/-! # Global preservation from a ready class-two source

The full local maximum-neighbour inequality replaces criticality.
Source degree ordering remains explicit in the certificate. No
no-overfullness of the matching residue or of the cleanup is assumed.
-/
namespace OverfullWork.ClassTwoGlobalNoOverfull
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open ClassTwoMatchingRound PaperTopDegreeMatching MatchingOddDeficiency
open PaperSmallCutGeometry CleanedSourceVAL
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem round_no_overfull_of_localization (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hReady : IsReady G c.setᶜ)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hxD : G.degree x<G.maxDegree) (hTop : IsTopPair G c.setᶜ y z)
    (r : CoreRound G c.set x y z) (hNo : ¬G.HasOverfullSubgraph)
    (hNonstop : ∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v)
    (hRoom : 2*B+3*K+4≤G.maxDegree)
    (hLocalize : ∀ S : Finset V, Odd S.card →
      (G\r.matching).maxDegree*(S.card/2) < internalEdges (G\r.matching) S →
      (c.set\S).card ≤ 2) :
    ¬(G\r.matching).HasOverfullSubgraph := by
  let R:=G\r.matching
  have hDrop:R.maxDegree=G.maxDegree-1:=by
    simpa only [R,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  have hD:4≤G.maxDegree:=by omega
  have hB:B≤G.maxDegree:=by omega
  have transport (S : Finset V) (d₁ d₂ : DecidableRel R.Adj) :
      (@internalEdges V _ _ R d₁ S≤@SimpleGraph.maxDegree V R _ d₁*(S.card/2)) →
      (@internalEdges V _ _ R d₂ S≤@SimpleGraph.maxDegree V R _ d₂*(S.card/2)):=by
    cases Subsingleton.elim d₁ d₂
    exact id
  rintro ⟨S,hOver⟩
  change R.maxDegree*(S.card/2) < internalEdges R S at hOver
  have hOdd:Odd S.card:=by
    by_contra hn
    exact (not_lt_of_ge (even_internal_bound R R.maxDegree R.degree_le_maxDegree S
      (Nat.not_odd_iff_even.mp hn))) hOver
  have hAtMost : (c.set\S).card ≤ 2 := hLocalize S hOdd hOver
  have hBound:internalEdges R S≤R.maxDegree*(S.card/2):=by
    by_cases hZero:(c.set\S).card=0
    · have hIn:c.set⊆S:=sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hZero)
      exact transport S _ _ (ClassTwoCoreSupersets.core_supersets_nonoverfull G c hx hLarge hxD hTop r hD hB hNo S hOdd hIn)
    · by_cases hOne:(c.set\S).card=1
      · by_cases hThree:3≤(S∩c.setᶜ).card
        · exact transport S _ _ (ClassTwoCoreSupersets.three_complement_nonoverfull G c r
            hTop.left_mem hTop.right_mem hTop.ne hB S hOdd hThree)
        · obtain ⟨v,hv,w,hw,hSet⟩:=PaperOneCoreRoundPreservation.one_omission_geometry
            c.set S c.odd hOdd hOne (by omega)
          rw [hSet]
          exact ClassTwoSmallOmissions.one_core_round_nonoverfull G c hReady hD hTop r v w hv hw
      · exact ClassTwoSmallOmissions.two_omission_round_nonoverfull G c hReady hx hLarge hxD
          hTop.left_mem r hNonstop hRoom S hOdd (by omega)
  exact (not_lt_of_ge hBound) hOver

theorem round_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hReady : IsReady G c.setᶜ)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hxD : G.degree x<G.maxDegree) (hTop : IsTopPair G c.setᶜ y z)
    (r : CoreRound G c.set x y z) (hNo : ¬G.HasOverfullSubgraph)
    (hNonstop : ∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v)
    (hDense : Fintype.card V+B+K+5≤2*G.maxDegree)
    (hSmall : 4*(B+K+2)+1≤G.maxDegree) :
    ¬(G\r.matching).HasOverfullSubgraph := by
  apply round_no_overfull_of_localization G c hReady hx hLarge hxD hTop r hNo hNonstop (by omega)
  intro S hOdd hOver
  have hDrop : (G\r.matching).maxDegree=G.maxDegree-1 := by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  apply overfull_omits_at_most_two (G\r.matching) c.set x B K c.complement_small
  · intro v hv hvx
    exact ClassTwoSmallOmissions.round_other_degree_lower G c hx hLarge r hv hvx
  · omega
  · omega
  · exact hOdd
  · exact hOver

theorem cleaned_round_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hReady : IsReady G c.setᶜ)
    (s : ClassTwoCleanupRound.CleanRound G c.set)
    (hLarge : G.degree s.anchor<(∑u∈c.setᶜ,G.degree u))
    (hNo : ¬G.HasOverfullSubgraph)
    (hNonstop : ∀v∈c.set,v≠s.anchor → G.maxDegree<G.degree s.anchor+G.degree v)
    (hDense : Fintype.card V+B+K+5≤2*G.maxDegree)
    (hSmall : 4*(B+K+2)+1≤G.maxDegree) :
    ¬s.graph.HasOverfullSubgraph := by
  have hR:=round_no_overfull G c hReady s.anchor_mem hLarge s.anchor_nonmaximum s.top s.round
    hNo hNonstop hDense hSmall
  have hRMax:(G\s.round.matching).maxDegree=G.maxDegree-1:=by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using s.round.residual_maxDegree
  exact Critical.no_overfull_of_copy (Copy.ofLE s.graph (G\s.round.matching) s.le_residue)
    (s.maximum.trans hRMax.symm) hR

theorem two_active_of_large_centre (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (x : V) (hx : x∈c.set)
    (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u)) :
    2≤(c.setᶜ.filter fun w=>0<G.degree w).card := by
  let A:=c.setᶜ.filter fun w=>0<G.degree w
  by_contra hn
  change ¬2≤A.card at hn
  have hAPos:A.Nonempty:=by
    by_contra hEmpty
    have hZero:∀u∈c.setᶜ,G.degree u=0:=by
      intro u hu
      by_contra hPos
      exact hEmpty ⟨u,mem_filter.mpr ⟨hu,by omega⟩⟩
    have hh: (∑u∈c.setᶜ,G.degree u)=0:=sum_eq_zero hZero
    omega
  have hCard:A.card=1:=by have hp:=card_pos.mpr hAPos;omega
  obtain ⟨y,hA⟩:=card_eq_one.mp hCard
  have hy:y∈A:=by rw [hA];simp
  have hyY:y∈c.setᶜ:=(mem_filter.mp hy).1
  have hOther:∀u∈c.setᶜ,u≠y → G.degree u=0:=by
    intro u hu huy
    by_contra hn
    have huA:u∈A:=mem_filter.mpr ⟨hu,by omega⟩
    rw [hA,mem_singleton] at huA
    exact huy huA
  have hSum:(∑u∈c.setᶜ,G.degree u)=G.degree y:=by
    apply sum_eq_single y hOther
    exact fun hh=>(hh hyY).elim
  have hOrder:=c.ordered y hyY x hx
  omega

theorem exists_safe_clean_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNC : ¬G.EdgeColorable G.maxDegree) {B K : ℕ} (c : Certificate G B K)
    (hReady : IsReady G c.setᶜ) (hNo : ¬G.HasOverfullSubgraph)
    (x : V) (hx : x∈c.set) (hxD : G.degree x<G.maxDegree)
    (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hNonstop : ∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v)
    (hMargin : Fintype.card V+2*B+c.setᶜ.card+3≤2*G.maxDegree)
    (hDense : Fintype.card V+B+K+5≤2*G.maxDegree)
    (hSmall : 4*(B+K+2)+1≤G.maxDegree) :
    ∃s : ClassTwoCleanupRound.CleanRound G c.set,s.anchor=x ∧ ¬s.graph.HasOverfullSubgraph := by
  classical
  have hInd:G.IsIndepSet (↑(c.setᶜ):Set V):=by simpa only [coe_compl] using c.independent
  have hHall:=MaximumNeighbourCleanup.hall_of_final_inequality G c.setᶜ hReady.1 hReady.2
  have hHigh:∀v∈c.set,v≠x → G.maxDegree≤G.degree v+B:=by
    intro v hv hvx
    have hh:=LargeCentreCriticalGeometry.other_degree_lower G c hx hLarge hv hvx
    omega
  obtain ⟨s,hsx⟩:=ClassTwoCleanupRound.exists_clean_round G hNC c.set c.odd hInd hHall
    hReady.1 c.light_pairs (by omega) x hx hxD B hHigh hMargin (two_active_of_large_centre G c x hx hLarge)
  refine ⟨s,hsx,cleaned_round_no_overfull G c hReady s ?_ hNo ?_ hDense hSmall⟩
  · simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,hsx] using hLarge
  · simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,hsx] using hNonstop

end OverfullWork.ClassTwoGlobalNoOverfull
