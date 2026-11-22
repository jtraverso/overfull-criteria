module

public import OverfullWork.CMSOperation42Excess
public import OverfullWork.CMSOperation41Invariants
public import OverfullWork.ClassTwoGlobalNoOverfull

@[expose] public section


/-! Small odd-cut geometry for Operation 4.2, obtained from robust
expansion as in CMS Claim 4.5(4). No above-half density is needed. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion PrunedCore OddCutDeficit NearTightOddSetGeometry
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem robust_cut_lower_simple (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (r t : ℕ) (hRob : IsRobustAt G r t) (hLo : t ≤ S.card) (hHi : S.card+t ≤ Fintype.card V) :
    r*r ≤ cutEdges G S := by
  let R := neighbourhood G r S
  have hGrow : S.card+r ≤ R.card := hRob S hLo hHi
  have hSplit := card_sdiff_add_card_inter R S
  have hLoss : (R∩S).card ≤ S.card := card_le_card inter_subset_right
  have hAfter : r ≤ (R \ S).card := by omega
  have hCut := MaximumOddCutPacking.cut_eq_sum_neighboursIn G S Sᶜ disjoint_compl_right
    (fun _ _ v _ => by by_cases hv : v ∈ S <;> simp_all)
  have hSub : R \ S ⊆ Sᶜ := fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2
  calc
    _ ≤ r*(R \ S).card := Nat.mul_le_mul_left r hAfter
    _ = ∑ v ∈ R \ S, r := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ R \ S, neighboursIn G S v := sum_le_sum (fun v hv =>
      (mem_filter.mp (mem_sdiff.mp hv).1).2)
    _ ≤ _ := by
      rw [hCut]
      exact sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => Nat.zero_le _)

set_option maxHeartbeats 1100000 in
theorem robust_overfull_omits_at_most_two (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (x : V) (B r t : ℕ) (hR : IsRobustAt H r t)
    (hRate : H.maxDegree ≤ r*r)
    (hPair : 2*B+2*t ≤ H.maxDegree)
    (hHigh : ∀ v ∈ X,v ≠ x → H.maxDegree ≤ H.degree v+B)
    (S : Finset V) (hOdd : Odd S.card) (hOver : H.maxDegree*(S.card/2) < internalEdges H S) :
    (X \ S).card ≤ 2 := by
  have hSize : H.maxDegree < S.card := by
    by_contra! h
    have hh := Nat.mul_le_mul_right (S.card/2) h
    have hCap := internalEdges_le_card_mul_half H S hOdd
    omega
  have hCut : cutEdges H S < H.maxDegree := by
    have h := (odd_internal_bound_iff_cut_deficit H H.maxDegree H.degree_le_maxDegree S hOdd).not.mp
      (not_le.mpr hOver)
    omega
  have hShort : Sᶜ.card < t := by
    by_contra! ht
    have hh := card_add_card_compl S
    have h := robust_cut_lower_simple H S r t hR (by omega) (by omega)
    omega
  have hOne : ((X \ S).erase x).card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra hn
    have huX := (mem_sdiff.mp (mem_erase.mp hu).2).1
    have hvX := (mem_sdiff.mp (mem_erase.mp hv).2).1
    have huS := mem_compl.mpr (mem_sdiff.mp (mem_erase.mp hu).2).2
    have hvS := mem_compl.mpr (mem_sdiff.mp (mem_erase.mp hv).2).2
    have hComp : ({u,v}:Finset V) ⊆ Sᶜ := insert_subset huS (singleton_subset_iff.mpr hvS)
    have hSum := CMSTrimmingRound.selected_degrees_le_cut_add_of_loss H H S {u,v} hComp 0
      (fun _ => by simp)
    rw [sum_pair hn,card_pair hn,Nat.add_zero] at hSum
    have h₁ := hHigh u huX (mem_erase.mp hu).1
    have h₂ := hHigh v hvX (mem_erase.mp hv).1
    omega
  have hh := card_erase_le (s := X \ S) (a := x)
  by_cases hx : x ∈ X \ S
  · have hh := card_erase_add_one hx
    omega
  · simpa only [erase_eq_of_notMem hx] using hOne.trans (by decide : 1 ≤ 2)

section ReadyRound

open ClassTwoMatchingRound NormalizedAlmostStoppingRun ClassTwoCleanupRound
open PaperTopDegreeMatching CleanedSourceVAL

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

theorem round_no_overfull_of_robust (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hReady : IsReady G c.setᶜ)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑u∈c.setᶜ,G.degree u))
    (hxD : G.degree x<G.maxDegree) (hTop : IsTopPair G c.setᶜ y z)
    (F : CoreRound G c.set x y z) (hNo : ¬G.HasOverfullSubgraph)
    (hNonstop : ∀v∈c.set,v≠x → G.maxDegree<G.degree x+G.degree v)
    (hRoom : 2*B+3*K+4 ≤ G.maxDegree) (r t : ℕ)
    (hRob : IsRobustAt (G \ F.matching) r t) (hRate : G.maxDegree ≤ r*r)
    (hPair : 2*B+2*t+1 ≤ G.maxDegree) :
    ¬(G \ F.matching).HasOverfullSubgraph := by
  apply ClassTwoGlobalNoOverfull.round_no_overfull_of_localization
    G c hReady hx hLarge hxD hTop F hNo hNonstop hRoom
  intro S hOdd hOver
  have hDrop : (G \ F.matching).maxDegree = G.maxDegree-1 := by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using F.residual_maxDegree
  apply robust_overfull_omits_at_most_two (G \ F.matching) c.set x B r t hRob (by omega) (by omega)
  · intro v hv hvx
    exact ClassTwoSmallOmissions.round_other_degree_lower G c hx hLarge F hv hvx
  · exact hOdd
  · exact hOver

theorem cleaned_round_no_overfull_of_robust (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hReady : IsReady G c.setᶜ) (s : CleanRound G c.set)
    (hLarge : G.degree s.anchor<(∑u∈c.setᶜ,G.degree u)) (hNo : ¬G.HasOverfullSubgraph)
    (hNonstop : ∀v∈c.set,v≠s.anchor → G.maxDegree<G.degree s.anchor+G.degree v)
    (hRoom : 2*B+3*K+4 ≤ G.maxDegree) (r t : ℕ)
    (hRob : IsRobustAt (G \ s.round.matching) r t) (hRate : G.maxDegree ≤ r*r)
    (hPair : 2*B+2*t+1 ≤ G.maxDegree) :
    ¬s.graph.HasOverfullSubgraph := by
  have hR := round_no_overfull_of_robust G c hReady s.anchor_mem hLarge s.anchor_nonmaximum
    s.top s.round hNo hNonstop hRoom r t hRob hRate hPair
  have hMax : (G \ s.round.matching).maxDegree = G.maxDegree-1 := by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using s.round.residual_maxDegree
  exact Critical.no_overfull_of_copy (Copy.ofLE s.graph (G \ s.round.matching) s.le_residue)
    (s.maximum.trans hMax.symm) hR

end ReadyRound

end OverfullWork.CMSMatchingRemoval
