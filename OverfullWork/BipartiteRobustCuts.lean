module

public import OverfullWork.BipartiteRobustTransport

@[expose] public section


/-! # Large cuts from the constructed bipartite expansion

This is the large-set step in the no-overfull argument of CMS Claim 4.3.
Expansion is used on one side of the actual cut, with a capped subset
when necessary. Counts in the conclusion include all multiplicities.
-/
namespace OverfullWork.BipartiteRobustCuts
open SimpleGraph Finset PrunedCore RobustExpansion BipartiteRobustMargin
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem neighbours_le_weight (M : MultiGraph V) (S : Finset V) (v : V) :
    neighboursIn M.supportGraph S v≤∑w∈S,M.mult s(v,w) := by
  rw [neighboursIn_eq_filter_card,card_filter]
  apply sum_le_sum
  intro w hw
  split_ifs with h
  · change 0<M.mult s(v,w) at h
    omega
  · exact Nat.zero_le _

theorem incidences_le_cut (M : MultiGraph V) (S R : Finset V) (r : ℕ)
    (hR : R⊆Sᶜ) (hN : ∀v∈R,r≤neighboursIn M.supportGraph S v) :
    r*R.card≤M.cutSize S := by
  calc
    _ = ∑_v∈R,r := by simp [Nat.mul_comm]
    _ ≤ ∑v∈R,∑w∈S,M.mult s(v,w) :=
      sum_le_sum (fun v hv=>(hN v hv).trans (neighbours_le_weight M S v))
    _ ≤ ∑v∈Sᶜ,∑w∈S,M.mult s(v,w) :=
      sum_le_sum_of_subset_of_nonneg hR (fun _ _ _=>Nat.zero_le _)
    _ = M.cutSize S := by
      rw [sum_comm]
      unfold MultiGraph.cutSize
      apply sum_congr rfl
      intro w hw
      apply sum_congr rfl
      intro v hv
      rw [Sym2.eq_swap]

theorem directed_cut_bound (M : MultiGraph V) (A B S : Finset V) (m r t : ℕ)
    (hA : A.card=m) (hExpand : ExpandsTo M.supportGraph A B r t)
    (hDisjoint : Disjoint A B) (hCover : A∪B=univ)
    (hSize : S.card≤m) (hThreshold : 2*t≤m)
    (hLarge : t≤(S∩A).card) (hBalance : (S∩B).card≤(S∩A).card) :
    r*r≤M.cutSize S := by
  have hSplit:(S∩A).card+(S∩B).card=S.card := by
    rw [←card_union_of_disjoint (hDisjoint.mono inter_subset_right inter_subset_right)]
    rw [←inter_union_distrib_left,hCover,inter_univ]
  let z:=min (S∩A).card (m-t)
  obtain ⟨T,hT,hCard⟩:=exists_subset_card_eq (show z≤(S∩A).card from min_le_left _ _)
  have hTA:T⊆A:=hT.trans inter_subset_right
  have hTS:T⊆S:=hT.trans inter_subset_left
  have ht:t≤T.card:=by rw [hCard];dsimp [z];omega
  have hhi:T.card+t≤A.card:=by rw [hCard,hA];dsimp [z];omega
  have hOther:(S∩B).card≤T.card:=by rw [hCard];dsimp [z];omega
  let R:=neighbours M.supportGraph B r T
  have hR:R⊆B:=filter_subset _ _
  have hRN:=hExpand T hTA ht hhi
  change T.card+r≤R.card at hRN
  have hInter:(R∩S).card≤(S∩B).card:=by
    apply card_le_card
    intro v hv
    obtain ⟨hvR,hvS⟩:=mem_inter.mp hv
    exact mem_inter.mpr ⟨hvS,hR hvR⟩
  have hDiff:r≤(R\S).card:=by have hh:=card_sdiff_add_card_inter R S;omega
  have hCount:=incidences_le_cut M S (R\S) r
    (by intro v hv;exact mem_compl.mpr (mem_sdiff.mp hv).2)
    (by
      intro v hv
      have hn: r≤neighboursIn M.supportGraph T v:=(mem_filter.mp (mem_sdiff.mp hv).1).2
      exact hn.trans (by
        unfold PrunedCore.neighboursIn
        apply card_le_card
        intro w hw
        obtain ⟨hwN,hwT⟩:=mem_filter.mp hw
        exact mem_filter.mpr ⟨hwN,hTS hwT⟩))
  exact (Nat.mul_le_mul_left r hDiff).trans hCount

/-- Every set between the two-sided threshold and half the vertices
has a cut of size at least r squared. -/
theorem large_cut_bound (M : MultiGraph V) (A S : Finset V) (m r t : ℕ)
    (hA : A.card=m) (hAc : Aᶜ.card=m)
    (hExpand : IsBipartiteRobustAt M.supportGraph A r t)
    (hSize : S.card≤m) (hLarge : 2*t≤S.card) (hThreshold : 2*t≤m) :
    r*r≤M.cutSize S := by
  have hSplit:(S∩A).card+(S∩Aᶜ).card=S.card := by
    rw [←card_union_of_disjoint (disjoint_compl_right.mono inter_subset_right inter_subset_right)]
    rw [←inter_union_distrib_left,union_compl,inter_univ]
  by_cases hBalance:(S∩Aᶜ).card≤(S∩A).card
  · exact directed_cut_bound M A Aᶜ S m r t hA hExpand.1 disjoint_compl_right
      (union_compl _) hSize hThreshold (by omega) hBalance
  · exact directed_cut_bound M Aᶜ A S m r t hAc hExpand.2 disjoint_compl_left
      (by rw [union_comm];exact union_compl _) hSize hThreshold (by omega) (by omega)

end OverfullWork.BipartiteRobustCuts
