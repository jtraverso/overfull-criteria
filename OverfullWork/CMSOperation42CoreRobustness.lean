module

public import OverfullWork.CMSOperation42RobustOddCuts
public import OverfullWork.RobustExpansionDeletion

@[expose] public section


/-! Robustness in the fixed ordinary core during Operation 4.2.
Algorithm 2 changes only edges outside this induced core, and each
completed matching spends at most one core neighbour per vertex. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem robust_at_of_eq (G H : SimpleGraph V) [dG : DecidableRel G.Adj]
    [dH : DecidableRel H.Adj] (he : G = H) (r t : ℕ) (h : IsRobustAt G r t) :
    IsRobustAt H r t := by
  subst H
  cases Subsingleton.elim dH dG
  exact h

theorem robust_core_after_matching_and_cleanup {G R : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel R.Adj] {X : Finset V} (M : SimpleGraph V)
    (hDegree : ∀ v,M.degree v ≤ 1)
    (hCore : R.induce (X : Set V) = (G \ M).induce (X : Set V))
    (r t : ℕ) (hRob : IsRobustAt (G.induce (X : Set V)) r t) :
    IsRobustAt (R.induce (X : Set V)) (r-1) t := by
  let F := M.induce (X : Set V)
  let H := G.induce (X : Set V)
  have hF (v : X) : F.degree v ≤ 1 := by
    let e : X ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    have hLe : F.map e ≤ M := by
      intro u w h
      obtain ⟨x,y,hxy,rfl,rfl⟩ := (map_adj e F u w).mp h
      exact hxy
    have hDeg := CMSTrimmingRound.map_degree_at_embedding F e v
    exact hDeg.symm.trans_le ((degree_le_of_le hLe (v := v.val)).trans (hDegree _))
  have hEq : H \ F = R.induce (X : Set V) := hCore.symm
  have hR := RobustExpansion.isRobustAt_sdiff H F r 1 t hRob hF
  exact robust_at_of_eq _ _ (dG := SimpleGraph.Sdiff.adjDecidable X H F) hEq _ _ hR

theorem clean_round_robust_core {G : SimpleGraph V} [DecidableRel G.Adj]
    {X : Finset V} (s : ClassTwoCleanupRound.CleanRound G X) (r t : ℕ)
    (hRob : IsRobustAt (G.induce (X : Set V)) r t) :
    IsRobustAt (s.graph.induce (X : Set V)) (r-1) t := by
  exact robust_core_after_matching_and_cleanup s.round.matching s.round.degree_le_one s.core r t hRob

theorem fixed_core_run_robust {G H : SimpleGraph V} [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj]
    {X : Finset V} {j : ℕ} (p : ClassTwoMatchingRun.Run X G H j) (r t : ℕ)
    (hRob : IsRobustAt (G.induce (X : Set V)) r t) :
    IsRobustAt (H.induce (X : Set V)) (r-j) t := by
  revert dH
  induction p with
  | refl =>
    intro dH
    cases Subsingleton.elim dH dG
    simpa only [Nat.sub_zero] using hRob
  | @step H j dStep p s ih =>
    intro dEnd
    cases Subsingleton.elim dEnd (fun v w => Classical.propDecidable (s.graph.Adj v w))
    have h := @ih dStep
    have hR := clean_round_robust_core s (r-j) t h
    rw [Nat.sub_sub] at hR
    exact hR

theorem robust_of_ordinary_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (r t : ℕ)
    (hRob : IsRobustAt (G.induce (X : Set V)) r t) :
    IsRobustAt G (r-Xᶜ.card) (t+Xᶜ.card) := by
  intro S hLo hHi
  by_cases hRate : Xᶜ.card ≤ r
  swap
  · have he : r-Xᶜ.card = 0 := by omega
    have hn : neighbourhood G 0 S = univ := by ext v; simp [neighbourhood]
    rw [he,hn,card_univ]
    omega
  let H := G.induce (X : Set V)
  let T : Finset X := S.subtype (· ∈ X)
  let emb : X ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hT : T.map emb = S∩X := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
      exact mem_inter.mpr ⟨mem_subtype.mp hw,w.property⟩
    · intro hv
      exact mem_map.mpr ⟨⟨v,(mem_inter.mp hv).2⟩,mem_subtype.mpr (mem_inter.mp hv).1,rfl⟩
  have hTCard : T.card = (S∩X).card := by rw [←hT,card_map]
  have hLoss : S.card ≤ T.card+Xᶜ.card := by
    have h := card_sdiff_add_card_inter S X
    have hh : (S \ X).card ≤ Xᶜ.card := card_le_card (fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2)
    omega
  have hTLo : t ≤ T.card := by omega
  have hTHi : T.card+t ≤ Fintype.card X := by
    have hC := card_add_card_compl X
    have hU : T.card ≤ S.card := by rw [hTCard]; exact card_le_card inter_subset_left
    rw [Fintype.card_coe]
    omega
  have hGrow := hRob T hTLo hTHi
  let R := neighbourhood H r T
  have hSub : R.map emb ⊆ neighbourhood G (r-Xᶜ.card) S := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
    have hNeigh : PrunedCore.neighboursIn H T w ≤ PrunedCore.neighboursIn G S w.val := by
      rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card,
        ←card_map (f := emb) (s := T.filter (H.Adj w))]
      apply card_le_card
      intro z hz
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hz
      obtain ⟨huT,hAdj⟩ := mem_filter.mp hu
      exact mem_filter.mpr ⟨mem_subtype.mp huT,hAdj⟩
    exact mem_filter.mpr ⟨mem_univ _,(Nat.sub_le _ _).trans ((mem_filter.mp hw).2.trans hNeigh)⟩
  have hCard := card_le_card hSub
  rw [card_map] at hCard
  change T.card+r ≤ R.card at hGrow
  omega

theorem fixed_core_run_robust_source {G H : SimpleGraph V} [DecidableRel G.Adj] [dH : DecidableRel H.Adj]
    {X : Finset V} {j : ℕ} (p : ClassTwoMatchingRun.Run X G H j) (r t : ℕ)
    (hRob : IsRobustAt (G.induce (X : Set V)) r t) :
    IsRobustAt H (r-(j+Xᶜ.card)) (t+Xᶜ.card) := by
  rw [←Nat.sub_sub]
  exact robust_of_ordinary_core H X (r-j) t (fixed_core_run_robust p r t hRob)


end OverfullWork.CMSMatchingRemoval
