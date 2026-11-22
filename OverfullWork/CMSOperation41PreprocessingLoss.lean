module

public import OverfullWork.CMSOperation41ActiveBands
public import OverfullWork.FixedCoreBudgetTransport

@[expose] public section


/-! The per-vertex loss spent by Algorithm 1 in Claim 4.2.
At an independent active vertex above the bad-edge threshold,
its first incident deletion cannot occur. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PrunedCore LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem DeletionRun.le_source {G H : SimpleGraph V} {W : Finset V}
    (p : DeletionRun W G H) : H ≤ G := by
  induction p with
  | refl => exact le_rfl
  | step _ _ _ _ ih => exact (deleteEdges_le _).trans ih

theorem independent_high_active_incidence_of_preprocessing {G H : SimpleGraph V}
    [dG : DecidableRel G.Adj] {W : Finset V} (p : DeletionRun W G H)
    (hInd : G.IsIndepSet (W : Set V)) (v : V) (hv : v ∈ W) (hLarge : W.card < G.degree v) :
    ∀ u,H.Adj v u ↔ G.Adj v u := by
  induction p with
  | refl => intro u; rfl
  | @step T dT prior w x hw hAdj hBad ih =>
    have hCard : neighboursIn T W x ≤ W.card :=
      card_le_card (fun y hy => (mem_filter.mp hy).2)
    have hDeg : T.degree v = G.degree v := by
      rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
      congr 1
      ext u
      simp only [mem_neighborFinset]
      exact ih u
    have hvw : v ≠ w := by
      intro h
      subst w
      have hLe := hBad.trans hCard
      rw [hDeg] at hLe
      exact (Nat.not_lt_of_ge hLe) hLarge
    have hvx : v ≠ x := by
      intro h
      subst x
      exact hInd hw hv hAdj.ne (DeletionRun.le_source prior hAdj)
    intro u
    simp only [deleteEdges_adj,Set.mem_singleton_iff]
    have hEdge : s(v,u) ≠ s(w,x) := by
      intro he
      have hM : v ∈ s(w,x) := he ▸ (Sym2.mem_iff.mpr (Or.inl rfl))
      exact (Sym2.mem_iff.mp hM).elim hvw hvx
    exact (and_iff_left hEdge).trans (ih u)

theorem independent_auxiliary_preprocessing_degree_loss {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {W : Finset V} (p : DeletionRun W G H)
    (hInd : G.IsIndepSet (W : Set V)) (v : V) : G.degree v ≤ H.degree v+W.card := by
  by_cases hv : v ∈ W
  · by_cases hLarge : W.card < G.degree v
    · have hEq : H.degree v = G.degree v := by
        rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
        congr 1
        ext u
        simp only [mem_neighborFinset]
        exact independent_high_active_incidence_of_preprocessing p hInd v hv hLarge u
      omega
    · omega
  · have hKeep : H.induce (↑(Wᶜ) : Set V) = G.induce (↑(Wᶜ) : Set V) := by
      have he : (↑(Wᶜ) : Set V) = (W : Set V)ᶜ := by ext u; simp
      rw [he]
      exact DeletionRun.induce_away p
    have h := FixedCoreBudgetTransport.degree_le_degree_add_complement G H Wᶜ hKeep v (mem_compl.mpr hv)
    simpa only [compl_compl] using h

theorem degree_loss_from_actual_cleanup_and_layer {G H L : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel L.Adj] {W : Finset V}
    (p : DeletionRun W G H) (hInd : G.IsIndepSet (W : Set V))
    (hLe : L ≤ H) (hDeg : ∀ v,L.degree v ≤ 2) :
    ∀ v,G.degree v ≤ (sdiff H L).degree v+(W.card+2) := by
  intro v
  have h₁ := independent_auxiliary_preprocessing_degree_loss p hInd v
  have h₂ : (sdiff H L).degree v+L.degree v = H.degree v := by
    simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le H L hLe v
  have h₃ := hDeg v
  omega

end OverfullWork.CMSTrimmingRound
