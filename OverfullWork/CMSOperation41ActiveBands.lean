module

public import OverfullWork.CMSOperation41PhysicalPrefix
public import OverfullWork.CMSOperation41DegreeLedger

@[expose] public section


/-! Claim 4.1(1)–(4), degree accounting at the critical switch.
The original low set is the intersection with the current exceptional
set. Once the auxiliary active set is chosen, its degree reserve
prevents the first preprocessing deletion during the shorter range. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PrunedCore LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem low_history_eq_inter_original (U W : ℕ → Finset V)
    (hInitial : W 0 ⊆ U 0) (hU : ∀ i,U (i+1) ⊆ U i)
    (hW : ∀ i,W (i+1) = U (i+1) ∩ W i) (i : ℕ) :
    W i = U i ∩ W 0 := by
  induction i with
  | zero => exact (inter_eq_right.mpr hInitial).symm
  | succ i ih =>
    rw [hW i,ih,←inter_assoc,inter_eq_left.mpr (hU i)]

theorem no_auxiliary_preprocessing_of_large_active_degrees {G T : SimpleGraph V}
    [dG : DecidableRel G.Adj] (W : Finset V) (p : DeletionRun W G T)
    (hDegree : ∀ w ∈ W,W.card < G.degree w) : T = G := by
  induction p with
  | refl => rfl
  | @step H dH p w x hw hAdj hBad ih =>
    subst H
    cases Subsingleton.elim dH dG
    have hCard : neighboursIn G W x ≤ W.card :=
      card_le_card (fun v hv => (mem_filter.mp hv).2)
    have hStrict := hDegree w hw
    exact False.elim (Nat.not_lt_of_ge (hBad.trans hCard) hStrict)

/-- The inheritance test is applied to the accumulated physical
debits. The formula counts a round with two prescribed edges twice. -/
theorem inherited_active_prefix_degree_balance (W : Finset V) (S T P : ℕ → SimpleGraph V) (m : ℕ)
    (hClean : ∀ i < m,DeletionRun W (S i) (T i))
    (hPrescribed : ∀ i < m,P i ≤ T i)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i))
    (hBudget : ∀ i < m,∀ w ∈ W,W.card < (S i).degree w ∨
      W.card+(∑ k ∈ range i,(P k).degree w) < (S 0).degree w) :
    (∀ i ≤ m,∀ w ∈ W,(S i).degree w+(∑ k ∈ range i,(P k).degree w) = (S 0).degree w) ∧
      (∀ i < m,T i = S i) := by
  have transfer (G H : SimpleGraph V) (v : V) (h : G = H) : G.degree v = H.degree v := by
    subst H
    rfl
  have hSame (i : ℕ) (hi : i < m)
      (hBalance : ∀ w ∈ W,(S i).degree w+(∑ k ∈ range i,(P k).degree w) = (S 0).degree w) :
      T i = S i :=
    no_auxiliary_preprocessing_of_large_active_degrees W (hClean i hi) (by
      intro w hw
      have h := hBalance w hw
      rcases hBudget i hi w hw with hHigh | hInit
      · exact hHigh
      · omega)
  have hRec (i : ℕ) (hi : i ≤ m) :
      ∀ w ∈ W,(S i).degree w+(∑ k ∈ range i,(P k).degree w) = (S 0).degree w := by
    induction i with
    | zero => simp
    | succ i ih =>
      intro w hw
      have hi' : i < m := by omega
      have hPrev := ih hi'.le
      have hs := hSame i hi' hPrev
      have hRemoved : (sdiff (T i) (P i)).degree w+(P i).degree w = (T i).degree w := by
        simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
          MaximumMatching.degree_sdiff_add_of_le (T i) (P i) (hPrescribed i hi') w
      have hStep := transfer (S (i+1)) (sdiff (T i) (P i)) w (hNext i hi')
      have hSameDegree := transfer (T i) (S i) w hs
      have hOld := hPrev w hw
      rw [sum_range_succ]
      omega
  exact ⟨hRec,fun i hi => hSame i hi (hRec i hi.le)⟩

theorem inherited_active_set_persists (W : Finset V) (S T P : ℕ → SimpleGraph V) (m : ℕ)
    (hInitial : ∀ w ∈ W,W.card+m < (S 0).degree w)
    (hClean : ∀ i < m,DeletionRun W (S i) (T i))
    (hPrescribed : ∀ i < m,P i ≤ T i)
    (hUnit : ∀ i < m,∀ w ∈ W,(P i).degree w = 1)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i)) :
    (∀ i ≤ m,∀ w ∈ W,(S i).degree w+i = (S 0).degree w) ∧
      (∀ i < m,T i = S i) ∧
      ∀ i ≤ m,∀ w ∈ W,0 < (S i).degree w := by
  have hSum (i : ℕ) (hi : i ≤ m) (w : V) (hw : w ∈ W) :
      (∑ k ∈ range i,(P k).degree w) = i := by
    calc
      _ = ∑ _k ∈ range i,(1 : ℕ) := sum_congr rfl fun k hk =>
        hUnit k ((mem_range.mp hk).trans_le hi) w hw
      _ = _ := by simp
  obtain ⟨hBalance,hNoCleanup⟩ :=
    inherited_active_prefix_degree_balance W S T P m hClean hPrescribed hNext (by
      intro i hi w hw
      apply Or.inr
      rw [hSum i hi.le w hw]
      exact (Nat.add_lt_add_left hi W.card).trans (hInitial w hw))
  have hRec (i : ℕ) (hi : i ≤ m) (w : V) (hw : w ∈ W) :
      (S i).degree w+i = (S 0).degree w := by
    simpa only [hSum i hi w hw] using hBalance i hi w hw
  refine ⟨hRec,hNoCleanup,?_⟩
  intro i hi w hw
  have h := hRec i hi w hw
  have hInit := hInitial w hw
  omega

end OverfullWork.CMSTrimmingRound
