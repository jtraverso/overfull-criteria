module

public import OverfullWork.CMSOperation41DegreeHistory
public import OverfullWork.CMSOperation41ExactRecords

@[expose] public section


/-! Charge all preprocessing losses to the original low set, as in
Claim 4.1(4). At an original low vertex the first incident deletion
occurs at degree at most the size of that active set. All subsequent
incident deletions use edges still present at that first round. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every removed edge in an Algorithm 1 run meets its active set. -/
theorem cleanup_removed_edge_meets_active {G H : SimpleGraph V} {W : Finset V}
    (p : DeletionRun W G H) {a b : V} (hEdge : (sdiff G H).Adj a b) : a ∈ W ∨ b ∈ W := by
  by_contra! hNo
  let a' : ↥((W : Set V)ᶜ) := ⟨a,hNo.1⟩
  let b' : ↥((W : Set V)ᶜ) := ⟨b,hNo.2⟩
  have hSame := congrArg (fun J : SimpleGraph ↥((W : Set V)ᶜ) => J.Adj a' b') (DeletionRun.induce_away p)
  exact hEdge.2 ((Iff.of_eq hSame).mpr hEdge.1)

/-- Virtual and physical cleanup delete the same edges. The earlier
packed edges have both endpoints outside the original exceptional set. -/
theorem trimming_cleanup_after_core_removal {S T : SimpleGraph V} {W U : Finset V}
    (run : DeletionRun W S T) (hW : W ⊆ U) (C : SimpleGraph V)
    (hCore : ∀ v ∈ U,∀ u,¬C.Adj v u) :
    sdiff S T ≤ sdiff S C ∧ sdiff (sdiff S C) (sdiff S T) = sdiff T C := by
  constructor
  · intro x y hGone
    refine ⟨hGone.1,?_⟩
    intro h
    exact (cleanup_removed_edge_meets_active run hGone).elim
      (fun hw => hCore x (hW hw) y h) (fun hw => hCore y (hW hw) x h.symm)
  · ext x y
    simp only [sdiff_adj]
    have hSub := DeletionRun.le_source run
    have hLe := @hSub x y
    tauto

set_option maxHeartbeats 3500000 in
/-- The sum of the actual cleanup losses at a vertex is at most the
original size of the low set. Later rounds may use an inherited active
set once their preprocessing is known to be empty. -/
theorem cumulative_cleanup_degree_le_original_low_card
    (G : SimpleGraph V) (W0 : Finset V) (S T : ℕ → SimpleGraph V) (W : ℕ → Finset V) (m : ℕ)
    (hFirst : S 0 = G) (hIndependent : G.IsIndepSet (W0 : Set V))
    (hClean : ∀ i < m,DeletionRun (W i) (S i) (T i))
    (hModes : ∀ i < m,W i ⊆ W0 ∨ T i = S i)
    (hNext : ∀ i < m,S (i+1) ≤ T i) :
    ∀ j ≤ m,∀ v,(∑ i : Fin j,(sdiff (S i.val) (T i.val)).degree v) ≤ W0.card := by
  let removed (i : ℕ) := sdiff (S i) (T i)
  have hDecrease (a b : ℕ) (hab : a ≤ b) (hb : b ≤ m) : S b ≤ S a := by
    induction b with
    | zero => have he : a = 0 := by omega
              subst a
              exact le_rfl
    | succ b ih =>
      by_cases he : a = b+1
      · rw [he]
      have hlt : b < m := by omega
      exact (hNext b hlt).trans ((DeletionRun.le_source (hClean b hlt)).trans (ih (by omega) hlt.le))
  have hSubsetG (i : ℕ) (hi : i ≤ m) : S i ≤ G := by
    rw [←hFirst]
    exact hDecrease 0 i (Nat.zero_le _) hi
  have hDis (i : ℕ) (hi : i < m) (k : ℕ) (hk : k < m) (hne : i ≠ k) :
      Disjoint (removed i) (removed k) := by
    have hBefore (a b : ℕ) (hab : a < b) (hb : b < m) : Disjoint (removed a) (removed b) := by
      rw [disjoint_iff_inf_le]
      intro u v h
      have hSa : S b ≤ T a := (hDecrease (a+1) b (by omega) hb.le).trans (hNext a (hab.trans hb))
      exact h.1.2 (hSa h.2.1)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hBefore i k h hk
    · exact (hBefore k i h hi).symm
  have hCharged (i : ℕ) (hi : i < m) {v x : V} (h : (removed i).Adj v x) :
      W i ⊆ W0 ∧ (v ∈ W i ∨ x ∈ W i) := by
    rcases hModes i hi with hSub | hEq
    · exact ⟨hSub,cleanup_removed_edge_meets_active (hClean i hi) h⟩
    · exact (h.2 (hEq.symm ▸ h.1)).elim
  intro j hj v
  let used := usedTrimmingPrefix removed j
  have hCount : used.degree v = ∑ i : Fin j,(removed i.val).degree v :=
    degree_of_disjoint_trimming_prefix removed j v (fun i hi k hk => hDis i (hi.trans_le hj) k (hk.trans_le hj))
  change (∑ i : Fin j,(removed i.val).degree v) ≤ W0.card
  rw [←hCount]
  by_cases hv : v ∈ W0
  · by_cases hAny : ∃ i < j,∃ x,(removed i).Adj v x
    · let first := Nat.find hAny
      obtain ⟨hf,xf,hGone⟩ := Nat.find_spec hAny
      have hW := hCharged first (hf.trans_le hj) hGone
      have hvActive : v ∈ W first := by
        rcases hW.2 with h | h
        · exact h
        · exact (hIndependent hv (hW.1 h) hGone.1.ne (hSubsetG first (hf.le.trans hj) hGone.1)).elim
      have hInd : (S first).IsIndepSet (W first : Set V) := by
        intro x hx y hy hne hEdge
        exact hIndependent (hW.1 hx) (hW.1 hy) hne (hSubsetG first (hf.le.trans hj) hEdge)
      have hSmall := active_degree_le_of_incident_cleanup (hClean first (hf.trans_le hj))
        hInd hvActive hGone.1 hGone.2
      have hLe : used.neighborFinset v ⊆ (S first).neighborFinset v := by
        intro x hx
        have hAdj : used.Adj v x := (mem_neighborFinset _ _ _).mp hx
        obtain ⟨i,hi⟩ := iSup_adj.mp hAdj
        have hPrior : first ≤ i.val := Nat.find_min' hAny ⟨i.isLt,x,hi⟩
        exact (mem_neighborFinset _ _ _).mpr (hDecrease first i.val hPrior (i.isLt.le.trans hj) hi.1)
      rw [←card_neighborFinset_eq_degree]
      exact (card_le_card hLe).trans (by
        rw [card_neighborFinset_eq_degree]
        exact hSmall.trans (card_le_card hW.1))
    · have hZero : used.degree v = 0 := by
        by_contra! hPos
        obtain ⟨x,hx⟩ := (used.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hPos)
        obtain ⟨i,hi⟩ := iSup_adj.mp hx
        exact hAny ⟨i.val,i.isLt,x,hi⟩
      omega
  · rw [←card_neighborFinset_eq_degree]
    apply card_le_card
    intro x hx
    have hAdj : used.Adj v x := (mem_neighborFinset _ _ _).mp hx
    obtain ⟨i,hi⟩ := iSup_adj.mp hAdj
    obtain ⟨hSub,hTouch⟩ := hCharged i.val (i.isLt.trans_le hj) hi
    exact hSub (hTouch.resolve_left (fun h => hv (hSub h)))

set_option maxHeartbeats 1600000 in
/-- The original cleanup budget can absorb one additional last edge
of an exhausted singleton. Its deletion is counted in the prefix. -/
theorem cumulative_cleanup_degree_with_one_extra_round
    (G : SimpleGraph V) (W0 : Finset V) (S T : ℕ → SimpleGraph V)
    (W : ℕ → Finset V) (m extra : ℕ)
    (hFirst : S 0 = G) (hIndependent : G.IsIndepSet (W0 : Set V))
    (hClean : ∀ i < m,DeletionRun (W i) (S i) (T i))
    (hModes : ∀ i < m,i ≠ extra → W i ⊆ W0 ∨ T i = S i)
    (hExtra : extra < m → ∀ v,(sdiff (S extra) (T extra)).degree v ≤ 1)
    (hNext : ∀ i < m,S (i+1) ≤ T i) :
    ∀ v,(∑ i ∈ range m,(sdiff (S i) (T i)).degree v) ≤ W0.card+1 := by
  let beforeRepair (i : ℕ) := if i = extra then S i else T i
  have hClean' (i : ℕ) (hi : i < m) : DeletionRun (W i) (S i) (beforeRepair i) := by
    by_cases he : i = extra
    · rw [show beforeRepair i = S i from if_pos he]
      exact .refl _
    · rw [show beforeRepair i = T i from if_neg he]
      exact hClean i hi
  have hModes' (i : ℕ) (hi : i < m) : W i ⊆ W0 ∨ beforeRepair i = S i := by
    by_cases he : i = extra
    · exact Or.inr (if_pos he)
    · rw [show beforeRepair i = T i from if_neg he]
      exact hModes i hi he
  have hNext' (i : ℕ) (hi : i < m) : S (i+1) ≤ beforeRepair i := by
    by_cases he : i = extra
    · rw [show beforeRepair i = S i from if_pos he]
      exact (hNext i hi).trans (DeletionRun.le_source (hClean i hi))
    · rw [show beforeRepair i = T i from if_neg he]
      exact hNext i hi
  intro v
  have hBase := cumulative_cleanup_degree_le_original_low_card G W0 S beforeRepair W m
    hFirst hIndependent hClean' hModes' hNext' m le_rfl v
  rw [Fin.sum_univ_eq_sum_range (fun i => (sdiff (S i) (beforeRepair i)).degree v) m] at hBase
  have hSum : (∑ i ∈ range m,if i = extra then 1 else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq']
    split <;> decide
  have hTotal : (∑ i ∈ range m,(sdiff (S i) (T i)).degree v) ≤
      (∑ i ∈ range m,(sdiff (S i) (beforeRepair i)).degree v)+
        (∑ i ∈ range m,if i = extra then 1 else 0) := by
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro i hi
    by_cases he : i = extra
    · subst i
      have h := hExtra (mem_range.mp hi) v
      rw [if_pos rfl]
      omega
    · rw [show beforeRepair i = T i from if_neg he,if_neg he,Nat.add_zero]
  omega

set_option maxHeartbeats 2500000 in
/-- Claim 4.1(4) for ordinary vertices, including those that became
ordinary in an earlier round. The bound includes the cleanup that
precedes the current Step 2. -/
theorem ordinary_degree_after_cumulative_cleanup
    (G : SimpleGraph V) (W0 : Finset V) (S T : ℕ → SimpleGraph V) (W U : ℕ → Finset V)
    (D m threshold : ℕ) (degree cleaned credit : ℕ → V → ℕ)
    (hFirst : S 0 = G) (hIndependent : G.IsIndepSet (W0 : Set V))
    (hClean : ∀ i < m,DeletionRun (W i) (S i) (T i))
    (hModes : ∀ i < m,W i ⊆ W0 ∨ T i = S i)
    (hNext : ∀ i < m,S (i+1) ≤ T i)
    (hInitial : ∀ v,0 < degree 0 v → v ∉ U 0 → D ≤ degree 0 v+threshold)
    (hUpdate : ∀ i < m,U (i+1) = nextTrimmingExceptional (U i)
      (univ.filter (fun v => 0 < degree (i+1) v)) (degree (i+1)) (D-2*(i+1)) threshold)
    (hRound : ∀ i < m,∀ v,degree (i+1) v+(sdiff (S i) (T i)).degree v+(2-credit i v) = degree i v)
    (hCleanDegree : ∀ i < m,∀ v,cleaned i v+(sdiff (S i) (T i)).degree v = degree i v)
    (hRoom : 2*m ≤ D) :
    ∀ j < m,∀ v,0 < cleaned j v → v ∉ U j → D-2*j ≤ cleaned j v+threshold+W0.card := by
  let loss (i : ℕ) (v : V) := (sdiff (S i) (T i)).degree v
  apply nonexceptional_degree_after_bounded_cleanup D m threshold W0.card U degree cleaned loss credit
    hInitial hUpdate hRound hCleanDegree _ hRoom
  intro v
  rw [←Fin.sum_univ_eq_sum_range (fun i => loss i v) m]
  exact cumulative_cleanup_degree_le_original_low_card G W0 S T W m
    hFirst hIndependent hClean hModes hNext m le_rfl v

end OverfullWork.CMSTrimmingRound
