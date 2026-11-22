module

public import OverfullWork.CMSOperation41ProjectionBudget
public import OverfullWork.CMSOperation41SpokePrescription

@[expose] public section


/-! The three charges in Claim 4.1(7) are counted separately.
Freely chosen representatives avoid a saturated history. Forced matching
endpoints consume distinct original edges. A deficient ordinary vertex
can be charged only while its saved degree fits below the target. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem projectionLoad_range_succ (use : ℕ → Finset V) (j : ℕ) (v : V) :
    projectionLoad (range (j+1)) use v = projectionLoad (range j) use v +
      if v ∈ use j then 1 else 0 := by
  rw [projectionLoad,card_filter,Finset.sum_range_succ,projectionLoad,card_filter]

omit [Fintype V] in
theorem projection_load_le_of_avoid_saturated (use : ℕ → Finset V) (m cap : ℕ)
    (hFresh : ∀ j < m,∀ v ∈ use j,projectionLoad (range j) use v < cap) :
    ∀ j ≤ m,∀ v,projectionLoad (range j) use v ≤ cap := by
  intro j hj
  induction j with
  | zero => simp [projectionLoad]
  | succ j ih =>
    intro v
    have hj' : j < m := by omega
    rw [projectionLoad_range_succ]
    by_cases hv : v ∈ use j
    · simpa only [if_pos hv] using Nat.succ_le_of_lt (hFresh j hj' v hv)
    · simpa only [if_neg hv,add_zero] using ih hj'.le v

set_option maxHeartbeats 1300000 in
theorem exists_spoke_prescription_avoiding_saturated (G : SimpleGraph V) [DecidableRel G.Adj]
    (B U F : Finset V) (hBU : B ⊆ U) (hUF : U ⊆ F)
    (use : ℕ → Finset V) (j cap k b : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(use i).card ≤ b) (hTotal : j*b ≤ k*cap)
    (hDegree : ∀ z ∈ B,F.card+k+2*B.card ≤ G.degree z) :
    let S := univ.filter fun v : V => cap ≤ projectionLoad (range j) use v
    ∃ (e : (↥B × Bool) ↪ ↥((F∪S)ᶜ : Finset V)) (P : SimpleGraph V),
      P ≤ G ∧ (∀ x y,P.Adj x y → x ∈ U ∨ y ∈ U) ∧
      (∀ v ∈ B,P.degree v = 2) ∧ (∀ v ∈ U,v ∉ B → P.degree v = 0) ∧
      (∀ v,v ∉ B → P.degree v ≤ 1) ∧
      (∀ z : B,G.Adj z.val (e (z,false)).val ∧ G.Adj z.val (e (z,true)).val) ∧
      (∀ x y,P.Adj x y ↔ ∃ z : B,∃ side : Bool,
        (x = z.val ∧ y = (e (z,side)).val) ∨ (y = z.val ∧ x = (e (z,side)).val)) ∧
      ∀ i,projectionLoad (range j) use (e i).val < cap := by
  intro S
  have hSCard : S.card ≤ k := saturated_projection_card_le (range j) use cap k b hCap
    (fun i hi => hUsed i (mem_range.mp hi)) (by simpa only [card_range] using hTotal)
  obtain ⟨e,P,hP,hCut,hB,hU,hMax,hEdges,hShape⟩ := exists_spoke_prescription G B U (F∪S) hBU
    (hUF.trans subset_union_left) (fun z hz => by
      have hSize := card_union_le F S
      have hzD := hDegree z hz
      omega)
  refine ⟨e,P,hP,hCut,hB,hU,hMax,hEdges,hShape,?_⟩
  intro i
  by_contra! h
  exact mem_compl.mp (e i).property (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩))

omit [Fintype V] in
theorem forced_projection_load_le_of_disjoint_edges (use : ℕ → Finset V) (layer : ℕ → SimpleGraph V)
    (j : ℕ) (v : V) (W T : Finset V)
    (hDis : ∀ i < j,∀ k < j,i ≠ k → Disjoint (layer i) (layer k))
    (hForced : ∀ i < j,v ∈ use i → ∃ w ∈ W∪T,(layer i).Adj v w) :
    projectionLoad (range j) use v ≤ W.card+T.card := by
  let visits := (range j).filter (fun i => v ∈ use i)
  have hWitness (i : visits) : ∃ w ∈ W∪T,(layer i).Adj v w :=
    hForced i.val (mem_range.mp (mem_filter.mp i.property).1) (mem_filter.mp i.property).2
  let charged (i : ℕ) := if hi : i ∈ visits then (hWitness ⟨i,hi⟩).choose else v
  have hCharge {i} (hi : i ∈ visits) : charged i ∈ W∪T ∧ (layer i).Adj v (charged i) := by
    simpa only [charged,dif_pos hi] using (hWitness ⟨i,hi⟩).choose_spec
  have hInj : (visits : Set ℕ).InjOn charged := by
    intro i hi k hk hEq
    by_contra hne
    have hd := hDis i (mem_range.mp (mem_filter.mp hi).1) k (mem_range.mp (mem_filter.mp hk).1) hne
    rw [disjoint_iff_inf_le] at hd
    exact hd ⟨(hCharge hi).2,hEq ▸ (hCharge hk).2⟩
  have hCard := card_le_card_of_injOn charged (fun i hi => (hCharge hi).1) hInj
  exact hCard.trans (card_union_le _ _)

omit [Fintype V] in
theorem exceptional_projection_load_le_of_degree_credits (use : ℕ → Finset V)
    (degree loss credit : ℕ → V → ℕ) (D j a : ℕ) (v : V)
    (hInit : D ≤ degree 0 v+a) (hFinal : degree j v ≤ D-2*j) (hRoom : 2*j ≤ D)
    (hStep : ∀ i < j,degree i v+credit i v ≤ degree (i+1) v+2+loss i v)
    (hCredit : ∀ i < j,v ∈ use i → 1 ≤ credit i v) :
    projectionLoad (range j) use v ≤ a+(∑ i ∈ range j,loss i v) := by
  have hTel : ∀ k ≤ j,degree 0 v+projectionLoad (range k) use v ≤
      degree k v+2*k+(∑ i ∈ range k,loss i v) := by
    intro k hk
    induction k with
    | zero => simp [projectionLoad]
    | succ k ih =>
      have hk' : k < j := by omega
      have hBefore := ih hk'.le
      have hAfter := hStep k hk'
      have hSaved : (if v ∈ use k then 1 else 0) ≤ credit k v := by
        by_cases hv : v ∈ use k
        · simpa only [if_pos hv] using hCredit k hk' hv
        · simp only [if_neg hv,Nat.zero_le]
      rw [projectionLoad_range_succ,sum_range_succ]
      omega
  have h := hTel j le_rfl
  omega

omit [Fintype V] in
theorem projection_load_le_sum_of_three_charges (all free forced deficient : ℕ → Finset V)
    (j : ℕ) (v : V) (a b c : ℕ)
    (hSplit : ∀ i < j,v ∈ all i → v ∈ free i ∨ v ∈ forced i ∨ v ∈ deficient i)
    (hFree : projectionLoad (range j) free v ≤ a)
    (hForced : projectionLoad (range j) forced v ≤ b)
    (hDeficient : projectionLoad (range j) deficient v ≤ c) :
    projectionLoad (range j) all v ≤ a+b+c := by
  let rounds (use : ℕ → Finset V) := (range j).filter (fun i => v ∈ use i)
  have hSub : rounds all ⊆ (rounds free∪rounds forced)∪rounds deficient := by
    intro i hi
    obtain ⟨hr,hUse⟩ := mem_filter.mp hi
    rcases hSplit i (mem_range.mp hr) hUse with hf|hm|hd
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hr,hf⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hr,hm⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hr,hd⟩)
  have hUnion₁ := card_union_le (rounds free) (rounds forced)
  have hUnion₂ := card_union_le (rounds free∪rounds forced) (rounds deficient)
  have hCard := card_le_card hSub
  change (rounds all).card ≤ a+b+c
  change (rounds free).card ≤ a at hFree
  change (rounds forced).card ≤ b at hForced
  change (rounds deficient).card ≤ c at hDeficient
  omega

omit [Fintype V] in
/-- A forced appearance is charged to an edge that is deleted in its
round. Once removed, that edge cannot pay for another appearance. -/
theorem projection_load_le_of_virtual_deletions_of_free_load
    (S T P : ℕ → SimpleGraph V) (all free forced deficient : ℕ → Finset V)
    (W inherited : Finset V) (m cap c : ℕ) (v : V)
    (hClean : ∀ i < m,T i ≤ S i) (hPrescribed : ∀ i < m,P i ≤ T i)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i))
    (hSplit : ∀ i < m,v ∈ all i → v ∈ free i ∨ v ∈ forced i ∨ v ∈ deficient i)
    (hFree : projectionLoad (range m) free v ≤ cap)
    (hForced : ∀ i < m,v ∈ forced i → ∃ w ∈ W∪inherited,(P i).Adj v w)
    (hDeficient : projectionLoad (range m) deficient v ≤ c) :
    projectionLoad (range m) all v ≤ cap+(W.card+inherited.card)+c := by
  have hMono (i j : ℕ) (hij : i ≤ j) (hj : j ≤ m) : S j ≤ S i := by
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      rw [hi]
    | succ j ih =>
      by_cases he : i = j+1
      · rw [he]
      · have hlt : j < m := by omega
        rw [hNext j hlt]
        exact (show sdiff (T j) (P j) ≤ T j from fun _ _ h => h.1).trans
          ((hClean j hlt).trans (ih (by omega) hlt.le))
  have hDis (i : ℕ) (hi : i < m) (j : ℕ) (hj : j < m) (hne : i ≠ j) : Disjoint (P i) (P j) := by
    have hBefore (a b : ℕ) (hab : a < b) (hb : b < m) : Disjoint (P a) (P b) := by
      rw [disjoint_iff_inf_le]
      intro u w he
      have hLater := ((hPrescribed b hb).trans (hClean b hb)).trans
        (hMono (a+1) b (by omega) hb.le) he.2
      rw [hNext a (hab.trans hb)] at hLater
      exact hLater.2 he.1
    rcases lt_or_gt_of_ne hne with h | h
    · exact hBefore i j h hj
    · exact (hBefore j i h hi).symm
  exact projection_load_le_sum_of_three_charges all free forced deficient m v cap
    (W.card+inherited.card) c hSplit hFree
    (forced_projection_load_le_of_disjoint_edges forced P m v W inherited hDis hForced) hDeficient

omit [Fintype V] in
theorem projection_load_le_of_virtual_deletions
    (S T P : ℕ → SimpleGraph V) (all free forced deficient : ℕ → Finset V)
    (W inherited : Finset V) (m cap c : ℕ) (v : V)
    (hClean : ∀ i < m,T i ≤ S i) (hPrescribed : ∀ i < m,P i ≤ T i)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i))
    (hSplit : ∀ i < m,v ∈ all i → v ∈ free i ∨ v ∈ forced i ∨ v ∈ deficient i)
    (hFree : ∀ i < m,∀ u ∈ free i,projectionLoad (range i) free u < cap)
    (hForced : ∀ i < m,v ∈ forced i → ∃ w ∈ W∪inherited,(P i).Adj v w)
    (hDeficient : projectionLoad (range m) deficient v ≤ c) :
    projectionLoad (range m) all v ≤ cap+(W.card+inherited.card)+c :=
  projection_load_le_of_virtual_deletions_of_free_load S T P all free forced deficient W inherited m cap c v
    hClean hPrescribed hNext hSplit (projection_load_le_of_avoid_saturated free m cap hFree m le_rfl v)
    hForced hDeficient

end OverfullWork.CMSTrimmingRound
