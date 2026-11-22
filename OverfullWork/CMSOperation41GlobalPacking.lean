module

public import OverfullWork.CMSOperation41GlobalHistory

@[expose] public section


/-! Bound the visits of the ordinary host over the common Operation 4.1
history, including the boundary cleanup and reselected pair. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing RobustExpansion DirectedSpanningConfiguration DirectedReserveUsage
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge SimpleGraph.instDecidableMapAdj SimpleGraph.fintypeEdgeSetSdiff

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every cleanup incidence at an ordinary vertex uses a different
edge to the original exceptional set. The cleanup sets may change. -/
theorem ordinary_cleanup_budget_of_history (U : Finset V)
    (S T P : ℕ → SimpleGraph V) (W : ℕ → Finset V) (m : ℕ)
    (hW : ∀ i < m,W i ⊆ U)
    (hClean : ∀ i < m,DeletionRun (W i) (S i) (T i))
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i)) :
    ∀ j ≤ m,∀ v,v ∉ U → (∑ i ∈ range j,(sdiff (S i) (T i)).degree v) ≤ U.card := by
  let removed (i : ℕ) := sdiff (S i) (T i)
  have hLe (i : ℕ) (hi : i < m) : T i ≤ S i := DeletionRun.le_source (hClean i hi)
  have hDecrease := virtual_trimming_prefix_le S T P m hLe hNext
  have hBefore (i k : ℕ) (hik : i < k) (hk : k < m) : Disjoint (removed i) (removed k) := by
    rw [disjoint_iff_inf_le]
    intro a b h
    have hLater := hDecrease (i+1) k (Nat.succ_le_of_lt hik) hk.le h.2.1
    rw [hNext i (hik.trans hk)] at hLater
    exact h.1.2 hLater.1
  intro j hj v hv
  let J := usedTrimmingPrefix removed j
  have hSum : J.degree v = ∑ i : Fin j,(removed i.val).degree v := by
    apply degree_of_disjoint_trimming_prefix
    intro i hi k hk hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hBefore i k h (hk.trans_le hj)
    · exact (hBefore k i h (hi.trans_le hj)).symm
  rw [Fin.sum_univ_eq_sum_range (fun i => (removed i).degree v) j] at hSum
  change (∑ i ∈ range j,(removed i).degree v) ≤ U.card
  rw [←hSum,←card_neighborFinset_eq_degree]
  apply card_le_card
  intro x hx
  obtain ⟨i,hi⟩ := iSup_adj.mp ((mem_neighborFinset J v x).mp hx)
  have hi' := i.isLt.trans_le hj
  have hUsed := cleanup_removed_edge_meets_active (hClean i hi') hi
  exact hW i hi' (hUsed.resolve_left (fun h => hv (hW i hi' h)))

set_option maxHeartbeats 3000000 in
/-- Telescoping the ordinary degree record bounds both the accumulated
credits and the loss from the initial ordinary degree floor. -/
theorem TrimmingPackingSegment.ordinary_credit_budget
    {G : SimpleGraph V} [dG : DecidableRel G.Adj] {initial : Finset V} {test cap m a : ℕ}
    {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish) (hG : start.graph = G)
    (hRoom : 2*m ≤ G.maxDegree) (hDegree : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+a) :
    let S (i : ℕ) := (H.states i).graph
    let T := H.cleanedGraph
    let P := prescribedTrimmingHistory initial T H.layoutSize H.layoutWords
    let credit := trimmingCreditHistory initial T H.layoutSize H.layoutWords H.layoutOmitted
    let degree (i : ℕ) := auxiliaryPhysicalDegree (S i) initial P credit i
    ∀ j ≤ m,∀ v,v ∉ initial →
      (∑ i ∈ range j,credit i v) ≤ a+initial.card ∧
      G.maxDegree-2*j ≤ degree j v+a+initial.card ∧
      degree j v ≤ G.maxDegree-2*j := by
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  intro S T P credit degree
  obtain ⟨hStart,hW,hClean,hNext,_,_,_,_,hCap,_,hSize,_,_,_⟩ := H.packing_inputs hG
  have hLoss := ordinary_cleanup_budget_of_history initial S T P H.cleanupSet m hW hClean hNext
  intro j hj v hv
  let loss (i : ℕ) := (sdiff (S i) (T i)).degree v
  have hStep (i : ℕ) (hi : i < m) :
      degree (i+1) v = degree i v-(loss i+(2-credit i v)) ∧
      degree (i+1) v ≤ G.maxDegree-2*(i+1) ∧ credit i v ≤ 2 := by
    let C := sdiff (S i) (T i)
    have hTLe : T i ≤ S i := DeletionRun.le_source (hClean i hi)
    have hC : C ≤ S i := sdiff_le
    have hT : sdiff (S i) C = T i := sdiff_sdiff_eq_self hTLe
    have hP : P i = (H.layoutWords ⟨i,hi⟩).prescribedGraph := dif_pos hi
    have hCredit : credit i = (H.layoutWords ⟨i,hi⟩).degreeCredit (H.layoutOmitted ⟨i,hi⟩) := by
      funext w
      exact dif_pos hi
    have hPLe : P i ≤ sdiff (S i) C := by
      rw [hT,hP]
      exact (H.layoutWords ⟨i,hi⟩).prescribedGraph_le
    have hDebit (w : V) (hw : w ∉ initial) : (P i).degree w ≤ 2-credit i w := by
      rw [hP,hCredit]
      exact (H.layoutWords ⟨i,hi⟩).prescribed_degree_le_core_debit _
        ((hSize ⟨i,hi⟩).2) hw
    have hRead := auxiliary_physical_degree_after_round (S i) C initial P credit i hC hPLe hDebit v
    have hNext' : S (i+1) = sdiff (T i) (P i) := hNext i hi
    simp only [hT,if_neg hv,←hNext'] at hRead
    have hSub : auxiliaryPhysicalDegree (T i) initial P credit i v = degree i v-loss i :=
      auxiliary_physical_degree_after_cleanup (S i) (T i) initial P credit i hTLe v
    have hUpper : auxiliaryPhysicalDegree (T i) initial P credit i v+credit i v ≤ G.maxDegree-2*i :=
      hCap i hi v
    have hCreditTwo : credit i v ≤ 2 := by
      rw [hCredit]
      exact (H.layoutWords ⟨i,hi⟩).degree_credit_le_two _ _
    change degree (i+1) v = degree i v-(loss i+(2-credit i v)) at hRead
    refine ⟨hRead,?_,hCreditTwo⟩
    omega
  have hZero : degree 0 v = G.degree v := by
    have hS : S 0 = G := hStart
    simp [degree,auxiliaryPhysicalDegree]
    exact congrArg (fun Q : SimpleGraph V => Q.degree v) hS
  have hTel (k : ℕ) (hk : k ≤ m) :
      degree 0 v+(∑ i ∈ range k,credit i v) ≤
        degree k v+2*k+(∑ i ∈ range k,loss i) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' := Nat.lt_of_succ_le hk
      have hp := ih hk'.le
      obtain ⟨hNext,_,hCredit⟩ := hStep k hk'
      rw [sum_range_succ,sum_range_succ]
      omega
  have hFinal : degree j v ≤ G.maxDegree-2*j := by
    cases j with
    | zero => simpa only [hZero,Nat.mul_zero,Nat.sub_zero] using G.degree_le_maxDegree v
    | succ j =>
      have h := (hStep j (Nat.lt_of_succ_le hj)).2.1
      exact h
  have hBalance := hTel j hj
  rw [hZero] at hBalance
  have hLost : (∑ i ∈ range j,loss i) ≤ initial.card := hLoss j hj v hv
  have hAt := hDegree v hv
  have hRoom' := (Nat.mul_le_mul_left 2 hj).trans hRoom
  exact ⟨by omega,by omega,hFinal⟩

set_option maxHeartbeats 3000000 in
/-- The three charges give the uniform visit bound for the layouts
used by Lemma 3.14. Omitted ordinary vertices pay a positive credit. -/
theorem TrimmingPackingSegment.layout_visit_bound
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial : Finset V} {test cap m a : ℕ}
    {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish) (hG : start.graph = G)
    (hRoom : 2*m ≤ G.maxDegree) (hDegree : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+a)
    (hFree : ∀ v,projectionLoad (range m) finish.used v ≤ cap) :
    let B (i : Fin m) := univ.image (H.layoutWords i).endpoint ∪ H.layoutOmitted i
    (∀ i,(B i).card+2 ≤ 2*initial.card+5) ∧
    (∀ v,visits B v ≤ cap+a+2*initial.card) := by
  intro B
  obtain ⟨_,_,hClean,hNext,_,_,_,hMass,_,_,hSize,_,hPaid,_⟩ := H.packing_inputs hG
  let S (i : ℕ) := (H.states i).graph
  let T := H.cleanedGraph
  let P := prescribedTrimmingHistory initial T H.layoutSize H.layoutWords
  let credit := trimmingCreditHistory initial T H.layoutSize H.layoutWords H.layoutOmitted
  constructor
  · intro i
    have hE : (univ.image (H.layoutWords i).endpoint).card ≤ 2*(initial.card+1) := by
      have h := card_image_le (s := (univ : Finset (Fin (H.layoutSize i) × Bool)))
        (f := (H.layoutWords i).endpoint)
      rw [card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
      exact h.trans (by have := (hSize i).1; omega)
    have hO := hMass i
    have hB := card_union_le (univ.image (H.layoutWords i).endpoint) (H.layoutOmitted i)
    change (B i).card ≤ _ at hB
    omega
  intro x
  let v := x.val
  have hv : v ∉ initial := mem_compl.mp x.property
  let all (i : ℕ) : Finset V := if hi : i < m then (B ⟨i,hi⟩).image Subtype.val else ∅
  let forced (i : ℕ) := univ.filter (fun z => ∃ w ∈ initial,(P i).Adj z w)
  let deficient (i : ℕ) := univ.filter (fun z => 0 < credit i z)
  have hP (i : ℕ) (hi : i < m) : P i ≤ T i := by
    rw [show P i = (H.layoutWords ⟨i,hi⟩).prescribedGraph from dif_pos hi]
    exact (H.layoutWords ⟨i,hi⟩).prescribedGraph_le
  have hSplit (i : ℕ) (hi : i < m) (ha : v ∈ all i) :
      v ∈ finish.used i ∨ v ∈ forced i ∨ v ∈ deficient i := by
    rw [show all i = (B ⟨i,hi⟩).image Subtype.val from dif_pos hi] at ha
    obtain ⟨z,hz,hZ⟩ := mem_image.mp ha
    have hz' : z = x := Subtype.ext hZ
    subst z
    rcases mem_union.mp hz with hEndpoint | hOmit
    · obtain ⟨k,_,hk⟩ := mem_image.mp hEndpoint
      have h := hPaid ⟨i,hi⟩ k
      dsimp only at h
      rw [hk] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (mem_filter.mpr ⟨mem_univ _,h⟩))
      · exact Or.inr (Or.inr (mem_filter.mpr ⟨mem_univ _,h⟩))
    · right
      right
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      have hC : credit i v = (H.layoutWords ⟨i,hi⟩).degreeCredit (H.layoutOmitted ⟨i,hi⟩) x.val :=
        dif_pos hi
      rw [hC,(H.layoutWords ⟨i,hi⟩).degree_credit_eq_two_at_omitted_core _ x hOmit]
      decide
  have hCredit : (∑ i ∈ range m,credit i v) ≤ a+initial.card :=
    (H.ordinary_credit_budget hG hRoom hDegree m le_rfl v hv).1
  have hDef : projectionLoad (range m) deficient v ≤ a+initial.card := by
    apply le_trans _ hCredit
    rw [projectionLoad,card_filter]
    apply sum_le_sum
    intro i _
    by_cases h : v ∈ deficient i
    · rw [if_pos h]
      exact (mem_filter.mp h).2
    · rw [if_neg h]
      exact Nat.zero_le _
  have hCount := projection_load_le_of_virtual_deletions_of_free_load S T P all finish.used forced deficient
    initial ∅ m cap (a+initial.card) v (fun i hi => DeletionRun.le_source (hClean i hi)) hP hNext hSplit (hFree v)
    (fun i _ hi => by simpa only [union_empty] using (mem_filter.mp hi).2) hDef
  have hIncluded (i : Fin m) (z : ↥(initialᶜ : Finset V)) (hz : z ∈ B i) : z.val ∈ all i.val := by
    rw [show all i.val = (B i).image Subtype.val from dif_pos i.isLt]
    exact mem_image.mpr ⟨z,hz,rfl⟩
  have hVisits := core_layout_visits_le_projection_history (Function.Embedding.subtype _) B all hIncluded x
  simp only [card_empty,Nat.add_zero] at hCount
  change visits B x ≤ projectionLoad (range m) all v at hVisits
  omega

set_option maxHeartbeats 4000000 in
/-- Apply the uniform Lemma 3.14 packing to the actual Operation 4.1
history. Its density, round count, and visits all come from the
initial graph and the common history. -/
theorem cms_operation_4_1_packed_layouts (α gap ν τ : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hGap : 0 < gap) (hGapα : 6*gap ≤ α)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hHalfτ : τ ≤ 1/2) (hτGap : 32768*τ ≤ gap) :
    ∃ γ ρ : ℝ,0 < γ ∧ 0 < ρ ∧ ∃ N : ℕ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (η : ℝ) (hη : 0 ≤ η) (hSmall : η ≤ 1/64)
        (hVAL : ∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v)
        (test : ℕ) (hTest : 1 ≤ test),
        let n := Fintype.card V
        let initial := initialExceptionalSet G η
        let shift := η*(n:ℝ)
        let cap := ⌊shift⌋₊
        let long := ⌊(G.maxDegree:ℝ)/3-shift⌋₊
        let short := ⌊(G.maxDegree:ℝ)/3-2*shift⌋₊
        2*N ≤ n → 64 ≤ shift → 6 ≤ η^2*(n:ℝ) → (initial.card:ℝ) ≤ η^2*(n:ℝ) →
        24*η ≤ α → 6*η ≤ γ → 8*η^2 ≤ ν → 4*η^2 ≤ τ →
        α*(n:ℝ) ≤ (G.maxDegree:ℝ) → IsRealRobust G ν τ →
        ∃ m ≤ long,∃ start finish : VirtualTrimmingState V,
          start.graph = G ∧ 2*m ≤ G.maxDegree ∧
          ∃ K : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish,
            K.HasWeakDegreeSums (⌊2*shift⌋₊-2*initial.card) ∧
            ∃ last : TrimmingPackingTermination initial finish (G.maxDegree-2*m) test m cap
              (m = long ∨ short ≤ m), last.HasProfile ⌊6*shift⌋₊ ∧
            HasPackedCoreLayouts (G.induce (↑(initialᶜ : Finset V) : Set V)) K.layoutSize
              (fun i => (K.layoutWords i).endpoint) K.layoutOmitted ρ (2*τ) := by
  obtain ⟨γ,ρ,hγ,hρ,N,hPack⟩ := cms_operation_4_1_core_packing_uniform α gap (ν/2) (2*τ)
    hα hα₁ hGap (by linarith only [hGap,hGapα]) (by positivity)
    (by linarith only [hν,hντ]) (by linarith only [hτGap])
  refine ⟨γ,ρ,hγ,hρ,N,?_⟩
  intro V instV dV G dG
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  intro η hη hSmall hVAL test hTest n initial shift cap long short hn hShift hSize hFew
    hαη hγη hνη hτη hDense hRob
  have hn' : 0 < n := by
    by_contra! h
    have hZero : n = 0 := Nat.eq_zero_of_le_zero h
    simp only [shift,hZero,Nat.cast_zero,mul_zero] at hShift
    norm_num at hShift
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn'
  have hs0 : 0 ≤ shift := mul_nonneg hη hnR.le
  have hDenseShift : 24*shift ≤ (G.maxDegree:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hαη hnR.le
    exact (by simpa only [shift,mul_assoc] using h.trans hDense)
  obtain ⟨m,hm,start,finish,hG,K,hWeak,last,hProfile⟩ :=
    cms_operation_4_1_packing_history G η hη hSmall hVAL test hTest hShift hSize hDenseShift hFew
  change m ≤ long at hm
  change TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish at K
  change TrimmingPackingTermination initial finish (G.maxDegree-2*m) test m cap
    (m = long ∨ short ≤ m) at last
  let A : Finset V := initialᶜ
  let core := G.induce (A : Set V)
  let a := (G.maxDegree:ℝ)/(n:ℝ)
  have hAn : A.card+initial.card = n := by
    rw [Nat.add_comm]
    exact card_add_card_compl initial
  have hAnR : (A.card:ℝ)+(initial.card:ℝ) = (n:ℝ) := by exact_mod_cast hAn
  have hFew' : (initial.card:ℝ) ≤ shift/64 := by
    have h := mul_le_mul_of_nonneg_right hSmall hs0
    dsimp only [shift] at h ⊢
    nlinarith only [h,hFew]
  have hShiftLe : shift ≤ n := by
    have h := mul_le_mul_of_nonneg_right (show η ≤ 1 by linarith only [hSmall]) hnR.le
    simpa only [shift,one_mul] using h
  have hHalfR : (n:ℝ) ≤ 2*(A.card:ℝ) := by
    linarith only [hAnR,hFew',hShiftLe,hnR.le]
  have hHalf : n ≤ 2*A.card := by exact_mod_cast hHalfR
  have hCard : N ≤ Fintype.card ↥A := by rw [Fintype.card_coe]; omega
  have hRoom : 0 ≤ (G.maxDegree:ℝ)/3-shift := by linarith only [hDenseShift,hs0]
  have hRounds : (m:ℝ) ≤ (G.maxDegree:ℝ)/3-shift := by
    have hLe : (m:ℝ) ≤ long := by exact_mod_cast hm
    exact hLe.trans (Nat.floor_le hRoom)
  have hTrimmingRoom : 2*m ≤ G.maxDegree := by
    have hD0 : 0 ≤ (G.maxDegree:ℝ) := Nat.cast_nonneg _
    exact_mod_cast (show (2:ℝ)*m ≤ G.maxDegree by linarith only [hRounds,hs0,hD0])
  let threshold := ⌈shift⌉₊
  have hFloor : (cap:ℝ) ≤ shift := Nat.floor_le hs0
  have hCeil : (threshold:ℝ) ≤ shift+1 := (Nat.ceil_lt_add_one hs0).le
  have hOrd (v : V) (hv : v ∉ initial) : G.maxDegree ≤ G.degree v+threshold := by
    have hNot : (G.maxDegree:ℝ)-G.degree v ≤ shift := by
      by_contra! h
      exact hv (mem_filter.mpr ⟨mem_univ _,h⟩)
    have hCeil' : shift ≤ (threshold:ℝ) := Nat.le_ceil _
    exact_mod_cast (show (G.maxDegree:ℝ) ≤ (G.degree v:ℝ)+threshold by linarith only [hNot,hCeil'])
  have hSmallν : 8*(initial.card:ℝ) ≤ ν*(n:ℝ) := by
    nlinarith only [hFew,mul_le_mul_of_nonneg_right hνη hnR.le]
  have hSmallτ : 4*(initial.card:ℝ) ≤ τ*(n:ℝ) := by
    nlinarith only [hFew,mul_le_mul_of_nonneg_right hτη hnR.le]
  obtain ⟨ha,ha₁,hDegreeCore,hRobCore⟩ := initial_core_density_and_robustness G α η ν τ
    hα hη (by linarith only [hSmall]) hν.le (by linarith only [hντ,hHalfτ])
    (hν.le.trans hντ) hHalfτ hn' hDense hFew hSmallν hSmallτ hRob
  have haD : a*(n:ℝ) = G.maxDegree := div_mul_cancel₀ _ hnR.ne'
  have hRoundCore := initial_round_limit_fits_core n G.maxDegree A.card initial.card m a η gap
    hAn haD (hα.le.trans ha) ha₁ (hGapα.trans ha) (by linarith only [hFew',hs0]) hRounds
  have hBudget : 3*shift ≤ γ*(A.card:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hHalfR (show 0 ≤ 3*η by positivity)
    have h' := mul_le_mul_of_nonneg_right hγη (Nat.cast_nonneg (α := ℝ) A.card)
    dsimp only [shift]
    linarith only [h,h']
  have hFree : ∀ v,projectionLoad (range m) finish.used v ≤ cap := last.free_load
  have hLayout := @TrimmingPackingSegment.layout_visit_bound V instV dV G
    (fun u v => Classical.propDecidable (G.Adj u v))
    initial test cap m threshold start finish K hG hTrimmingRoom hOrd hFree
  obtain ⟨hB,hVisits⟩ := hLayout
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hRetained,_,_,_⟩ := TrimmingPackingSegment.packing_inputs (G := G) hG K
  have hDecEq : (fun x y : ↥A => Classical.propDecidable (x = y)) =
      (fun x y : ↥A => Subtype.instDecidableEq x y) := Subsingleton.elim _ _
  refine ⟨m,hm,start,finish,hG,hTrimmingRoom,K,hWeak,last,hProfile,?_⟩
  change HasPackedCoreLayouts core K.layoutSize (fun i => (K.layoutWords i).endpoint)
    K.layoutOmitted ρ (2*τ)
  refine @hPack ↥A _ (Fin m) _ core _ a K.layoutSize (fun i => (K.layoutWords i).endpoint) K.layoutOmitted
    ha ha₁ hCard ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hDecEq]
    exact hRobCore
  · intro v
    rw [Fintype.card_coe]
    exact (hDegreeCore v).trans (mul_le_mul_of_nonneg_right (by linarith only [hγη,hη]) (Nat.cast_nonneg _))
  · simpa only [Fintype.card_fin,Fintype.card_coe] using hRoundCore
  · exact fun i => (hRetained i).2
  · intro i
    rw [hDecEq,Fintype.card_coe]
    have h := hB i
    have hR : (((univ.image (K.layoutWords i).endpoint ∪ K.layoutOmitted i).card+2:ℕ):ℝ)
        ≤ 2*(initial.card:ℝ)+5 := by exact_mod_cast h
    exact hR.trans ((by linarith only [hFew',hShift] : 2*(initial.card:ℝ)+5 ≤ 3*shift).trans hBudget)
  · intro v
    rw [hDecEq,Fintype.card_coe]
    have h := hVisits v
    have hR : (visits (fun i => univ.image (K.layoutWords i).endpoint ∪ K.layoutOmitted i) v:ℝ) ≤
        (cap:ℝ)+threshold+2*(initial.card:ℝ) := by exact_mod_cast h
    push_cast
    linarith only [hR,hFloor,hCeil,hFew',hShift,hBudget]

/-- The final preprocessing has the same effect on the virtual
record and on the physical graph with its packed core edges removed. -/
theorem TrimmingPackingTermination.physical_stop
    {initial : Finset V} {S : VirtualTrimmingState V} {d test j cap : ℕ} {atLimit : Prop}
    (last : TrimmingPackingTermination initial S d test j cap atLimit) (C : SimpleGraph V)
    (hCore : ∀ v ∈ initial,∀ u,¬C.Adj v u)
    (hRead : ∀ v,S.record initial j v = (sdiff S.graph C).degree v) :
    let before := sdiff S.graph C
    let after := sdiff last.cleaned C
    (∀ v,auxiliaryPhysicalDegree last.cleaned initial S.prescribed S.credit j v = after.degree v) ∧
      (atLimit ∨ HasAlmostOverfullRecord (univ.filter (fun v => 0 < after.degree v)) d test
        (fun v => after.degree v)) ∧
      (before.maxDegree = d → ¬before.EdgeColorable before.maxDegree →
        DeletionRun last.cleanupSet before after ∧ after ≤ before ∧
          after.maxDegree = d ∧ ¬after.EdgeColorable after.maxDegree) := by
  intro before after
  let deleted := sdiff S.graph last.cleaned
  obtain ⟨hDeleted,hAfter⟩ := trimming_cleanup_after_core_removal last.cleanup last.cleanup_subset C hCore
  change sdiff before deleted = after at hAfter
  have hDegree (v : V) :
      auxiliaryPhysicalDegree last.cleaned initial S.prescribed S.credit j v = after.degree v := by
    have hFirst : after.degree v+deleted.degree v = before.degree v := by
      simpa only [hAfter,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le before deleted hDeleted v
    rw [auxiliary_physical_degree_after_cleanup S.graph last.cleaned initial S.prescribed S.credit j
      (DeletionRun.le_source last.cleanup) v]
    have hRead' : auxiliaryPhysicalDegree S.graph initial S.prescribed S.credit j v = before.degree v :=
      hRead v
    rw [hRead']
    change before.degree v-deleted.degree v = after.degree v
    omega
  refine ⟨hDegree,?_,?_⟩
  · have hEq := funext hDegree
    have hStop := last.stop
    change atLimit ∨ HasAlmostOverfullRecord
      (univ.filter (fun v => 0 < auxiliaryPhysicalDegree last.cleaned initial S.prescribed S.credit j v))
      d test (auxiliaryPhysicalDegree last.cleaned initial S.prescribed S.credit j) at hStop
    simpa only [hEq] using hStop
  · intro hMax hNo
    have hSmall (w : V) (hw : w ∈ last.cleanupSet) : before.degree w < before.maxDegree := by
      rw [hMax,←hRead w]
      rw [VirtualTrimmingState.record,auxiliaryPhysicalDegree,if_pos (last.cleanup_subset hw)]
      exact last.cleanup_below_target w hw
    obtain ⟨hRun,hLe,hAfterMax,hAfterNo⟩ :=
      exact_replay_away_from_core_removals last.cleanup last.cleanup_subset hCore hSmall hNo
    exact ⟨hRun,hLe,hAfterMax.trans hMax,hAfterNo⟩

/-- Numerical margins on the degree records used to transfer
Claim 4.2(4) to every realized prefix. -/
def TrimmingPackingSegment.HasClaim42Margins
    {initial : Finset V} {D test cap m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial D test cap 0 m start finish) (r t b a : ℕ) : Prop :=
  ∀ i < m,
    let d := D-2*i
    let degree := (H.states i).record initial i
    t+initial.card+2 ≤ d ∧ d ≤ (r-initial.card)*(r-initial.card) ∧
    (∀ u v,(H.states i).graph.Adj u v → (u ∈ initial ∨ v ∈ initial) → d-b ≤ degree u+degree v) ∧
    (∀ v,v ∉ initial → d ≤ degree v+a) ∧
    3*b+6*(t+2*initial.card+2) ≤ d ∧ 2*a+2*(t+2*initial.card+2) ≤ d

/-- Check the scalar constraints at the endpoints of the round range.
The ordinary record floor throughout the range follows from the
accumulated credit calculation. -/
theorem TrimmingPackingSegment.claim42_margins
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial : Finset V}
    {test cap m : ℕ} {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish) (hG : start.graph = G)
    (r t b a : ℕ) (hRoom : 2*m ≤ G.maxDegree) (hWeak : H.HasWeakDegreeSums b)
    (hOrd : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+a)
    (hSquare : G.maxDegree ≤ (r-initial.card)*(r-initial.card))
    (hB : 3*b+6*(t+2*initial.card+2) ≤ G.maxDegree-2*m)
    (hA : 2*(a+initial.card)+2*(t+2*initial.card+2) ≤ G.maxDegree-2*m) :
    H.HasClaim42Margins r t b (a+initial.card) := by
  let S (i : ℕ) := (H.states i).graph
  let T := H.cleanedGraph
  let P := prescribedTrimmingHistory initial T H.layoutSize H.layoutWords
  let credit := trimmingCreditHistory initial T H.layoutSize H.layoutWords H.layoutOmitted
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hRead,_,_⟩ := H.packing_inputs hG
  have hBound := H.ordinary_credit_budget hG hRoom hOrd
  intro i hi
  have hLower : G.maxDegree-2*m ≤ G.maxDegree-2*i :=
    Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 hi.le) _
  refine ⟨by omega,(Nat.sub_le _ _).trans hSquare,?_,?_,hB.trans hLower,hA.trans hLower⟩
  · intro u v hEdge _
    have h := hWeak i hi.le u v hEdge
    simp only [Nat.zero_add] at h
    omega
  · intro v hv
    have h : G.maxDegree-2*i ≤ auxiliaryPhysicalDegree (S i) initial P credit i v+a+initial.card :=
      (hBound i hi.le v hv).2.1
    rw [hRead i hi.le (S i)] at h
    simpa only [VirtualTrimmingState.record,Nat.add_assoc] using h

set_option maxHeartbeats 3600000 in
/-- Realize the indexed prescriptions as two-colour layers. Each
physical prefix and the final cleaned graph retain the core reserve.
The class-two obstruction persists through every certified cleanup. -/
theorem TrimmingPackingSegment.realize_layouts
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial : Finset V} {test cap m : ℕ}
    {start finish : VirtualTrimmingState V}
    (H : TrimmingPackingSegment initial G.maxDegree test cap 0 m start finish) (hG : start.graph = G)
    {atLimit : Prop}
    (last : TrimmingPackingTermination initial finish (G.maxDegree-2*m) test m cap atLimit)
    (ρ τ : ℝ)
    (hPack : HasPackedCoreLayouts (G.induce (↑(initialᶜ : Finset V) : Set V)) H.layoutSize
      (fun i => (H.layoutWords i).endpoint) H.layoutOmitted ρ τ) :
    let S (i : ℕ) := (H.states i).graph
    let T := H.cleanedGraph
    let P := prescribedTrimmingHistory initial T H.layoutSize H.layoutWords
    let credit := trimmingCreditHistory initial T H.layoutSize H.layoutWords H.layoutOmitted
    ∃ (R : SimpleGraph ↥(initialᶜ : Finset V)) (L : ℕ → SimpleGraph V),
      let physical (i : ℕ) := sdiff (S i) (usedTrimmingPrefix L i)
      let cleaned (i : ℕ) := sdiff (T i) (usedTrimmingPrefix L i)
      let terminal := sdiff last.cleaned (usedTrimmingPrefix L m)
      R ≤ G.induce (↑(initialᶜ : Finset V) : Set V) ∧ IsRealRobust R ρ τ ∧
      (∀ r t : ℕ,IsRobustAt R r t → ∀ i ≤ m,IsRobustAt (physical i) (r-initial.card) (t+initial.card)) ∧
      (∀ r t : ℕ,IsRobustAt R r t → IsRobustAt terminal (r-initial.card) (t+initial.card)) ∧
      (∀ i < m,P i ⊔ L i ≤ cleaned i ∧ (P i ⊔ L i).EdgeColorable 2 ∧
        physical (i+1) = sdiff (cleaned i) (P i ⊔ L i) ∧
        ∀ v,(P i ⊔ L i).degree v+credit i v = 2) ∧
      (∀ i ≤ m,∀ v,(H.states i).record initial i v = (physical i).degree v) ∧
      (∀ i < m,∀ v,auxiliaryPhysicalDegree (T i) initial (H.states i).prescribed (H.states i).credit i v =
        (cleaned i).degree v) ∧
      (∀ v,auxiliaryPhysicalDegree last.cleaned initial finish.prescribed finish.credit m v =
        terminal.degree v) ∧
      (atLimit ∨ HasAlmostOverfullRecord (univ.filter (fun v => 0 < terminal.degree v))
        (G.maxDegree-2*m) test (fun v => terminal.degree v)) ∧
      (∀ budget,H.HasWeakDegreeSums budget →
        (∀ i ≤ m,∀ u v,(physical i).Adj u v →
          G.maxDegree-2*i ≤ (physical i).degree u+(physical i).degree v+budget) ∧
        (∀ u v,terminal.Adj u v →
          G.maxDegree-2*m ≤ terminal.degree u+terminal.degree v+(budget+2*initial.card))) ∧
      (2*m ≤ G.maxDegree → ¬G.EdgeColorable G.maxDegree →
        (∀ i ≤ m,(physical i).maxDegree = G.maxDegree-2*i ∧
          ¬(physical i).EdgeColorable (physical i).maxDegree) ∧
        (DeletionRun last.cleanupSet (physical m) terminal ∧ terminal ≤ physical m ∧
          terminal.maxDegree = G.maxDegree-2*m ∧ ¬terminal.EdgeColorable terminal.maxDegree) ∧
        (∀ r t b a : ℕ,IsRobustAt R r t → ¬G.HasOverfullSubgraph → 6*initial.card+6 ≤ test →
          H.HasClaim42Margins r t b a →
          (∀ i ≤ m,¬(physical i).HasOverfullSubgraph) ∧ ¬terminal.HasOverfullSubgraph)) := by
  intro S T P credit
  obtain ⟨hStart,hW,hClean,hNext,hInd,hEmpty,hParity,hMass,hCap,hNoStop,_,hRead,_,_⟩ :=
    H.packing_inputs hG
  obtain ⟨R,L,hRLe,hRob,hProtected,hInner,hRobust,hLayer,hBefore,hAfter,_,_,hClaims⟩ :=
    packed_operation_4_1_history G initial S T H.cleanupSet m H.layoutSize H.layoutWords H.layoutOmitted
      ρ τ hStart hW hClean hNext hEmpty hPack hParity
  let C := usedTrimmingPrefix L m
  have hS : S m = finish.graph := congrArg VirtualTrimmingState.graph H.finishes
  have hRecord (i : ℕ) (hi : i ≤ m) (v : V) :
      (H.states i).record initial i v = (sdiff (S i) (usedTrimmingPrefix L i)).degree v :=
    (congrFun (hRead i hi (S i)) v).symm.trans (hBefore i hi v)
  have hEndRecord (v : V) : finish.record initial m v = (sdiff finish.graph C).degree v := by
    have h := hRecord m le_rfl v
    rw [H.finishes,hS] at h
    exact h
  have hNoCore (v : V) (hv : v ∈ initial) (u : V) : ¬C.Adj v u := by
    intro h
    obtain ⟨i,hi⟩ := iSup_adj.mp h
    exact (hInner i i.isLt v u hi).1 hv
  obtain ⟨hEndDegree,hEndStop,hEndClass⟩ := last.physical_stop C hNoCore hEndRecord
  have hEdge (i : ℕ) (hi : i < m) (u v : V) (h : (P i).Adj u v) :
      u ∈ initial ∨ v ∈ initial := by
    rw [show P i = (H.layoutWords ⟨i,hi⟩).prescribedGraph from dif_pos hi] at h
    exact (H.layoutWords ⟨i,hi⟩).prescribedGraph_meets_exceptional_set
      (hEmpty ⟨i,hi⟩) _ _ h
  have hCore := (auxiliary_trimming_preserves_core G initial S T P H.cleanupSet m
    hStart hW hClean hEdge hNext).1 m le_rfl
  rw [hS] at hCore
  have hEndCore (u v : V) (hu : u ∉ initial) (hv : v ∉ initial) :
      last.cleaned.Adj u v ↔ G.Adj u v := by
    apply Iff.trans _ (hCore u v hu hv)
    refine ⟨fun h => DeletionRun.le_source last.cleanup h,fun h => ?_⟩
    by_contra! hNo
    rcases cleanup_removed_edge_meets_active last.cleanup (show (sdiff finish.graph last.cleaned).Adj u v
      from ⟨h,hNo⟩) with hU | hV
    · exact hu (last.cleanup_subset hU)
    · exact hv (last.cleanup_subset hV)
  refine ⟨R,L,hRLe,hRob,hRobust,?_,hLayer,hRecord,?_,hEndDegree,hEndStop,?_,?_⟩
  · intro r t hAt
    exact robust_physical_prefix_of_core_reserve G last.cleaned initial L m R hEndCore hRLe
      hProtected r t hAt
  · intro i hi v
    exact (congrFun (hRead i hi.le (T i)) v).symm.trans (hAfter i hi v)
  · intro budget hWeak
    constructor
    · intro i hi u v hEdge
      have h := hWeak i hi u v hEdge.1
      simpa only [Nat.zero_add,hRecord i hi] using h
    · intro u v hEdge
      have h : finish.HasWeakDegreeSum initial m (G.maxDegree-2*m) budget := by
        simpa only [H.finishes,Nat.zero_add] using hWeak m le_rfl
      have h' := last.weak_degree_sum h u v hEdge.1
      simpa only [VirtualTrimmingState.record,hEndDegree] using h'
  · intro hRoom hNo
    obtain ⟨hClass,hAbsence⟩ := hClaims hRoom hNo H.cleanup_below_target (fun i hi v _ => hCap i hi v)
    obtain ⟨hMax,hNC⟩ := hClass m le_rfl
    have hEnd := hEndClass
      (show (sdiff finish.graph C).maxDegree = G.maxDegree-2*m from by simpa only [←hS] using hMax)
      (show ¬(sdiff finish.graph C).EdgeColorable (sdiff finish.graph C).maxDegree from by
        simpa only [←hS] using hNC)
    refine ⟨hClass,by simpa only [←hS] using hEnd,?_⟩
    intro r t b a hRobAt hNoOver hTest hMargins
    have hNoPrefix := hAbsence r t b a test hRobAt hNoOver hTest hMass
      (fun i hi => Or.inl (hInd i hi)) (by
        intro i hi
        obtain ⟨hWindow,hSquares,hWeak,hOrd,hM₁,hM₂⟩ := hMargins i hi
        have ht : t+initial.card+initial.card+2 = t+2*initial.card+2 := by omega
        refine ⟨hWindow,hSquares,?_,?_,by simpa only [ht] using hM₁,
          by simpa only [ht] using hM₂,hNoStop i hi⟩
        · intro u v hEdge hMem
          change G.maxDegree-2*i-b ≤ auxiliaryPhysicalDegree (S i) initial P credit i u+
            auxiliaryPhysicalDegree (S i) initial P credit i v
          rw [hRead i hi.le (S i)]
          exact hWeak u v hEdge hMem
        · intro v hv
          change G.maxDegree-2*i ≤ auxiliaryPhysicalDegree (S i) initial P credit i v+a
          rw [hRead i hi.le (S i)]
          exact hOrd v hv)
    refine ⟨hNoPrefix,?_⟩
    rintro ⟨A,hOver⟩
    apply hNoPrefix m le_rfl
    refine ⟨A,?_⟩
    have hSub : sdiff last.cleaned C ≤ sdiff (S m) C := by
      rw [hS]
      exact hEnd.2.1
    have hEndMax : (sdiff last.cleaned C).maxDegree = (sdiff (S m) C).maxDegree :=
      hEnd.2.2.1.trans hMax.symm
    rw [←hEndMax]
    apply hOver.trans_le
    apply card_le_card
    intro e he
    obtain ⟨hMem,hA⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hSub (mem_edgeFinset.mp hMem)),hA⟩

end OverfullWork.CMSTrimmingRound
