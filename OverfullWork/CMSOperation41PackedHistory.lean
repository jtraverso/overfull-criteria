module

public import OverfullWork.CMSOperation41PhysicalLayerFamily
public import OverfullWork.CMSOperation41CutSupport
public import OverfullWork.CMSOperation41CumulativeCleanup
public import OverfullWork.CMSOperation41ExactRecords
public import OverfullWork.CMSOperation41CoreReserve
public import OverfullWork.CMSOperation41CoreCreditMass
public import OverfullWork.CMSOperation41SafePrefixStep

@[expose] public section


/-! Read the physical prefix degrees from a virtual trimming history.
The true core edges are supplied all at once. Preservation of class two
is then a degree check on the virtual record and its prescribed credits. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph RobustExpansion DirectedSpanningConfiguration LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge SimpleGraph.instDecidableMapAdj

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def prescribedTrimmingHistory (U : Finset V) {m : ℕ} (T : ℕ → SimpleGraph V)
    (f : Fin m → ℕ) (words : ∀ i : Fin m,TrimmingReplacementWords (T i.val) U (Fin (f i)))
    (i : ℕ) : SimpleGraph V :=
  if hi : i < m then (words ⟨i,hi⟩).prescribedGraph else ⊥

noncomputable def trimmingCreditHistory (U : Finset V) {m : ℕ} (T : ℕ → SimpleGraph V)
    (f : Fin m → ℕ) (words : ∀ i : Fin m,TrimmingReplacementWords (T i.val) U (Fin (f i)))
    (omitted : Fin m → Finset ↥(Uᶜ : Finset V)) (i : ℕ) (v : V) : ℕ :=
  if hi : i < m then (words ⟨i,hi⟩).degreeCredit (omitted ⟨i,hi⟩) v else 2

set_option maxHeartbeats 6000000 in
theorem packed_operation_4_1_history (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (S T : ℕ → SimpleGraph V) (W : ℕ → Finset V) (m : ℕ)
    (f : Fin m → ℕ) (words : ∀ i : Fin m,TrimmingReplacementWords (T i.val) U (Fin (f i)))
    (omitted : Fin m → Finset ↥(Uᶜ : Finset V)) (ρ τ : ℝ) :
    let host := G.induce (↑(Uᶜ : Finset V) : Set V)
    let P := prescribedTrimmingHistory U T f words
    let credit := trimmingCreditHistory U T f words omitted
    S 0 = G →
    (∀ i < m,W i ⊆ U) → (∀ i < m,DeletionRun (W i) (S i) (T i)) →
    (∀ i < m,S (i+1) = sdiff (T i) (P i)) →
    (∀ (i : Fin m) k,(words i).body k = [] →
      s(((words i).endpoint (k,false)).val,((words i).endpoint (k,true)).val) ∈ (words i).gaps) →
    HasPackedCoreLayouts host f (fun i => (words i).endpoint) omitted ρ τ →
    (∀ i,
      let len := (Uᶜ : Finset V).card-(omitted i).card+∑ k,((words i).body k).length
      3 ≤ len ∧ (Even len ∨ (words i).gaps.Nonempty)) →
    ∃ (R : SimpleGraph ↥(Uᶜ : Finset V)) (L : ℕ → SimpleGraph V),
      R ≤ host ∧ IsRealRobust R ρ τ ∧
      (∀ i < m,∀ a b,R.Adj a b → ¬(L i).Adj a.val b.val) ∧
      (∀ i < m,∀ u v,(L i).Adj u v → u ∉ U ∧ v ∉ U) ∧
      (∀ r t : ℕ,IsRobustAt R r t → ∀ j ≤ m,
        IsRobustAt (sdiff (S j) (usedTrimmingPrefix L j)) (r-U.card) (t+U.card)) ∧
      (∀ i < m,
        P i ⊔ L i ≤ sdiff (T i) (usedTrimmingPrefix L i) ∧ (P i ⊔ L i).EdgeColorable 2 ∧
        sdiff (S (i+1)) (usedTrimmingPrefix L (i+1)) =
          sdiff (sdiff (T i) (usedTrimmingPrefix L i)) (P i ⊔ L i) ∧
        ∀ v,(P i ⊔ L i).degree v+credit i v = 2) ∧
      (∀ j ≤ m,∀ v,auxiliaryPhysicalDegree (S j) U P credit j v =
        (sdiff (S j) (usedTrimmingPrefix L j)).degree v) ∧
      (∀ j < m,∀ v,auxiliaryPhysicalDegree (T j) U P credit j v =
        (sdiff (T j) (usedTrimmingPrefix L j)).degree v) ∧
      (∀ i < m,∀ v,auxiliaryPhysicalDegree (T i) U P credit i v+
        (sdiff (S i) (T i)).degree v = auxiliaryPhysicalDegree (S i) U P credit i v) ∧
      (∀ i < m,∀ v,auxiliaryPhysicalDegree (S (i+1)) U P credit (i+1) v+
        (sdiff (S i) (T i)).degree v+(2-credit i v) = auxiliaryPhysicalDegree (S i) U P credit i v) ∧
      (2*m ≤ G.maxDegree → ¬G.EdgeColorable G.maxDegree →
        (∀ i < m,∀ w ∈ W i,(S i).degree w < G.maxDegree-2*i) →
        (∀ i < m,∀ v,0 < credit i v →
          auxiliaryPhysicalDegree (T i) U P credit i v+credit i v ≤ G.maxDegree-2*i) →
        (∀ i ≤ m,
          let H := sdiff (S i) (usedTrimmingPrefix L i)
          H.maxDegree = G.maxDegree-2*i ∧ ¬H.EdgeColorable H.maxDegree) ∧
        (∀ r t b a B : ℕ,IsRobustAt R r t → ¬G.HasOverfullSubgraph →
          6*U.card+6 ≤ B →
          (∀ i : Fin m,(omitted i).card+(words i).coreIncidentGaps.card ≤ 1) →
          (∀ i < m,(S i).IsIndepSet (W i : Set V) ∨ T i = S i) →
          (∀ i < m,
            let d := G.maxDegree-2*i
            let D := auxiliaryPhysicalDegree (S i) U P credit i
            let active := univ.filter (fun v => 0 < D v)
            t+U.card+2 ≤ d ∧ d ≤ (r-U.card)*(r-U.card) ∧
            (∀ u v,(S i).Adj u v → (u ∈ U ∨ v ∈ U) → d-b ≤ D u+D v) ∧
            (∀ v,v ∉ U → d ≤ D v+a) ∧
            3*b+6*(t+U.card+U.card+2) ≤ d ∧ 2*a+2*(t+U.card+U.card+2) ≤ d ∧
            ¬HasAlmostOverfullRecord active d B D) →
          ∀ i ≤ m,¬(sdiff (S i) (usedTrimmingPrefix L i)).HasOverfullSubgraph)) := by
  intro host P credit hFirst hW hClean hNext hEmpty hPack hParity
  have hP (i : ℕ) (hi : i < m) : P i = (words ⟨i,hi⟩).prescribedGraph := by
    simp only [P,prescribedTrimmingHistory,dif_pos hi]
  have hCredit (i : ℕ) (hi : i < m) (v : V) :
      credit i v = (words ⟨i,hi⟩).degreeCredit (omitted ⟨i,hi⟩) v := by
    simp only [credit,trimmingCreditHistory,dif_pos hi]
  have hOuter (i : ℕ) (hi : i < m) (x y : V) (h : (P i).Adj x y) : x ∈ U ∨ y ∈ U := by
    rw [hP i hi] at h
    exact (words ⟨i,hi⟩).prescribedGraph_meets_exceptional_set (hEmpty ⟨i,hi⟩) _ _ h
  obtain ⟨hCoreS,hCoreT⟩ := auxiliary_trimming_preserves_core G U S T P W m hFirst hW hClean hOuter hNext
  have hHost (i : Fin m) (a b : ↥(Uᶜ : Finset V)) (h : host.Adj a b) : (T i.val).Adj a.val b.val := by
    exact (hCoreT i.val i.isLt a.val b.val (mem_compl.mp a.property) (mem_compl.mp b.property)).mpr h
  obtain ⟨R,layer,hRLe,hRob,hDis,hInner,hAvoid,hLayers⟩ :=
    physical_layers_of_packed_trimming_words U host (fun i : Fin m => T i.val) f words omitted ρ τ
      hHost hPack hParity
  let L (i : ℕ) := if hi : i < m then layer ⟨i,hi⟩ else ⊥
  have hL (i : ℕ) (hi : i < m) : L i = layer ⟨i,hi⟩ := dif_pos hi
  have hInner' (i : ℕ) (x y : V) (h : (L i).Adj x y) : x ∉ U ∧ y ∉ U := by
    by_cases hi : i < m
    · rw [hL i hi] at h
      exact hInner ⟨i,hi⟩ x y h
    · have hBot : L i = ⊥ := dif_neg hi
      simp [hBot] at h
  have hDis' (i j : ℕ) (hi : i < m) (hj : j < m) (hne : i ≠ j) : Disjoint (L i) (L j) := by
    rw [hL i hi,hL j hj]
    exact hDis (fun he => hne (congrArg Fin.val he))
  have hParts (i : ℕ) (hi : i < m) (j : ℕ) : Disjoint (P i) (L j) := by
    rw [disjoint_iff_inf_le]
    intro x y h
    obtain ⟨hx,hy⟩ := hInner' j x y h.2
    exact (hOuter i hi x y h.1).elim hx hy
  have hZero (i : ℕ) (v : V) (hv : v ∈ U) : (L i).degree v = 0 := by
    by_contra! h
    obtain ⟨x,hx⟩ := ((L i).degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero h)
    exact (hInner' i v x hx).1 hv
  have hActual (i : ℕ) (hi : i < m) : P i ⊔ L i ≤ T i ∧ (P i ⊔ L i).EdgeColorable 2 ∧
      (∀ v,(P i ⊔ L i).degree v ≤ 2) ∧ ∀ v,(P i ⊔ L i).degree v+credit i v = 2 := by
    obtain ⟨hLe,hTwo,hDeg,_,_,hEq⟩ := hLayers ⟨i,hi⟩
    rw [hP i hi,hL i hi]
    exact ⟨hLe,hTwo,hDeg,fun v => by rw [hCredit i hi]; exact hEq v⟩
  have hLeG (i : ℕ) (hi : i < m) : L i ≤ G := by
    intro x y h
    obtain ⟨hx,hy⟩ := hInner' i x y h
    exact (hCoreT i hi x y hx hy).mp ((hActual i hi).1 (Or.inr h))
  have hRead (Q : SimpleGraph V) (j : ℕ) (hj : j ≤ m)
      (hCore : ∀ x y,x ∉ U → y ∉ U → (Q.Adj x y ↔ G.Adj x y)) :
      ∀ v,auxiliaryPhysicalDegree Q U P credit j v = (sdiff Q (usedTrimmingPrefix L j)).degree v := by
    apply auxiliary_physical_degree_eq Q U P L credit j
    · intro i hi x y h
      obtain ⟨hx,hy⟩ := hInner' i x y h
      exact (hCore x y hx hy).mpr (hLeG i (hi.trans_le hj) h)
    · exact fun i hi k hk => hDis' i k (hi.trans_le hj) (hk.trans_le hj)
    · exact fun i hi => hParts i (hi.trans_le hj) i
    · exact fun i _ => hZero i
    · intro i hi v _
      have h := (hActual i (hi.trans_le hj)).2.2.2 v
      omega
  have hReadS (j : ℕ) (hj : j ≤ m) := hRead (S j) j hj (hCoreS j hj)
  have hReadT (j : ℕ) (hj : j < m) := hRead (T j) j hj.le (hCoreT j hj)
  let H (i : ℕ) := sdiff (S i) (usedTrimmingPrefix L i)
  let C (i : ℕ) := sdiff (T i) (usedTrimmingPrefix L i)
  let Q (i : ℕ) := P i ⊔ L i
  have hAvailable (i : ℕ) (hi : i < m) : Q i ≤ C i :=
    realized_layer_available_at_prefix (T i) (P i) L i
      (le_sup_left.trans (hActual i hi).1) (le_sup_right.trans (hActual i hi).1)
      (fun j hj => hDis' i j hi (hj.trans hi) (Nat.ne_of_gt hj)) (fun j _ => hParts i hi j)
  have hPhysicalNext (i : ℕ) (hi : i < m) : H (i+1) = sdiff (C i) (Q i) :=
    virtual_and_physical_prefix_step (S (i+1)) (T i) (P i) (Q i) L i (hNext i hi) rfl
  have hStepBalance (i : ℕ) (hi : i < m) (v : V) :
      (auxiliaryPhysicalDegree (T i) U P credit i v+(sdiff (S i) (T i)).degree v =
        auxiliaryPhysicalDegree (S i) U P credit i v) ∧
      auxiliaryPhysicalDegree (S (i+1)) U P credit (i+1) v+(sdiff (S i) (T i)).degree v
        +(2-credit i v) = auxiliaryPhysicalDegree (S i) U P credit i v := by
    let previous := usedTrimmingPrefix L i
    let H := sdiff (S i) previous
    let C := sdiff (T i) previous
    let E := sdiff (S i) (T i)
    let Q := P i ⊔ L i
    have hNoPacked (v : V) (hv : v ∈ U) (u : V) : ¬previous.Adj v u := by
      intro hOld
      obtain ⟨j,hj⟩ := iSup_adj.mp hOld
      exact (hInner' j.val v u hj).1 hv
    obtain ⟨hE,hCleaned⟩ := trimming_cleanup_after_core_removal (hClean i hi) (hW i hi) previous hNoPacked
    change sdiff H E = C at hCleaned
    have hLeQ : Q ≤ C := hAvailable i hi
    have hEq : sdiff (S (i+1)) (usedTrimmingPrefix L (i+1)) = sdiff C Q := hPhysicalNext i hi
    have hCleanup : C.degree v+E.degree v = H.degree v := by
      simpa only [hCleaned,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le H E hE v
    have hLayer : (sdiff C Q).degree v+Q.degree v = C.degree v := by
      simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le C Q hLeQ v
    have hCredit' : Q.degree v = 2-credit i v := by
      have h := (hActual i hi).2.2.2 v
      change Q.degree v+credit i v = 2 at h
      omega
    constructor
    · rw [hReadT i hi v,hReadS i hi.le v]
      exact hCleanup
    · rw [hReadS (i+1) (by omega) v,hReadS i hi.le v,hEq]
      change (sdiff C Q).degree v+E.degree v+(2-credit i v) = H.degree v
      rw [←hCredit',Nat.add_right_comm,hLayer,hCleanup]
  have hProtected (i : ℕ) (hi : i < m) (a b : ↥(Uᶜ : Finset V)) (h : R.Adj a b) :
      ¬(L i).Adj a.val b.val := by
    rw [hL i hi]
    exact hAvoid ⟨i,hi⟩ a b h
  have hRobust (r t : ℕ) (hRes : IsRobustAt R r t) (j : ℕ) (hj : j ≤ m) :
      IsRobustAt (H j) (r-U.card) (t+U.card) :=
    robust_physical_prefix_of_core_reserve G (S j) U L j R (hCoreS j hj) hRLe
      (fun i hi => hProtected i (hi.trans_le hj)) r t hRes
  refine ⟨R,L,hRLe,hRob,hProtected,fun i _ => hInner' i,hRobust,
    fun i hi => ⟨hAvailable i hi,(hActual i hi).2.1,hPhysicalNext i hi,(hActual i hi).2.2.2⟩,hReadS,hReadT,
    fun i hi v => (hStepBalance i hi v).1,fun i hi v => (hStepBalance i hi v).2,?_⟩
  intro hSize hNC hLow hCaps
  have hClass (i : ℕ) (hi : i ≤ m) :
      (H i).maxDegree = G.maxDegree-2*i ∧ ¬(H i).EdgeColorable (H i).maxDegree := by
    have hRun (j : ℕ) (hj : j ≤ m)
        (hComplete : ∀ i < j,∀ v,auxiliaryPhysicalDegree (T i) U P credit i v+credit i v ≤ G.maxDegree-2*i) :
        ∀ i ≤ j,
          let H := sdiff (S i) (usedTrimmingPrefix L i)
          H.maxDegree = G.maxDegree-2*i ∧ ¬H.EdgeColorable H.maxDegree := by
      have inRange (i : ℕ) (hi : i < j) : i < m := hi.trans_le hj
      refine realized_trimming_prefixes_class_two G U S T P L W j hFirst (by omega) hNC
        (fun i hi => hW i (inRange i hi)) (fun i hi => hClean i (inRange i hi))
        (fun i hi => hLow i (inRange i hi))
        (fun i hi => le_sup_left.trans (hActual i (inRange i hi)).1)
        (fun i hi => hOuter i (inRange i hi)) (fun i hi => hLeG i (inRange i hi)) hInner'
        (fun i hi k hk => hDis' i k (inRange i hi) (hk.trans (inRange i hi)) (Nat.ne_of_gt hk))
        (fun i hi => hNext i (inRange i hi))
        (fun i hi => (hActual i (inRange i hi)).2.1)
        (fun i hi => (hActual i (inRange i hi)).2.2.1) ?_
      intro i hi v
      change (sdiff (T i) (usedTrimmingPrefix L i)).degree v+2 ≤ G.maxDegree-2*i+(P i ⊔ L i).degree v
      have hCap := hComplete i hi v
      rw [hReadT i (inRange i hi) v] at hCap
      have hCharge := (hActual i (inRange i hi)).2.2.2 v
      omega
    have hCheck (i : ℕ) (hi : i < m) :
        ∀ v,auxiliaryPhysicalDegree (T i) U P credit i v+credit i v ≤ G.maxDegree-2*i := by
      induction i using Nat.strong_induction_on with
      | h i ih =>
        intro v
        by_cases hc : 0 < credit i v
        · exact hCaps i hi v hc
        have hZero : credit i v = 0 := by omega
        have hMax := (hRun i hi.le (fun k hk => ih k hk (hk.trans hi)) i le_rfl).1
        let H := sdiff (S i) (usedTrimmingPrefix L i)
        let C := sdiff (T i) (usedTrimmingPrefix L i)
        have hC : C ≤ H := by
          intro x y h
          exact ⟨DeletionRun.le_source (hClean i hi) h.1,h.2⟩
        have hD : C.degree v ≤ H.maxDegree :=
          (degree_le_of_le hC (v := v)).trans (H.degree_le_maxDegree v)
        rw [hReadT i hi v,hZero,Nat.add_zero]
        exact hD.trans (le_of_eq hMax)
    exact hRun m le_rfl hCheck i hi
  refine ⟨hClass,?_⟩
  intro r t b a B hRes hNoG hBudget hMass hIndependent hMargins j hj
  change ¬(H j).HasOverfullSubgraph
  cases j with
  | zero =>
    have hStart : H 0 = G := by
      change sdiff (S 0) (usedTrimmingPrefix L 0) = G
      rw [hFirst]
      ext u v
      refine ⟨And.left,fun h => ⟨h,?_⟩⟩
      intro hUsed
      obtain ⟨i,_⟩ := iSup_adj.mp hUsed
      exact Fin.elim0 i
    have transport (J : SimpleGraph V) (h : J = G) : ¬J.HasOverfullSubgraph := by
      subst J
      have hDec : (fun u v => Classical.propDecidable (G.Adj u v)) =
          (inferInstance : DecidableRel G.Adj) := Subsingleton.elim _ _
      rw [hDec]
      exact hNoG
    exact transport _ hStart
  | succ i =>
    have hi : i < m := hj
    let D := auxiliaryPhysicalDegree (S i) U P credit i
    let active := univ.filter (fun v => 0 < D v)
    have hReadDegree (v : V) : D v = (H i).degree v := hReadS i hi.le v
    obtain ⟨hMax,hUncol⟩ := hClass i hi.le
    have hNoOld (v : V) (hv : v ∈ U) (u : V) : ¬(usedTrimmingPrefix L i).Adj v u := by
      intro h
      obtain ⟨k,hk⟩ := iSup_adj.mp h
      exact (hInner' k.val v u hk).1 hv
    have hSmall (v : V) (hv : v ∈ W i) : (H i).degree v < (H i).maxDegree := by
      rw [hMax,←hReadDegree]
      simpa only [D,auxiliaryPhysicalDegree,if_pos (hW i hi hv)] using hLow i hi v hv
    obtain ⟨hReplay,_,hCleanMax,_⟩ := exact_replay_away_from_core_removals (hClean i hi)
      (hW i hi) hNoOld hSmall hUncol
    have hCleanChoice : (H i).IsIndepSet (W i : Set V) ∨ C i = H i := by
      rcases hIndependent i hi with hInd | hSame
      · exact Or.inl (fun x hx y hy hne hEdge => hInd hx hy hne hEdge.1)
      · exact Or.inr (congrArg (fun J => sdiff J (usedTrimmingPrefix L i)) hSame)
    have hCharge : (∑ v ∈ Uᶜ,(2-(Q i).degree v)) ≤ 2 :=
      (words ⟨i,hi⟩).core_missing_degree_le_two_of_credits (omitted ⟨i,hi⟩) (Q i)
        (hMass ⟨i,hi⟩) (fun v => by rw [←hCredit i hi]; exact (hActual i hi).2.2.2 v)
    obtain ⟨hT,hRate,hWeak,hOrd,hM₁,hM₂,hSkip⟩ := hMargins i hi
    have hAfter : (sdiff (C i) (Q i)).maxDegree = (H i).maxDegree-2 := by
      rw [←hPhysicalNext i hi,(hClass (i+1) hj).1,hMax]
      omega
    have hRemaining : IsRobustAt (sdiff (C i) (Q i)) (r-U.card) (t+U.card) := by
      rw [←hPhysicalNext i hi]
      exact hRobust r t hRes (i+1) hj
    have hNoRecord : ¬HasAlmostOverfullRecord active (H i).maxDegree B D := by
      rw [hMax]
      exact hSkip
    have hDiffDec : SimpleGraph.Sdiff.adjDecidable V (C i) (Q i) =
        (fun x y => Classical.propDecidable ((sdiff (C i) (Q i)).Adj x y)) :=
      Subsingleton.elim _ _
    have hWeakPhysical (u v : V) (he : (H i).Adj u v) :
        (H i).maxDegree-b ≤ (H i).degree u+(H i).degree v := by
      rw [hMax,←hReadDegree,←hReadDegree]
      by_cases hPair : u ∈ U ∨ v ∈ U
      · exact hWeak u v he.1 hPair
      · have hu : G.maxDegree-2*i ≤ D u+a := hOrd u (fun h => hPair (Or.inl h))
        have hv : G.maxDegree-2*i ≤ D v+a := hOrd v (fun h => hPair (Or.inr h))
        omega
    have hNo := realized_trimming_step_no_overfull (H i) (C i) (Q i) active U (W i) D
      (r-U.card) (t+U.card) b a B hReplay hCleanChoice (hW i hi) hCleanMax
      (by rw [hMax]; omega) (hAvailable i hi) (by rw [hDiffDec]; exact hAfter)
      (hActual i hi).2.2.1 hCharge (by rw [hDiffDec]; exact hRemaining)
      (by rwa [hMax]) (by rwa [hMax]) hWeakPhysical
      (fun v hv => by rw [hMax,←hReadDegree]; exact hOrd v hv)
      (by rwa [hMax]) (by rwa [hMax])
      hBudget (fun v hv => mem_filter.mpr ⟨mem_univ _,by rwa [hReadDegree]⟩)
      (fun v _ => hReadDegree v) hNoRecord
    rw [hDiffDec] at hNo
    rwa [hPhysicalNext i hi]

end OverfullWork.CMSTrimmingRound
