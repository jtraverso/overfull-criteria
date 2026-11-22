module

public import OverfullWork.KuhnOsthusPrimaryCycleFactor
public import OverfullWork.KuhnOsthusResidualCycleFactor
public import OverfullWork.MergeReservePacking

@[expose] public section


/-! Assemble the three factors on ordinary vertices with the four
complete exceptional path covers held out of the routing host. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Whole successor pairs retain lower superregularity after deleting
arcs covered by a bounded number of matchings. -/
theorem residual_pairs_after_matchings {G L : Digraph V} {t m : ℕ}
    (M : Fin t → Equiv.Perm V) (hL : L ≤ matchingUnion M)
    (U W : Finset V) (hm : 0 < m) (hU : U.card = 2*m) (hW : W.card = 2*m)
    (ε η d a : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hBudget : (t:ℝ) ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPair : IsLowerSuperregularPair G ε d U W) :
    IsLowerSuperregularPair (G \ L) η d U W := by
  have hSub : G ⊓ L ≤ matchingUnion M := inf_le_right.trans hL
  have hMono {J K : Digraph V} (h : J ≤ K) (v : V) :
      inDegree J v ≤ inDegree K v ∧ outDegree J v ≤ outDegree K v := by
    constructor
    · apply card_le_card
      intro x hx
      exact mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp hx).2⟩
    · apply card_le_card
      intro x hx
      exact mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp hx).2⟩
  have hLoss (v : V) : inDegree (G ⊓ L) v ≤ t ∧ outDegree (G ⊓ L) v ≤ t :=
    ⟨(hMono hSub v).1.trans (matchingUnion_semidegrees M v).1,
     (hMono hSub v).2.trans (matchingUnion_semidegrees M v).2⟩
  have he : G \ (G ⊓ L) = G \ L := by
    ext x y
    simp only [Digraph.sdiff_adj,Digraph.inf_adj]
    tauto
  rw [←he]
  exact IsLowerSuperregularPair.after_bounded_arc_deletion inf_le_left t hLoss U W
    (card_pos.mp (by rw [hU]; omega)) (card_pos.mp (by rw [hW]; omega)) _ hU hW
    ε η d a hη hη₁ ha hd hTol hBudget hPair

omit [Fintype V] in
private theorem factor_le_single_matching {F : Digraph V} (σ : Equiv.Perm V)
    (h : ∀ x y, F.Adj x y ↔ σ x = y) :
    F ≤ matchingUnion (fun _ : Fin 1 => σ) :=
  fun x y he => ⟨0,(h x y).mp he⟩

private theorem interval_arc_source {H : Digraph V} {A : ℕ → Finset V} {b c : ℕ}
    (E : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c)) {x y : V}
    (h : E.digraph.Adj x y) : ∃ i, b ≤ i ∧ i < c ∧ x ∈ A i := by
  obtain ⟨hx,hEnd⟩ := mem_sdiff.mp ((E.slots x).1.mp ⟨y,h⟩)
  obtain ⟨i,hi,hic,hm⟩ := (mem_clusterIntervalVertices A b c x).mp hx
  exact ⟨i,hi,lt_of_le_of_ne hic (fun h => hEnd (h ▸ hm)),hm⟩

/-- In the normalized cluster cycle, first construct (F), then the
upper reserve, then the lower reserve. The third operation removes
the two unused upper repair arcs along with the factors already
constructed. All three factors are disjoint, and both repairs stay free.
The exceptional interval covers are supplied in the same physical coordinates. -/
theorem kuhn_osthus_lemma_10_3_cluster_assembly {G H : Digraph V} {m q : ℕ}
    (X : Fin (14*q) → Finset V) (hq : 15 ≤ q) (hm : 0 < m)
    (hCover : ∀ v, ∃ i, v ∈ X i)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (ε η d a : ℝ) (hε : 0 ≤ ε) (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a)
    (hGapε : 2*ε < d) (hGapη : 2*η < d) (hd : d ≤ 1)
    (hTol : 2*(ε+a) ≤ η) (hBudget : 3 ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPairs : ∀ i, IsLowerSuperregularPair G ε d (X i) (X (finRotate (14*q) i)))
    (r : ℕ) (hr : 0 < r) (hCutε : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hCutη : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRouteε : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ)))
    (hRouteη : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    let hk : 0 < 14*q := by omega
    let X' := rotateClusterArray X hk (7*q)
    let A := cyclicCluster X hk
    let B := cyclicCluster X' hk
    ∀ (C : CycleAbsorberClaimOne G A m (4*q)) (C' : CycleAbsorberClaimOne G B m q)
      (E₂ : IntervalPathCover H (clusterIntervalVertices B (9*q) (11*q)) (B (9*q)) (B (11*q)))
      (E₃ : IntervalPathCover H (clusterIntervalVertices A (4*q) (6*q)) (A (4*q)) (A (6*q)))
      (E₄ : IntervalPathCover H (clusterIntervalVertices A (6*q) (8*q)) (A (6*q)) (A (8*q)))
      (E₅ : IntervalPathCover H (clusterIntervalVertices B q (3*q)) (B q) (B (3*q))),
      (∀ x y, G.Adj x y → ¬ (((E₃.digraph ⊔ E₅.digraph) ⊔ E₄.digraph) ⊔ E₂.digraph).Adj x y) →
    ∃ (P : OrderedClusterPaths G A (Fin (2*m)) (6*q) (7*q))
      (Q : OrderedClusterPaths G B (Fin (2*m)) (3*q) (7*q))
      (φ : Equiv.Perm V),
      let F := ((C.paths.unionPaths ⊔ E₃.digraph) ⊔ P.unionPaths) ⊔
        ((C'.paths.unionPaths ⊔ E₅.digraph) ⊔ Q.unionPaths)
      ∃ (S : CycleAbsorberResidualFactor C (fun i => A (8*q+i)) E₄ (G \ F) (14*q+3-8*q))
        (D' : Digraph V)
        (S' : CycleAbsorberResidualFactor C' (fun i => B (11*q+i)) E₂ D' (14*q+3-11*q)),
        let U := S.ordinary ⊔ E₄.digraph
        let W := S'.ordinary ⊔ E₂.digraph
        D' ≤ G ∧
        (∀ x y, F.Adj x y ↔ φ x = y) ∧
        (∀ x y, F.Adj x y → ¬ U.Adj x y ∧ ¬ W.Adj x y) ∧
        (∀ x y, U.Adj x y → ¬ W.Adj x y) ∧
        (∀ l, (G \ (F ⊔ U ⊔ W)).Adj (S.rows.mark (l,Fin.last (2*m)))
          (S.permutation (S.rows.mark (!l,Fin.last (2*m))))) ∧
        (∀ l, (G \ (F ⊔ U ⊔ W)).Adj (S'.rows.mark (l,Fin.last (2*m)))
          (S'.permutation (S'.rows.mark (!l,Fin.last (2*m))))) := by
  intro hk X' A B C C' E₂ E₃ E₄ E₅ hClean
  obtain ⟨P,Q,φ,hF⟩ := kuhn_osthus_lemma_10_3_primary_factor hq X hCover hDis hSize
    ε d hε hGapε hd hPairs r hr hCutε hRouteε C C' E₃ E₅
  let F := ((C.paths.unionPaths ⊔ E₃.digraph) ⊔ P.unionPaths) ⊔
    ((C'.paths.unionPaths ⊔ E₅.digraph) ⊔ Q.unionPaths)
  have hPaths : C.paths.unionPaths ≤ F := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hPaths' : C'.paths.unionPaths ≤ F := le_sup_left.trans (le_sup_left.trans le_sup_right)
  have hUnique : ∀ {x y z}, F.Adj x y → F.Adj x z → y = z :=
    fun {x y z} hy hz => ((hF x y).mp hy).symm.trans ((hF x z).mp hz)
  have hOrigin (i : ℕ) : B i = A (7*q+i) := cyclicCluster_rotateClusterArray X _ _ _
  have hSame {i j : ℕ} (hi : i < 14*q) (hj : j < 14*q) {x : V}
      (hxi : x ∈ A i) (hxj : x ∈ A j) : i = j := by
    by_contra hne
    have h := cyclicCluster_distinct hk hDis (i := i) (j := j)
      (by rwa [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj])
    exact disjoint_left.mp h hxi hxj
  have hSource₂ {x y : V} (h : E₂.digraph.Adj x y) :
      ∃ i, 2*q ≤ i ∧ i < 4*q ∧ x ∈ A i := by
    obtain ⟨j,hj,hjc,hjx⟩ := interval_arc_source E₂ h
    let i := 7*q+j-14*q
    have hi : i+14*q = 7*q+j := by dsimp [i]; omega
    have he : A (7*q+j) = A i := by
      apply congrArg X
      apply Fin.ext
      change (7*q+j)%(14*q) = i%(14*q)
      rw [← hi,Nat.add_mod_right]
    exact ⟨i,by dsimp [i]; omega,by dsimp [i]; omega,he ▸ (hOrigin j ▸ hjx)⟩
  have hSource₅ {x y : V} (h : E₅.digraph.Adj x y) :
      ∃ i, 8*q ≤ i ∧ i < 10*q ∧ x ∈ A i := by
    obtain ⟨j,hj,hjc,hjx⟩ := interval_arc_source E₅ h
    exact ⟨7*q+j,by omega,by omega,hOrigin j ▸ hjx⟩
  have hExc₄ (x y : V) (h : (E₃.digraph ⊔ E₅.digraph).Adj x y) :
      ¬ E₄.digraph.Adj x y := by
    intro he
    obtain ⟨i,hi,hic,hix⟩ := interval_arc_source E₄ he
    rcases h with h | h
    · obtain ⟨j,hj,hjc,hjx⟩ := interval_arc_source E₃ h
      have := hSame (by omega) (by omega) hix hjx
      omega
    · obtain ⟨j,hj,hjc,hjx⟩ := hSource₅ h
      have := hSame (by omega) (by omega) hix hjx
      omega
  have hExc₂ (x y : V) (h : ((E₃.digraph ⊔ E₅.digraph) ⊔ E₄.digraph).Adj x y) :
      ¬ E₂.digraph.Adj x y := by
    intro he
    obtain ⟨i,hi,hic,hix⟩ := hSource₂ he
    rcases h with (h | h) | h
    · obtain ⟨j,hj,hjc,hjx⟩ := interval_arc_source E₃ h
      have := hSame (by omega) (by omega) hix hjx
      omega
    · obtain ⟨j,hj,hjc,hjx⟩ := hSource₅ h
      have := hSame (by omega) (by omega) hix hjx
      omega
    · obtain ⟨j,hj,hjc,hjx⟩ := interval_arc_source E₄ h
      have := hSame (by omega) (by omega) hix hjx
      omega
  have hCard (i : ℕ) : (A i).card = 2*m := hSize _
  have hPair (i : ℕ) : IsLowerSuperregularPair G ε d (A i) (A (i+1)) := by
    change IsLowerSuperregularPair G ε d (A i) (cyclicCluster X hk (i+1))
    rw [cyclicCluster_successor]
    exact hPairs _
  obtain ⟨hFirst,hSecond⟩ := C.crossed_arcs_after_factor (by omega) hPaths hUnique
  have hPair₁ (i : ℕ) : IsLowerSuperregularPair (G \ F) η d (A i) (A (i+1)) :=
    residual_pairs_after_matchings _ (factor_le_single_matching φ hF) _ _ hm (hCard i) (hCard (i+1))
      ε η d a hη hη₁ ha (by linarith) hTol
      (by simpa only [Nat.cast_one] using (show (1:ℝ) ≤ 3 by norm_num).trans hBudget) (hPair i)
  obtain ⟨S⟩ := C.exists_cyclic_residual_factor X hk (by omega) (by omega) (by omega) hm E₄
    hCover hDis hSize hFirst hSecond η d hη.le hGapη hd hPair₁ r hr hCutη hRouteη
  let U := S.ordinary ⊔ E₄.digraph
  let endpoint (l : Bool) := S.rows.mark (l,Fin.last (2*m))
  let R : Digraph V := ⟨fun x y => ∃ l, endpoint l = x ∧ S.permutation (endpoint (!l)) = y⟩
  let L := F ⊔ U ⊔ R
  let D' := G \ L
  let M : Fin 3 → Equiv.Perm V := ![φ,S.permutation,
    switchSuccessors S.permutation (endpoint false) (endpoint true)]
  have hL : L ≤ matchingUnion M := by
    intro x y h
    rcases h with (hf | hs) | ⟨l,rfl,rfl⟩
    · exact ⟨0,(hF x y).mp hf⟩
    · exact ⟨1,(S.exact_factor x y).mp hs⟩
    · refine ⟨2,?_⟩
      change switchSuccessors S.permutation (endpoint false) (endpoint true) (endpoint l) = _
      cases l
      · exact switchSuccessors_left _ _ _
      · exact switchSuccessors_right _ _ _
  have hPair₂ (i : ℕ) : IsLowerSuperregularPair D' η d (B i) (B (i+1)) := by
    rw [hOrigin,hOrigin]
    simpa only [Nat.add_assoc] using residual_pairs_after_matchings M hL _ _ hm
      (hCard (7*q+i)) (hCard (7*q+i+1)) ε η d a hη hη₁ ha (by linarith)
      hTol (by simpa only [Nat.cast_ofNat] using hBudget) (hPair (7*q+i))
  have hKeep {i : ℕ} (hi : 6*q ≤ i) (hi' : i < 8*q) {x y : V}
      (hx : x ∈ A i) (h : (G \ F).Adj x y) : D'.Adj x y := by
    refine ⟨h.1,?_⟩
    rintro ((hf | hs) | ⟨l,he,_⟩)
    · exact h.2 hf
    · rcases hs with hs | hs
      · exact S.ordinary_avoids_exceptional_slots hk (by omega) (by omega) hDis hi hi' hx hs
      · exact hClean x y h.1 (.inl (.inr hs))
    · have hDis' := cyclicCluster_distinct hk hDis (i := i) (j := 11)
        (by rw [Nat.mod_eq_of_lt (by omega : i < 14*q),Nat.mod_eq_of_lt (by omega : 11 < 14*q)]; omega)
      exact disjoint_left.mp hDis' hx (he ▸ S.repair_start l)
  obtain ⟨hFirst',hSecond'⟩ := C'.crossed_arcs_after_factor (by omega) hPaths' hUnique
  have hCross₀ (i : Fin m) (l : Fin 2) : D'.Adj (C'.first.source (cycleAbsorberSwitchSlot m (i,l)))
      (C'.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 l))) :=
    hKeep (i := 7*q+3) (by omega) (by omega) (hOrigin 3 ▸ (C'.first.source _).prop) (hFirst' i l)
  have hCross₁ (i : Fin m) (l : Fin 2) : D'.Adj (C'.second.source (alternateCycleAbsorberSwitchSlot m (i,l)))
      (C'.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 l))) :=
    hKeep (i := 7*q+7) (by omega) (by omega) (hOrigin 7 ▸ (C'.second.source _).prop) (hSecond' i l)
  have hCover' (v : V) : ∃ i, v ∈ X' i := by
    obtain ⟨i,hi⟩ := hCover v
    let j : Fin (14*q) := ⟨(i.val+7*q) % (14*q),Nat.mod_lt _ hk⟩
    refine ⟨j,?_⟩
    change v ∈ X ⟨(7*q+j.val) % (14*q),Nat.mod_lt _ hk⟩
    have he : (7*q+j.val) % (14*q) = i.val := by
      change (7*q+(i.val+7*q)%(14*q))%(14*q) = i.val
      rw [Nat.add_mod_mod,show 7*q+(i.val+7*q) = 14*q+i.val by omega,
        Nat.add_mod_left,Nat.mod_eq_of_lt i.isLt]
    rw [show (⟨(7*q+j.val) % (14*q),Nat.mod_lt _ hk⟩ : Fin (14*q)) = i from Fin.ext he]
    exact hi
  have hDis' (i j : Fin (14*q)) (he : i ≠ j) : Disjoint (X' i) (X' j) := by
    apply cyclicCluster_distinct hk hDis
    intro h
    have hh := congrArg (fun z : ℕ => (7*q+z)%(14*q)) h
    rw [Nat.add_mod_mod,Nat.add_mod_mod,show 7*q+(7*q+i.val) = 14*q+i.val by omega,
      show 7*q+(7*q+j.val) = 14*q+j.val by omega,Nat.add_mod_left,Nat.add_mod_left,
      Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at hh
    exact he (Fin.ext hh)
  obtain ⟨S'⟩ := C'.exists_cyclic_residual_factor X' hk (by omega) (by omega) (by omega) hm E₂
    hCover' hDis' (fun i => hCard (7*q+i.val)) hCross₀ hCross₁ η d hη.le hGapη hd hPair₂ r hr hCutη hRouteη
  have hSplitF {x y : V} (hf : F.Adj x y) : G.Adj x y ∨ (E₃.digraph ⊔ E₅.digraph).Adj x y := by
    rcases hf with ((hf | hf) | hf) | ((hf | hf) | hf)
    · exact .inl (C.paths.unionPaths_le hf)
    · exact .inr (.inl hf)
    · exact .inl (P.unionPaths_le hf)
    · exact .inl (C'.paths.unionPaths_le hf)
    · exact .inr (.inr hf)
    · exact .inl (Q.unionPaths_le hf)
  refine ⟨P,Q,φ,S,D',S',fun _ _ h => h.1,hF,?_,?_,?_,?_⟩
  · intro x y hf
    constructor
    · rintro (hs | he)
      · exact (S.ordinary_le hs).2 hf
      · exact (hSplitF hf).elim (fun hg => hClean x y hg (.inl (.inr he))) (fun he' => hExc₄ x y he' he)
    · rintro (hs | he)
      · exact (S'.ordinary_le hs).2 (.inl (.inl hf))
      · exact (hSplitF hf).elim (fun hg => hClean x y hg (.inr he)) (fun he' => hExc₂ x y (.inl he') he)
  · intro x y hu
    rintro (hs | he)
    · exact (S'.ordinary_le hs).2 (.inl (.inr hu))
    · exact hu.elim (fun hs => hClean x y (S.ordinary_le hs).1 (.inr he)) (fun he' => hExc₂ x y (.inr he') he)
  · intro l
    have hs := S.repair l
    refine ⟨hs.1.1,?_⟩
    rintro ((hf | hu) | (hw | he))
    · exact hs.1.2 hf
    · exact hs.2 hu
    · exact (S'.ordinary_le hw).2 (.inr ⟨l,rfl,rfl⟩)
    · exact hClean _ _ hs.1.1 (.inr he)
  · intro l
    have hs := S'.repair l
    refine ⟨hs.1.1,?_⟩
    rintro (h | hw)
    · exact hs.1.2 (.inl h)
    · exact hs.2 hw

end OverfullWork.DirectedRobustExpansion
