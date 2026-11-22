module

public import OverfullWork.KuhnOsthusProjectedExceptionalArcs

@[expose] public section


/-! Restore the four exceptional systems in a constructed cycle
absorber. Their incoming and outgoing slots lie in disjoint halves
of the common interval partition, including at shared boundaries. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V Z : Type*} [Fintype V]

/-- Earlier and later exceptional covers own distinct incoming and
outgoing slots, even when their intervals share a boundary. -/
theorem IntervalPathCover.disjoint_cyclic_slots_at_wrap {H H' : Digraph V} {k b c l r : ℕ}
    {X : Fin k → Finset V} (hk : 0 < k)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j)) (hc : c < k) (hr : r ≤ k) (hOrder : c ≤ l)
    (P : IntervalPathCover H (clusterIntervalVertices (cyclicCluster X hk) b c)
      (cyclicCluster X hk b) (cyclicCluster X hk c))
    (Q : IntervalPathCover H' (clusterIntervalVertices (cyclicCluster X hk) l r)
      (cyclicCluster X hk l) (cyclicCluster X hk r)) :
    (∀ {x a y z}, P.digraph.Adj x y → Q.digraph.Adj a z → x ≠ a) ∧
    (∀ {x a y z}, P.digraph.Adj x y → Q.digraph.Adj a z → y ≠ z) := by
  have unique {i j : ℕ} (hi : i < k) (hj : j < k) {v : V}
      (h : v ∈ cyclicCluster X hk i) (h' : v ∈ cyclicCluster X hk j) : i = j := by
    by_contra he
    exact disjoint_left.mp (cyclicCluster_disjoint_before_wrap hk hDis hi hj he) h h'
  constructor
  · intro x a y z hp hq he
    subst a
    obtain ⟨hp₁,hp₂⟩ := mem_sdiff.mp ((P.slots x).1.mp ⟨y,hp⟩)
    have hq₁ := (mem_sdiff.mp ((Q.slots x).1.mp ⟨z,hq⟩)).1
    obtain ⟨i,_,hi,hxi⟩ := (mem_clusterIntervalVertices _ _ _ _).mp hp₁
    obtain ⟨j,hj,hj',hxj⟩ := (mem_clusterIntervalVertices _ _ _ _).mp hq₁
    have hjk : j < k := by
      by_contra! h
      have he : j = r := by omega
      exact (mem_sdiff.mp ((Q.slots x).1.mp ⟨z,hq⟩)).2 (he ▸ hxj)
    have hij := unique (hi.trans_lt hc) hjk hxi hxj
    exact hp₂ ((by omega : i = c) ▸ hxi)
  · intro x a y z hp hq he
    subst z
    have hp₁ := (mem_sdiff.mp ((P.slots y).2.mp ⟨x,hp⟩)).1
    obtain ⟨hq₁,hq₂⟩ := mem_sdiff.mp ((Q.slots y).2.mp ⟨a,hq⟩)
    obtain ⟨i,hib,hi,hyi⟩ := (mem_clusterIntervalVertices _ _ _ _).mp hp₁
    obtain ⟨j,hj,hj',hyj⟩ := (mem_clusterIntervalVertices _ _ _ _).mp hq₁
    by_cases hjk : j < k
    · have hij := unique (hi.trans_lt hc) hjk hyi hyj
      exact hq₂ ((by omega : j = l) ▸ hyj)
    · have hi₀ : 0 < i := by
        by_contra! h
        have he : i = b := by omega
        exact (mem_sdiff.mp ((P.slots y).2.mp ⟨x,hp⟩)).2 (he ▸ hyi)
      have hEnd : j = k := by omega
      have hSep := cyclicCluster_distinct hk hDis (i := i) (j := j)
        (by rw [hEnd,Nat.mod_self,Nat.mod_eq_of_lt (by omega)]; omega)
      exact disjoint_left.mp hSep hyi hyj

/-- Earlier and later exceptional covers own distinct incoming and
outgoing slots, even when their intervals share a boundary. -/
theorem IntervalPathCover.disjoint_cyclic_slots {H H' : Digraph V} {k b c l r : ℕ}
    {X : Fin k → Finset V} (hk : 0 < k)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j)) (hc : c < k) (hr : r < k) (hOrder : c ≤ l)
    (P : IntervalPathCover H (clusterIntervalVertices (cyclicCluster X hk) b c)
      (cyclicCluster X hk b) (cyclicCluster X hk c))
    (Q : IntervalPathCover H' (clusterIntervalVertices (cyclicCluster X hk) l r)
      (cyclicCluster X hk l) (cyclicCluster X hk r)) :
    (∀ {x a y z}, P.digraph.Adj x y → Q.digraph.Adj a z → x ≠ a) ∧
    (∀ {x a y z}, P.digraph.Adj x y → Q.digraph.Adj a z → y ≠ z) :=
  P.disjoint_cyclic_slots_at_wrap hk hDis hc hr.le hOrder Q

/-- The ordinary routes of the main factor, before reinserting the
third and fifth exceptional systems. -/
noncomputable def NormalizedCycleAbsorber.mainOrdinary
    {G H : Digraph V} {A B : ℕ → Finset V} {m q : ℕ}
    {E : CycleAbsorberExceptionalCovers H A q}
    {eTop : Fin (2*m) ≃ A 0} {eLow : Fin (2*m) ≃ B 0}
    (N : NormalizedCycleAbsorber (G := G) E eTop eLow) : Digraph V :=
  (N.top.paths.unionPaths ⊔ N.topTail.unionPaths) ⊔ (N.low.paths.unionPaths ⊔ N.lowTail.unionPaths)

omit [Fintype V] in
/-- All ordinary arcs of the three factors follow consecutive pairs
of the same cyclic cluster order, including across the rotated origin. -/
theorem NormalizedCycleAbsorber.ordinary_arcs_wind
    {G H : Digraph V} {m q : ℕ} (X : Fin (14*q) → Finset V) (hk : 0 < 14*q) :
    let A := cyclicCluster X hk
    let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
    ∀ {E : CycleAbsorberExceptionalCovers H A q}
      {eTop : Fin (2*m) ≃ A 0} {eLow : Fin (2*m) ≃ B 0}
      (N : NormalizedCycleAbsorber (G := G) E eTop eLow) {x y : V},
      ((N.mainOrdinary ⊔ N.upper.ordinary) ⊔ N.lower.ordinary).Adj x y →
      ∃ i, x ∈ A i ∧ y ∈ A (i+1) := by
  intro A B E eTop eLow N x y h
  have hOrigin (i : ℕ) : B i = A (7*q+i) := cyclicCluster_rotateClusterArray X hk _ _
  have hLift {i : ℕ} (hx : x ∈ B i) (hy : y ∈ B (i+1)) :
      ∃ j, x ∈ A j ∧ y ∈ A (j+1) :=
    ⟨7*q+i,hOrigin i ▸ hx,by simpa only [hOrigin,Nat.add_assoc] using hy⟩
  have hPath {J : Type} {T : ℕ → Finset V} {l r : ℕ}
      (P : OrderedClusterPaths G T J l r) (hp : P.unionPaths.Adj x y) :
      ∃ i, x ∈ T i ∧ y ∈ T (i+1) := by
    obtain ⟨j,i,hi,hir,rfl,rfl⟩ := Digraph.iSup_adj.mp hp
    exact ⟨i,P.part _ hi hir.le j,P.part _ (by omega) (by omega) j⟩
  rcases h with (((ht | hp) | (hb | hq)) | hu) | hw
  · exact hPath N.top.paths ht
  · exact hPath N.topTail hp
  · obtain ⟨_,hx,hy⟩ := hPath N.low.paths hb
    exact hLift hx hy
  · obtain ⟨_,hx,hy⟩ := hPath N.lowTail hq
    exact hLift hx hy
  · rcases N.upper.ordinary_slots x y hu with ⟨i,_,_,hx,hy⟩ | ⟨i,_,hx,hy⟩
    · exact ⟨i,hx,hy⟩
    · exact ⟨8*q+i,hx,by simpa only [Nat.add_assoc] using hy⟩
  · rcases N.lower.ordinary_slots x y hw with ⟨i,_,_,hx,hy⟩ | ⟨i,_,hx,hy⟩
    · exact hLift hx hy
    · exact hLift hx (by simpa only [Nat.add_assoc] using hy)

/-- The original arc sets preserve each prescribed exceptional
interval, remain disjoint and leave the two crossed repair pairs free. -/
noncomputable def CycleAbsorberOriginalConclusion
    {G H : Digraph V} {A B : ℕ → Finset V} {m q : ℕ}
    {E : CycleAbsorberExceptionalCovers H A q}
    {eTop : Fin (2*m) ≃ A 0} {eLow : Fin (2*m) ≃ B 0}
    (N : NormalizedCycleAbsorber (G := G \ E.arcs) E eTop eLow)
    (D : Digraph (V ⊕ Z))
    (P₂ : ProjectedExceptionalArcs D E.second.digraph (id : Z → Z))
    (P₃ : ProjectedExceptionalArcs D E.third.digraph (id : Z → Z))
    (P₄ : ProjectedExceptionalArcs D E.fourth.digraph (id : Z → Z))
    (P₅ : ProjectedExceptionalArcs D E.fifth.digraph (id : Z → Z)) : Prop :=
    let F := liftOrdinaryCycleArcs Z N.mainOrdinary ⊔ (P₃.original ⊔ P₅.original)
    let U := liftOrdinaryCycleArcs Z N.upper.ordinary ⊔ P₄.original
    let W := liftOrdinaryCycleArcs Z N.lower.ordinary ⊔ P₂.original
    F ≤ D ∧ U ≤ D ∧ W ≤ D ∧
    Disjoint F U ∧ Disjoint F W ∧ Disjoint U W ∧
    (∀ x y, (F ⊔ U ⊔ W).Adj (.inl x) (.inl y) →
      (N.main ⊔ (N.upper.ordinary ⊔ E.fourth.digraph) ⊔
        (N.lower.ordinary ⊔ E.second.digraph)).Adj x y) ∧
    (∀ l, (D \ (F ⊔ U ⊔ W)).Adj (.inl (N.upper.rows.mark (l,Fin.last (2*m))))
      (.inl (N.upper.permutation (N.upper.rows.mark (!l,Fin.last (2*m)))))) ∧
    (∀ l, (D \ (F ⊔ U ⊔ W)).Adj (.inl (N.lower.rows.mark (l,Fin.last (2*m))))
      (.inl (N.lower.permutation (N.lower.rows.mark (!l,Fin.last (2*m))))))

/-- The projected factors expand in the original host. All four
original exceptional systems occur unchanged, the three expanded
factors are pairwise arc-disjoint, and both repair pairs stay free. -/
theorem NormalizedCycleAbsorber.restore_original_factors
    {G H : Digraph V} {m q : ℕ} (X : Fin (14*q) → Finset V) (hk : 0 < 14*q)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    {E : CycleAbsorberExceptionalCovers H (cyclicCluster X hk) q}
    {eTop : Fin (2*m) ≃ cyclicCluster X hk 0}
    {eLow : Fin (2*m) ≃ cyclicCluster (rotateClusterArray X hk (7*q)) hk 0}
    (N : NormalizedCycleAbsorber (G := G \ E.arcs) E eTop eLow)
    (D : Digraph (V ⊕ Z)) (hHost : ∀ {x y}, G.Adj x y → D.Adj (.inl x) (.inl y))
    (P₂ : ProjectedExceptionalArcs D E.second.digraph (id : Z → Z))
    (P₃ : ProjectedExceptionalArcs D E.third.digraph (id : Z → Z))
    (P₄ : ProjectedExceptionalArcs D E.fourth.digraph (id : Z → Z))
    (P₅ : ProjectedExceptionalArcs D E.fifth.digraph (id : Z → Z)) :
    CycleAbsorberOriginalConclusion N D P₂ P₃ P₄ P₅ := by
  unfold CycleAbsorberOriginalConclusion
  intro F U W
  have slots {b c l r : ℕ} (hc : c < 14*q) (hr : r < 14*q) (h : c ≤ l)
      (P : IntervalPathCover H (clusterIntervalVertices (cyclicCluster X hk) b c)
        (cyclicCluster X hk b) (cyclicCluster X hk c))
      (Q : IntervalPathCover H (clusterIntervalVertices (cyclicCluster X hk) l r)
        (cyclicCluster X hk l) (cyclicCluster X hk r)) := IntervalPathCover.disjoint_cyclic_slots hk hDis hc hr h P Q
  have h₂₃ := slots (by omega) (by omega) le_rfl E.second E.third
  have h₂₄ := slots (by omega) (by omega) (by omega) E.second E.fourth
  have h₂₅ := slots (by omega) (by omega) (by omega) E.second E.fifth
  have h₃₄ := slots (by omega) (by omega) le_rfl E.third E.fourth
  have h₃₅ := slots (by omega) (by omega) (by omega) E.third E.fifth
  have h₄₅ := slots (by omega) (by omega) le_rfl E.fourth E.fifth
  have hJoin (x : V) (h : ∃ y, E.third.digraph.Adj x y)
      (h' : ∃ y, E.fifth.digraph.Adj x y) : False := by
    obtain ⟨_,hy⟩ := h
    obtain ⟨_,hy'⟩ := h'
    exact h₃₅.1 hy hy' rfl
  let J := P₃.join P₅ hJoin
  have hO : N.mainOrdinary ≤ G \ E.arcs :=
    sup_le (sup_le N.top.paths.unionPaths_le N.topTail.unionPaths_le)
      (sup_le N.low.paths.unionPaths_le N.lowTail.unionPaths_le)
  have hU : N.upper.ordinary ≤ G \ E.arcs := N.upper.ordinary_le.trans (fun _ _ h => h.1)
  have hMain : ∀ x y, (N.mainOrdinary ⊔ (E.third.digraph ⊔ E.fifth.digraph)).Adj x y ↔ N.mainPermutation x = y := by
    intro x y
    rw [← N.exact_main x y,N.main_arcs]
    simp only [NormalizedCycleAbsorber.mainOrdinary,Digraph.sup_adj]
    tauto
  have hLower : ∀ x y, (N.lower.ordinary ⊔ E.second.digraph).Adj x y ↔ N.lower.permutation x = y := by
    intro x y
    rw [← N.second_arcs]
    exact N.lower.exact_factor x y
  have hFExact : restoreExceptionalFactor N.mainPermutation J.source (Sum.elim id id) = F :=
    (J.restore_exact N.mainPermutation hMain (fun ho he => (hO ho).2 (.inl (.inl he)))).trans
      (congrArg (liftOrdinaryCycleArcs Z N.mainOrdinary ⊔ ·) (P₃.join_original P₅ hJoin))
  have hUExact : restoreExceptionalFactor N.upper.permutation P₄.source id = U :=
    P₄.restore_exact N.upper.permutation N.upper.exact_factor
      (fun ho he => (hU ho).2 (.inl (.inr he)))
  have hWExact : restoreExceptionalFactor N.lower.permutation P₂.source id = W :=
    P₂.restore_exact N.lower.permutation hLower (fun ho he => (N.lower_le ho).2 (.inr he))
  have hLift {R : Digraph V} (hR : R ≤ G \ E.arcs) : liftOrdinaryCycleArcs Z R ≤ D := by
    rintro (x | z) (y | w) h
    · exact hHost (hR h).1
    · exact h.elim
    · exact h.elim
    · exact h.elim
  have hF₃ (z : Z) : N.mainPermutation (P₃.source z) = P₃.target z :=
    (hMain _ _).mp (.inr (.inl (P₃.shortcut z)))
  have hF₅ (z : Z) : N.mainPermutation (P₅.source z) = P₅.target z :=
    (hMain _ _).mp (.inr (.inr (P₅.shortcut z)))
  have hU₄ (z : Z) : N.upper.permutation (P₄.source z) = P₄.target z :=
    (N.upper.exact_factor _ _).mp (.inr (P₄.shortcut z))
  have hW₂ (z : Z) : N.lower.permutation (P₂.source z) = P₂.target z :=
    (hLower _ _).mp (.inr (P₂.shortcut z))
  have hProject (x y : V) (h : (F ⊔ U ⊔ W).Adj (.inl x) (.inl y)) :
      (N.main ⊔ (N.upper.ordinary ⊔ E.fourth.digraph) ⊔
        (N.lower.ordinary ⊔ E.second.digraph)).Adj x y := by
    rw [←hFExact,←hUExact,←hWExact] at h
    rcases h with (hf | hu) | hw
    · exact .inl (.inl ((N.exact_main _ _).mpr hf.1))
    · exact .inl (.inr ((N.upper.exact_factor _ _).mpr hu.1))
    · exact .inr ((hLower _ _).mpr hw.1)
  have transfer {x y : V}
      (h : ((G \ E.arcs) \ (N.main ⊔ (N.upper.ordinary ⊔ E.fourth.digraph) ⊔
        (N.lower.ordinary ⊔ E.second.digraph))).Adj x y) :
      (D \ (F ⊔ U ⊔ W)).Adj (.inl x) (.inl y) := by
    exact ⟨hHost h.1.1,fun he => h.2 (hProject x y he)⟩
  refine ⟨sup_le (hLift hO) (sup_le P₃.original_le P₅.original_le),
    sup_le (hLift hU) P₄.original_le,sup_le (hLift N.lower_le) P₂.original_le,?_,?_,?_,hProject,?_,?_⟩
  · rw [←hFExact,←hUExact]
    apply restoreExceptionalFactor_disjoint
    · intro x h
      exact (N.main_disjoint x _ ((N.exact_main _ _).mpr h)).1
        ((N.upper.exact_factor _ _).mpr rfl)
    · rintro (z | z) w _
      · exact h₃₄.1 (P₃.shortcut z) (P₄.shortcut w)
      · exact (h₄₅.1 (P₄.shortcut w) (P₅.shortcut z)).symm
    · rintro (z | z) w _
      · change N.mainPermutation (P₃.source z) ≠ N.upper.permutation (P₄.source w)
        rw [hF₃,hU₄]
        exact h₃₄.2 (P₃.shortcut z) (P₄.shortcut w)
      · change N.mainPermutation (P₅.source z) ≠ N.upper.permutation (P₄.source w)
        rw [hF₅,hU₄]
        exact (h₄₅.2 (P₄.shortcut w) (P₅.shortcut z)).symm
  · rw [←hFExact,←hWExact]
    apply restoreExceptionalFactor_disjoint
    · intro x h
      exact (N.main_disjoint x _ ((N.exact_main _ _).mpr h)).2 ((hLower _ _).mpr rfl)
    · rintro (z | z) w _
      · exact (h₂₃.1 (P₂.shortcut w) (P₃.shortcut z)).symm
      · exact (h₂₅.1 (P₂.shortcut w) (P₅.shortcut z)).symm
    · rintro (z | z) w _
      · change N.mainPermutation (P₃.source z) ≠ N.lower.permutation (P₂.source w)
        rw [hF₃,hW₂]
        exact (h₂₃.2 (P₂.shortcut w) (P₃.shortcut z)).symm
      · change N.mainPermutation (P₅.source z) ≠ N.lower.permutation (P₂.source w)
        rw [hF₅,hW₂]
        exact (h₂₅.2 (P₂.shortcut w) (P₅.shortcut z)).symm
  · rw [←hUExact,←hWExact]
    apply restoreExceptionalFactor_disjoint
    · intro x h
      exact N.upper_disjoint x _ ((N.upper.exact_factor _ _).mpr h) ((hLower _ _).mpr rfl)
    · intro z w _
      exact (h₂₄.1 (P₂.shortcut w) (P₄.shortcut z)).symm
    · intro z w _
      rw [hU₄,hW₂]
      exact (h₂₄.2 (P₂.shortcut w) (P₄.shortcut z)).symm
  · exact fun l => transfer (N.upper_repair l)
  · exact fun l => transfer (N.lower_repair l)

end OverfullWork.DirectedRobustExpansion
