module

public import OverfullWork.KuhnOsthusCycleAbsorberAssembly

@[expose] public section


/-! The four canonical exceptional covers of the cycle absorber use
the original cluster order. Move the two lower covers to their rotated
coordinates without changing any arcs, and reserve their union. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

structure CycleAbsorberExceptionalCovers (H : Digraph V) (A : ℕ → Finset V) (q : ℕ) where
  second : IntervalPathCover H (clusterIntervalVertices A (2*q) (4*q)) (A (2*q)) (A (4*q))
  third : IntervalPathCover H (clusterIntervalVertices A (4*q) (6*q)) (A (4*q)) (A (6*q))
  fourth : IntervalPathCover H (clusterIntervalVertices A (6*q) (8*q)) (A (6*q)) (A (8*q))
  fifth : IntervalPathCover H (clusterIntervalVertices A (8*q) (10*q)) (A (8*q)) (A (10*q))

noncomputable def CycleAbsorberExceptionalCovers.arcs {H : Digraph V} {A : ℕ → Finset V} {q : ℕ}
    (E : CycleAbsorberExceptionalCovers H A q) : Digraph V :=
  ((E.third.digraph ⊔ E.fifth.digraph) ⊔ E.fourth.digraph) ⊔ E.second.digraph

omit [Fintype V] in
theorem cyclicCluster_disjoint_before_wrap {k : ℕ} {X : Fin k → Finset V} (hk : 0 < k)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j)) {i j : ℕ}
    (hi : i < k) (hj : j < k) (hne : i ≠ j) :
    Disjoint (cyclicCluster X hk i) (cyclicCluster X hk j) :=
  cyclicCluster_distinct hk hDis (by rwa [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj])

omit [Fintype V] in
/-- Joining the exceptional covers in their physical order gives one
path system. Its intersection with the routing host therefore costs
at most one arc in each semidegree. -/
theorem CycleAbsorberExceptionalCovers.exists_interval_cover {H : Digraph V}
    {A : ℕ → Finset V} {q : ℕ} (E : CycleAbsorberExceptionalCovers H A q)
    (hDis : ∀ i j, i ≤ 10*q → j ≤ 10*q → i ≠ j → Disjoint (A i) (A j)) :
    ∃ (P : IntervalPathCover H (clusterIntervalVertices A (2*q) (10*q)) (A (2*q)) (A (10*q))),
      P.digraph = E.arcs := by
  have meet (l m r : ℕ) (hl : l ≤ m) (hr : m ≤ r) (hr' : r ≤ 10*q) :=
    clusterIntervalVertices_inter A hl hr (fun i j _ hi _ hj he => hDis i j
      (hi.trans hr') (hj.trans hr') he)
  obtain ⟨P,hP,_⟩ := E.second.exists_concat E.third (meet _ _ _ (by omega) (by omega) (by omega))
  let P' := P.castSupport (clusterIntervalVertices_union A (by omega) (by omega))
  obtain ⟨Q,hQ,_⟩ := P'.exists_concat E.fourth (meet _ _ _ (by omega) (by omega) (by omega))
  let Q' := Q.castSupport (clusterIntervalVertices_union A (by omega) (by omega))
  obtain ⟨R,hR,_⟩ := Q'.exists_concat E.fifth (meet _ _ _ (by omega) (by omega) le_rfl)
  let R' := R.castSupport (clusterIntervalVertices_union A (by omega) (by omega))
  refine ⟨R',?_⟩
  calc
    R'.digraph = R.digraph := IntervalPathCover.castSupport_digraph _ _
    _ = (Q.digraph ⊔ E.fifth.digraph) :=
      hR.trans (congrArg (· ⊔ E.fifth.digraph) (IntervalPathCover.castSupport_digraph _ _))
    _ = E.arcs := by
      rw [hQ]
      have he : P'.digraph = P.digraph := IntervalPathCover.castSupport_digraph _ _
      rw [he,hP,CycleAbsorberExceptionalCovers.arcs]
      ac_rfl

omit [Fintype V] in
/-- Translate an entire closed interval along a change of cyclic
origin. Only the cluster indices are changed. -/
theorem clusterIntervalVertices_translate (A B : ℕ → Finset V) {l r s t : ℕ}
    (hs : s ≤ t) (hLen : r-l = t-s) (hl : l ≤ r)
    (hSlot : ∀ i, l ≤ i → i ≤ r → B i = A (s+(i-l))) :
    clusterIntervalVertices B l r = clusterIntervalVertices A s t := by
  ext x
  simp only [mem_clusterIntervalVertices]
  constructor
  · rintro ⟨i,hi,hir,hx⟩
    exact ⟨s+(i-l),by omega,by omega,hSlot i hi hir ▸ hx⟩
  · rintro ⟨i,hi,hit,hx⟩
    have h := hSlot (l+(i-s)) (by omega) (by omega)
    rw [show s+(l+(i-s)-l) = i by omega] at h
    exact ⟨l+(i-s),by omega,by omega,h.symm ▸ hx⟩

omit [Fintype V] in
/-- Reindex the second and fifth exceptional covers for the lower
half starting at cluster `7*q`. Both keep their exact arc sets. -/
theorem CycleAbsorberExceptionalCovers.exists_rotated {H : Digraph V} {q : ℕ}
    (X : Fin (14*q) → Finset V) (hk : 0 < 14*q)
    (E : CycleAbsorberExceptionalCovers H (cyclicCluster X hk) q) :
    let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
    ∃ (E₂ : IntervalPathCover H (clusterIntervalVertices B (9*q) (11*q)) (B (9*q)) (B (11*q)))
      (E₅ : IntervalPathCover H (clusterIntervalVertices B q (3*q)) (B q) (B (3*q))),
      E₂.digraph = E.second.digraph ∧ E₅.digraph = E.fifth.digraph := by
  intro B
  let A := cyclicCluster X hk
  have hB (i : ℕ) : B i = A (7*q+i) := cyclicCluster_rotateClusterArray X hk _ _
  have h₂ (i : ℕ) (hi : 9*q ≤ i) (_ : i ≤ 11*q) : B i = A (2*q+(i-9*q)) := by
    rw [hB]
    apply congrArg X
    apply Fin.ext
    change (7*q+i)%(14*q) = (2*q+(i-9*q))%(14*q)
    rw [show 7*q+i = 14*q+(2*q+(i-9*q)) by omega,Nat.add_mod_left]
  have h₅ (i : ℕ) (hi : q ≤ i) (_ : i ≤ 3*q) : B i = A (8*q+(i-q)) := by
    rw [hB,show 7*q+i = 8*q+(i-q) by omega]
  have hA₂ := clusterIntervalVertices_translate A B (s := 2*q) (t := 4*q)
    (by omega) (by omega) (by omega) h₂
  have hA₅ := clusterIntervalVertices_translate A B (s := 8*q) (t := 10*q)
    (by omega) (by omega) (by omega) h₅
  have h₂a : B (9*q) = A (2*q) := by simpa using h₂ (9*q) le_rfl (by omega)
  have h₂b : B (11*q) = A (4*q) := by
    rw [h₂ _ (by omega) le_rfl,show 2*q+(11*q-9*q) = 4*q by omega]
  have h₅a : B q = A (8*q) := by simpa using h₅ q le_rfl (by omega)
  have h₅b : B (3*q) = A (10*q) := by
    rw [h₅ _ (by omega) le_rfl,show 8*q+(3*q-q) = 10*q by omega]
  let E₂ := (E.second.castSupport hA₂.symm).castBoundaries h₂a.symm h₂b.symm
  let E₅ := (E.fifth.castSupport hA₅.symm).castBoundaries h₅a.symm h₅b.symm
  exact ⟨E₂,E₅,(IntervalPathCover.castBoundaries_digraph _ _ _).trans
    (IntervalPathCover.castSupport_digraph _ _),(IntervalPathCover.castBoundaries_digraph _ _ _).trans
    (IntervalPathCover.castSupport_digraph _ _)⟩

/-- Preparing the common routing host deletes the coincident arcs of
the projected exceptional covers and preserves superregularity. -/
theorem CycleAbsorberExceptionalCovers.residual_pair {G H : Digraph V} {A : ℕ → Finset V}
    {q m : ℕ} (E : CycleAbsorberExceptionalCovers H A q)
    (hDis : ∀ i j, i ≤ 10*q → j ≤ 10*q → i ≠ j → Disjoint (A i) (A j))
    (U W : Finset V) (hm : 0 < m) (hU : U.card = 2*m) (hW : W.card = 2*m)
    (ε η d a : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hBudget : 1 ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPair : IsLowerSuperregularPair G ε d U W) :
    IsLowerSuperregularPair (G \ E.arcs) η d U W := by
  obtain ⟨P,hP⟩ := E.exists_interval_cover hDis
  have hBound (L : Digraph V) (hL : L ≤ E.arcs) (v : V) :
      inDegree L v ≤ 1 ∧ outDegree L v ≤ 1 := by
    constructor
    · apply card_le_one.mpr
      intro x hx y hy
      exact P.is_path_system.in_unique (hP.symm ▸ hL (mem_filter.mp hx).2)
        (hP.symm ▸ hL (mem_filter.mp hy).2)
    · apply card_le_one.mpr
      intro x hx y hy
      exact P.is_path_system.out_unique (hP.symm ▸ hL (mem_filter.mp hx).2)
        (hP.symm ▸ hL (mem_filter.mp hy).2)
  have he : G \ (G ⊓ E.arcs) = G \ E.arcs := by
    ext x y
    simp only [Digraph.sdiff_adj,Digraph.inf_adj]
    tauto
  rw [←he]
  exact IsLowerSuperregularPair.after_bounded_arc_deletion inf_le_left 1 (hBound _ inf_le_right) U W
    (card_pos.mp (by rw [hU]; omega)) (card_pos.mp (by rw [hW]; omega)) _ hU hW
    ε η d a hη hη₁ ha hd hTol (by simpa only [Nat.cast_one] using hBudget) hPair

end OverfullWork.DirectedRobustExpansion
