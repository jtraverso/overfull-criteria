module

public import OverfullWork.KuhnOsthusCycleAbsorberClaimOne

@[expose] public section


/-! The first portion of the auxiliary factor S from the proof of
Kühn–Osthus Lemma 10.3. Use the crossed edges of both switches and
route their corresponding ends in the host left after the main paths. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*}

def OrderedClusterPaths.unionPaths {G : Digraph V} {A : ℕ → Finset V} {J : Type*} {l r : ℕ}
    (P : OrderedClusterPaths G A J l r) : Digraph V :=
  ⨆ j, P.pathDigraph j

theorem OrderedClusterPaths.unionPaths_le {G : Digraph V} {A : ℕ → Finset V} {J : Type*} {l r : ℕ}
    (P : OrderedClusterPaths G A J l r) : P.unionPaths ≤ G :=
  iSup_le P.pathDigraph_le

theorem OrderedClusterPaths.unionPaths_out_unique {G : Digraph V} {A : ℕ → Finset V} {J : Type*}
    {l r : ℕ} (P : OrderedClusterPaths G A J l r)
    (hDis : ∀ i k, l ≤ i → i ≤ r → l ≤ k → k ≤ r → i ≠ k → Disjoint (A i) (A k))
    {x y z : V} (h₁ : P.unionPaths.Adj x y) (h₂ : P.unionPaths.Adj x z) : y = z := by
  obtain ⟨j,i,hi,hir,hx,hy⟩ := Digraph.iSup_adj.mp h₁
  obtain ⟨j',i',hi',hir',hx',hz⟩ := Digraph.iSup_adj.mp h₂
  obtain ⟨rfl,rfl⟩ := P.unique_coordinates hDis hi hir.le hi' hir'.le (hx.symm.trans hx')
  exact hy.trans hz.symm

theorem OrderedClusterPaths.unionPaths_in_unique {G : Digraph V} {A : ℕ → Finset V} {J : Type*}
    {l r : ℕ} (P : OrderedClusterPaths G A J l r)
    (hDis : ∀ i k, l ≤ i → i ≤ r → l ≤ k → k ≤ r → i ≠ k → Disjoint (A i) (A k))
    {x y z : V} (h₁ : P.unionPaths.Adj x z) (h₂ : P.unionPaths.Adj y z) : x = y := by
  obtain ⟨j,i,hi,hir,hx,hz⟩ := Digraph.iSup_adj.mp h₁
  obtain ⟨j',i',hi',hir',hy,hz'⟩ := Digraph.iSup_adj.mp h₂
  obtain ⟨h,rfl⟩ := P.unique_coordinates hDis
    (show l ≤ i+1 by omega) (show i+1 ≤ r by omega) (show l ≤ i'+1 by omega)
    (show i'+1 ≤ r by omega) (hz.symm.trans hz')
  have he : i = i' := by omega
  subst i'
  exact hx.trans hy.symm

theorem OrderedClusterPaths.unionPaths_semidegrees [Fintype V] {G : Digraph V}
    {A : ℕ → Finset V} {J : Type*} {l r : ℕ} (P : OrderedClusterPaths G A J l r)
    (hDis : ∀ i k, l ≤ i → i ≤ r → l ≤ k → k ≤ r → i ≠ k → Disjoint (A i) (A k))
    (v : V) : inDegree P.unionPaths v ≤ 1 ∧ outDegree P.unionPaths v ≤ 1 := by
  constructor
  · unfold inDegree inNeighbours
    apply card_le_one.mpr
    intro x hx y hy
    exact P.unionPaths_in_unique hDis (mem_filter.mp hx).2 (mem_filter.mp hy).2
  · unfold outDegree
    apply card_le_one.mpr
    intro x hx y hy
    exact P.unionPaths_out_unique hDis (mem_filter.mp hx).2 (mem_filter.mp hy).2

/-- Deletion of a bounded number of arcs per vertex in a whole pair. -/
theorem IsLowerSuperregularPair.after_bounded_arc_deletion [Fintype V] {G L : Digraph V}
    (hL : L ≤ G) (k : ℕ) (hLoss : ∀ v, inDegree L v ≤ k ∧ outDegree L v ≤ k)
    (U W : Finset V) (hU : U.Nonempty) (hW : W.Nonempty) (m : ℕ)
    (hCardU : U.card = m) (hCardW : W.card = m)
    (ε η d a : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hTol : 2*(ε+a) ≤ η) (hBudget : (k:ℝ) ≤ a*((m:ℝ)*η))
    (H : IsLowerSuperregularPair G ε d U W) :
    IsLowerSuperregularPair (G \ L) η d U W := by
  obtain ⟨c,hc,hc₁,hG⟩ := H
  have hSmall : ε+a ≤ η := by linarith
  have hScale (Z : Finset V) : (Z.card:ℝ)*ε ≤ (Z.card:ℝ)*η :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hPay (Z : Finset V) (hZ : Z.card = m) :
      ε*(Z.card:ℝ)+((Z \ Z).card:ℝ)+(k:ℝ) ≤ η*(Z.card:ℝ) := by
    have hEmpty : (((Z \ Z).card:ℕ):ℝ) = 0 := by simp
    rw [hEmpty,hZ,add_zero]
    have h₁ := mul_le_mul_of_nonneg_right hSmall (Nat.cast_nonneg (α := ℝ) m)
    have h₂ := mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (Nat.cast_nonneg _ : (0:ℝ) ≤ m) hη₁) ha
    linarith only [h₁,h₂,hBudget]
  exact ⟨c,hc,hc₁,hG.on_pair_remainder G L hL U W U W
    (subset_refl _) (subset_refl _) hU hW c ε η a k (hd.trans hc) hc₁ hη hη₁ ha
    (hScale U) (hScale W) hTol (by simpa only [hCardU] using hBudget)
    (hPay U hCardU) (hPay W hCardW) (fun x _ => (hLoss x).2) (fun y _ => (hLoss y).1)⟩

/-- Explicit deletion margins for the case of a whole pair with
the arcs of a spanning path bundle removed. -/
theorem IsLowerSuperregularPair.after_path_bundle [Fintype V] {G : Digraph V}
    {A : ℕ → Finset V} {J : Type*} {l r : ℕ} (P : OrderedClusterPaths G A J l r)
    (hDis : ∀ i k, l ≤ i → i ≤ r → l ≤ k → k ≤ r → i ≠ k → Disjoint (A i) (A k))
    (U W : Finset V) (hU : U.Nonempty) (hW : W.Nonempty) (m : ℕ)
    (hCardU : U.card = m) (hCardW : W.card = m)
    (ε η d a : ℝ) (_hε : 0 ≤ ε) (hη : 0 < η) (hη₁ : η ≤ 1)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hTol : 2*(ε+a) ≤ η) (hBudget : 1 ≤ a*((m:ℝ)*η))
    (H : IsLowerSuperregularPair G ε d U W) :
    IsLowerSuperregularPair (G \ P.unionPaths) η d U W :=
  IsLowerSuperregularPair.after_bounded_arc_deletion P.unionPaths_le 1
    (P.unionPaths_semidegrees hDis) U W hU hW m hCardU hCardW ε η d a hη hη₁ ha hd hTol
    (by simpa only [Nat.cast_one] using hBudget) H

/-- The crossed switch edges survive deletion of any graph that
contains the primary paths and has at most one arc leaving each vertex. -/
theorem CycleAbsorberClaimOne.crossed_arcs_after_factor {G F : Digraph V} {A : ℕ → Finset V}
    {m n : ℕ} (C : CycleAbsorberClaimOne G A m n) (hn : 8 ≤ n)
    (hContain : C.paths.unionPaths ≤ F)
    (hUnique : ∀ {x y z}, F.Adj x y → F.Adj x z → y = z) :
    (∀ i b, (G \ F).Adj (C.first.source (cycleAbsorberSwitchSlot m (i,b)))
      (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 b)))) ∧
    ∀ i b, (G \ F).Adj (C.second.source (alternateCycleAbsorberSwitchSlot m (i,b)))
      (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 b))) := by
  have hFlip (b : Fin 2) : finRotate 2 b ≠ b := by fin_cases b <;> decide
  constructor
  · intro i b
    refine ⟨C.first.cross i b (finRotate 2 b),?_⟩
    intro h
    let j := cycleAbsorberSwitchSlot m (i,b)
    have hDiag : F.Adj (C.first.source j) (C.first.target j) := by
      rw [←C.firstSource,←C.firstTarget]
      exact hContain (Digraph.iSup_adj.mpr ⟨j,3,by decide,by omega,rfl,rfl⟩)
    have he := C.first.target.injective (Subtype.ext (hUnique h hDiag))
    exact hFlip b (congrArg Prod.snd ((cycleAbsorberSwitchSlot m).injective he))
  · intro i b
    refine ⟨C.second.cross i b (finRotate 2 b),?_⟩
    intro h
    let j := alternateCycleAbsorberSwitchSlot m (i,b)
    have hDiag : F.Adj (C.second.source j) (C.second.target j) := by
      rw [←C.secondSource,←C.secondTarget]
      exact hContain (Digraph.iSup_adj.mpr ⟨j,7,by decide,by omega,rfl,rfl⟩)
    have he := C.second.target.injective (Subtype.ext (hUnique h hDiag))
    exact hFlip b (congrArg Prod.snd ((alternateCycleAbsorberSwitchSlot m).injective he))

/-- Route through both prescribed crossed matchings in the common
residual host of the construction. -/
theorem CycleAbsorberClaimOne.exists_reserve_middle_in [Fintype V] {G D : Digraph V}
    {A : ℕ → Finset V} {m n : ℕ} (C : CycleAbsorberClaimOne G A m n)
    (hSize : ∀ i, 4 ≤ i → i ≤ 7 → (A i).card = 2*m)
    (hDis : ∀ i j, 4 ≤ i → i ≤ 7 → 4 ≤ j → j ≤ 7 → i ≠ j → Disjoint (A i) (A j))
    (hFirst : ∀ i b, D.Adj (C.first.source (cycleAbsorberSwitchSlot m (i,b)))
      (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 b))))
    (hSecond : ∀ i b, D.Adj (C.second.source (alternateCycleAbsorberSwitchSlot m (i,b)))
      (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 b))))
    (η d : ℝ) (hη : 0 ≤ η) (hGap : 2*η < d) (hd : d ≤ 1)
    (hPairs : ∀ i, 4 ≤ i → i < 7 → IsLowerSuperregularPair D η d (A i) (A (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRoute : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    ∃ S : OrderedClusterPaths D A (Fin m × Fin 2) 3 8,
      (∀ i b, S.vertex 3 (i,b) = (C.first.source (cycleAbsorberSwitchSlot m (i,b))).val) ∧
      (∀ i b, S.vertex 4 (i,b) = (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 b))).val) ∧
      (∀ i b, S.vertex 7 (i,b) = (C.second.source (alternateCycleAbsorberSwitchSlot m (i,b))).val) ∧
      ∀ i b, S.vertex 8 (i,b) = (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 b))).val := by
  let flip : Equiv.Perm (Fin m × Fin 2) := Equiv.prodCongr (.refl _) (finRotate 2)
  let s₀ := (cycleAbsorberSwitchSlot m).trans C.first.source
  let t₀ := (flip.trans (cycleAbsorberSwitchSlot m)).trans C.first.target
  let s₁ := (alternateCycleAbsorberSwitchSlot m).trans C.second.source
  let t₁ := (flip.trans (alternateCycleAbsorberSwitchSlot m)).trans C.second.target
  have hM₀ (p : Fin m × Fin 2) : D.Adj (s₀ p) (t₀ p) := hFirst p.1 p.2
  have hM₁ (p : Fin m × Fin 2) : D.Adj (s₁ p) (t₁ p) := hSecond p.1 p.2
  obtain ⟨P,hP₄,hP₇⟩ := exists_ordered_cluster_paths D A 4 7 (2*m) r (by decide) t₀ s₁
    η d hη hGap hd hr hCut hRoute hSize hDis hPairs
  let M₀ := OrderedClusterPaths.of_pair D A 3 s₀ t₀ hM₀
  let M₁ := OrderedClusterPaths.of_pair D A 7 s₁ t₁ hM₁
  let T := P.concat M₁ (fun j => by simp [M₁,hP₇ j])
  let S := M₀.concat T (fun j => by simp [M₀,T,OrderedClusterPaths.concat_left,hP₄ j])
  refine ⟨S,?_,?_,?_,?_⟩
  · intro i b
    exact (OrderedClusterPaths.concat_left _ _ _ (by decide) _).trans
      (OrderedClusterPaths.of_pair_left D A 3 s₀ t₀ hM₀ _)
  · intro i b
    exact (OrderedClusterPaths.concat_left _ _ _ (by decide) _).trans
      (OrderedClusterPaths.of_pair_right D A 3 s₀ t₀ hM₀ _)
  · intro i b
    have h : S.vertex 7 (i,b) = T.vertex 7 (i,b) := OrderedClusterPaths.concat_right _ _ _ (by decide) _
    rw [h]
    simp [T,OrderedClusterPaths.concat_left,hP₇ (i,b),s₁]
  · intro i b
    have h : S.vertex 8 (i,b) = T.vertex 8 (i,b) := OrderedClusterPaths.concat_right _ _ _ (by decide) _
    have h' : T.vertex 8 (i,b) = M₁.vertex 8 (i,b) := OrderedClusterPaths.concat_right _ _ _ (by decide) _
    rw [h,h']
    exact OrderedClusterPaths.of_pair_right D A 7 s₁ t₁ hM₁ _

/-- The left and right tracks of S keep the same copy index in
both switch pairs. In each pair the matching of S uses the crossed
edges rather than the corresponding edges of the main paths. -/
theorem CycleAbsorberClaimOne.exists_reserve_middle [Fintype V] {G : Digraph V} {A : ℕ → Finset V}
    {m n : ℕ} (C : CycleAbsorberClaimOne G A m n) (hn : 8 ≤ n)
    (hSize : ∀ i ≤ n, (A i).card = 2*m)
    (hDis : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (A i) (A j))
    (ε η d a : ℝ) (hε : 0 ≤ ε) (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a)
    (hGap : 2*η < d) (hd : d ≤ 1) (hTol : 2*(ε+a) ≤ η)
    (hBudget : 1 ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPairs : ∀ i, 4 ≤ i → i < 7 → IsLowerSuperregularPair G ε d (A i) (A (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
    (hRoute : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))) :
    let D := G \ C.paths.unionPaths
    ∃ S : OrderedClusterPaths D A (Fin m × Fin 2) 3 8,
      (∀ i b, S.vertex 3 (i,b) = (C.first.source (cycleAbsorberSwitchSlot m (i,b))).val) ∧
      (∀ i b, S.vertex 4 (i,b) = (C.first.target (cycleAbsorberSwitchSlot m (i,finRotate 2 b))).val) ∧
      (∀ i b, S.vertex 7 (i,b) = (C.second.source (alternateCycleAbsorberSwitchSlot m (i,b))).val) ∧
      ∀ i b, S.vertex 8 (i,b) = (C.second.target (alternateCycleAbsorberSwitchSlot m (i,finRotate 2 b))).val := by
  intro D
  have hDis' (i j : ℕ) (_ : 0 ≤ i) (hi : i ≤ n) (_ : 0 ≤ j) (hj : j ≤ n) (he : i ≠ j) :=
    hDis i j hi hj he
  obtain ⟨hFirst,hSecond⟩ := C.crossed_arcs_after_factor hn (le_refl C.paths.unionPaths)
    (C.paths.unionPaths_out_unique hDis')
  have hRes (i : ℕ) (hi : 4 ≤ i) (hi' : i < 7) : IsLowerSuperregularPair D η d (A i) (A (i+1)) := by
    have hm : 0 < m := by
      by_contra! h
      have he : m = 0 := by omega
      rw [he] at hBudget
      norm_num at hBudget
    exact IsLowerSuperregularPair.after_path_bundle C.paths (fun j k _ hj _ hk h => hDis j k hj hk h)
      (A i) (A (i+1)) (card_pos.mp (by rw [hSize i (by omega)]; omega))
      (card_pos.mp (by rw [hSize (i+1) (by omega)]; omega)) (2*m)
      (hSize i (by omega)) (hSize (i+1) (by omega))
      ε η d a hε hη hη₁ ha (by linarith) hTol hBudget (hPairs i hi hi')
  exact C.exists_reserve_middle_in (fun i _ hi => hSize i (by omega))
    (fun i j _ hi _ hj he => hDis i j (by omega) (by omega) he)
    hFirst hSecond η d hη.le hGap hd hRes r hr hCut hRoute

end OverfullWork.DirectedRobustExpansion
