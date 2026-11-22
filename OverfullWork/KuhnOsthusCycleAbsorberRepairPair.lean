module

public import OverfullWork.KuhnOsthusCycleAbsorberReserveMiddle
public import OverfullWork.KuhnOsthusPrescribedMatchings

@[expose] public section


/-! Choose the final repair switch on V₁₂→V₁₃. Its diagonal
is extended to the whole pair, and its two positions are specified
before joining the paths that come from V₉. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V J : Type*}

noncomputable def OrderedClusterPaths.orderAt {G : Digraph V} {A : ℕ → Finset V} {l r : ℕ}
    (P : OrderedClusterPaths G A J l r) (i : ℕ) (hi : l ≤ i) (hir : i ≤ r) : J ≃ A i :=
  Equiv.ofBijective (fun j => ⟨P.vertex i j,P.part i hi hir j⟩)
    ⟨fun a b h => P.injective i hi hir (congrArg (fun z : A i => z.val) h),
      fun v => by
        obtain ⟨j,hj⟩ := P.covers i hi hir v.val v.prop
        exact ⟨j,Subtype.ext hj⟩⟩

@[simp] theorem OrderedClusterPaths.orderAt_val {G : Digraph V} {A : ℕ → Finset V} {l r : ℕ}
    (P : OrderedClusterPaths G A J l r) (i : ℕ) (hi : l ≤ i) (hir : i ≤ r) (j : J) :
    (P.orderAt i hi hir j).val = P.vertex i j := rfl

/-- Change a bijection at two prescribed labels. The second swap
fixes the label already set by the first swap. -/
theorem exists_equiv_with_two_values {A B : Type*} (e : A ≃ B)
    {x y : A} {u v : B} (hxy : x ≠ y) (huv : u ≠ v) :
    ∃ f : A ≃ B, f x = u ∧ f y = v := by
  let g : A ≃ B := (Equiv.swap x (e.symm u)).trans e
  have hx : g x = u := by simp [g]
  have hz : x ≠ g.symm v := by
    intro h
    exact huv (hx.symm.trans ((congrArg g h).trans (g.apply_symm_apply v)))
  let f := (Equiv.swap y (g.symm v)).trans g
  refine ⟨f,?_,?_⟩
  · change g (Equiv.swap y (g.symm v) x) = u
    rw [Equiv.swap_apply_of_ne_of_ne hxy hz,hx]
  · simp [f]

private noncomputable def pairEnumeration {x y : V} (h : x ≠ y) : Fin 2 ≃ ({x,y} : Finset V) := by
  let pick (i : Fin 2) : ({x,y} : Finset V) :=
    if i = 0 then ⟨x,by simp⟩ else ⟨y,by simp⟩
  apply Equiv.ofBijective pick
  constructor
  · intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · exact (h (congrArg (fun w : ({x,y} : Finset V) => w.val) he)).elim
    · exact (h.symm (congrArg (fun w : ({x,y} : Finset V) => w.val) he)).elim
    · rfl
  · intro v
    rcases mem_insert.mp v.prop with hv | hv
    · exact ⟨0,Subtype.ext hv.symm⟩
    · exact ⟨1,Subtype.ext (mem_singleton.mp hv).symm⟩

/-- Select a repair switch and reserve its diagonal inside a
matching on the entire layer. -/
theorem IsLowerSuperregularPair.exists_matching_with_repair_switch [Fintype V]
    (G : Digraph V) (A B : Finset V) (m r : ℕ) (ε d : ℝ)
    (hPair : IsLowerSuperregularPair G ε d A B)
    (hA : A.card = 2*m) (hB : B.card = 2*m) (hSize : 0 < m)
    (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    ∃ (f : A ≃ B) (u : Fin 2 ↪ A),
      (∀ x : A, G.Adj x (f x)) ∧ ∀ i j, G.Adj (u i) (f (u j)) := by
  have hη : 0 ≤ d-2*ε := by linarith
  have hη₁ : d-2*ε ≤ 1 := by linarith
  have hδ : 0 ≤ (d-ε)*((2*m:ℕ):ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hPow : (d-2*ε)^14 ≤ d-2*ε := by
    simpa only [pow_one] using pow_le_pow_of_le_one hη hη₁ (by decide : 1 ≤ 14)
  have hDeg := mul_le_mul_of_nonneg_right hPow hδ
  have hDeg' := mul_le_mul_of_nonneg_right (pow_le_one₀ hη hη₁ (n := 14)) hδ
  have hLarge : 2 ≤ A.card := by rw [hA]; omega
  have hLeft : (A.card:ℝ)*ε ≤ ((A.card-1:ℕ):ℝ) := by
    have he : (A.card:ℝ)*ε ≤ (A.card:ℝ)/2 := by
      have h := mul_le_mul_of_nonneg_left (show ε ≤ (1:ℝ)/2 by linarith) (Nat.cast_nonneg A.card)
      linarith
    have hTwo : (2:ℝ) ≤ A.card := by exact_mod_cast hLarge
    rw [Nat.cast_sub (by omega),Nat.cast_one]
    linarith only [he,hTwo]
  have hRight : (B.card:ℝ)*ε ≤ (d-ε)*(B.card:ℝ) := by
    rw [mul_comm (B.card:ℝ) ε]
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hSwitch : (2:ℝ) ≤ (d-2*ε)*((d-ε)*(B.card:ℝ)) := by
    rw [hB]
    have hR := Nat.cast_nonneg (α := ℝ) r
    linarith only [hBudget,hDeg,hR]
  obtain ⟨x,hx,y,hy,hxy,T,hT,hTcard,hSwitchEdges⟩ :=
    hPair.exists_common_switch_targets G A B d ε 2 hGap hLarge hLeft hRight hSwitch
  let S : Finset V := {x,y}
  have hS : S ⊆ A := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact hx
    · exact mem_singleton.mp hv ▸ hy
  have hScard : S.card = 2 := by simp [S,hxy]
  let p : Fin 2 ≃ S := pairEnumeration hxy
  let q : Fin 2 ≃ T := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hTcard)).symm
  let e := p.symm.trans q
  have hEdges (u : S) (v : T) : G.Adj u v := by
    have hv := hSwitchEdges v.val v.prop
    rcases mem_insert.mp u.prop with hu | hu
    · exact hu.symm ▸ hv.1
    · exact (mem_singleton.mp hu).symm ▸ hv.2
  have hMargin : (r:ℝ)+(S.card:ℝ) ≤ (d-ε)*(A.card:ℝ) := by
    rw [hA,hScard]
    simp only [one_mul] at hDeg'
    norm_num only [Nat.cast_ofNat]
    linarith only [hBudget,hDeg',Nat.cast_nonneg (α := ℝ) r]
  obtain ⟨f,hf,hFixed⟩ := hPair.extend_prescribed_matching G A B S T d ε r hS hT
    (hA.trans hB.symm) e (fun u => hEdges u (e u)) hGap hr (by rwa [hA]) hMargin
  let u : Fin 2 ↪ A := ⟨fun i => ⟨(p i).val,hS (p i).prop⟩,
    fun i j h => p.injective (Subtype.ext (congrArg (fun v : A => v.val) h))⟩
  refine ⟨f,u,hf,?_⟩
  intro i j
  change G.Adj (p i).val (f ⟨(p j).val,hS (p j).prop⟩).val
  rw [hFixed (p j)]
  exact hEdges (p i) (e (p j))

/-- Complete the first open portion of S through the repair layer.
The two marked edges are on the two tracks of one designated copy
index, with all four possible cross arcs available in the host. -/
theorem exists_ordered_paths_through_repair_pair [Fintype V] {D : Digraph V}
    {A : ℕ → Finset V} {m l : ℕ}
    (S : OrderedClusterPaths D A (Fin m × Fin 2) l 8) (hl : l ≤ 8)
    (mark : Fin m) (hSize : ∀ i, 8 ≤ i → i ≤ 12 → (A i).card = 2*m)
    (hDis : ∀ i j, 8 ≤ i → i ≤ 12 → 8 ≤ j → j ≤ 12 → i ≠ j → Disjoint (A i) (A j))
    (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hPairs : ∀ i, 8 ≤ i → i < 12 → IsLowerSuperregularPair D ε d (A i) (A (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    ∃ T : OrderedClusterPaths D A (Fin m × Fin 2) l 12,
      (∀ i ≤ 8, ∀ j, T.vertex i j = S.vertex i j) ∧
      ∀ a b : Fin 2, D.Adj (T.vertex 11 (mark,a)) (T.vertex 12 (mark,b)) := by
  obtain ⟨f,u,hf,hCross⟩ := (hPairs 11 (by decide) (by decide)).exists_matching_with_repair_switch
    D (A 11) (A 12) m r ε d (hSize 11 (by decide) (by decide))
    (hSize 12 (by decide) (by decide)) (Nat.zero_lt_of_lt mark.isLt) hε hGap hd hr hCut hBudget
  let e : Fin m × Fin 2 ≃ A 11 := (cycleAbsorberSwitchSlot m).trans
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hSize 11 (by decide) (by decide))).symm
  obtain ⟨e',h₀,h₁⟩ := exists_equiv_with_two_values e
    (show (mark,0) ≠ (mark,1) from fun he => (by decide : (0:Fin 2) ≠ 1) (congrArg Prod.snd he))
    (show u 0 ≠ u 1 from u.injective.ne (by decide))
  have hMark (a : Fin 2) : e' (mark,a) = u a := by fin_cases a <;> assumption
  obtain ⟨P,hP₈,hP₁₁⟩ := exists_ordered_cluster_paths D A 8 11 (2*m) r
    (by decide) (S.orderAt 8 hl le_rfl) e' ε d hε hGap hd hr hCut hBudget
    (fun i hi hir => hSize i hi (by omega))
    (fun i j hi hir hj hjr h => hDis i j hi (by omega) hj (by omega) h)
    (fun i hi hir => hPairs i hi (by omega))
  let M := OrderedClusterPaths.of_pair D A 11 e' (e'.trans f) (fun j => hf (e' j))
  have hML (j : Fin m × Fin 2) : M.vertex 11 j = (e' j).val :=
    OrderedClusterPaths.of_pair_left D A 11 e' (e'.trans f) _ j
  have hMR (j : Fin m × Fin 2) : M.vertex 12 j = (f (e' j)).val :=
    OrderedClusterPaths.of_pair_right D A 11 e' (e'.trans f) _ j
  let Q := P.concat M (fun j => (hP₁₁ j).trans (hML j).symm)
  let T := S.concat Q (fun j => by simp [Q,OrderedClusterPaths.concat_left,hP₈ j])
  refine ⟨T,?_,?_⟩
  · intro i hi j
    exact OrderedClusterPaths.concat_left _ _ _ hi j
  · intro a b
    have hL : T.vertex 11 (mark,a) = P.vertex 11 (mark,a) :=
      (OrderedClusterPaths.concat_right _ _ _ (by decide) _).trans
        (OrderedClusterPaths.concat_left _ _ _ (by decide) _)
    have hR : T.vertex 12 (mark,b) = M.vertex 12 (mark,b) :=
      (OrderedClusterPaths.concat_right _ _ _ (by decide) _).trans
        (OrderedClusterPaths.concat_right _ _ _ (by decide) _)
    rw [hL,hR,hP₁₁,hMR,hMark,hMark]
    exact hCross a b

end OverfullWork.DirectedRobustExpansion
