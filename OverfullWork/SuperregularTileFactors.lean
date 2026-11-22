module

public import OverfullWork.SuperregularTileAugmentation

@[expose] public section


/-! A spanning tile factor from rectangle bounds and minimum degrees.
The two alternatives for a maximal packing are adding a tile in the
unused vertices and swapping a bounded group of already packed tiles. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*} [Fintype V]

omit [Fintype V] in
theorem LayeredTilePacking.slot_range {p k : ℕ} {X : Fin p → Finset V}
    {E : Fin p → Fin p → Bool} {R : Fin p → Fin p → Digraph V}
    (P : LayeredTilePacking X E R k) (a : Fin p) :
    let S := (univ : Finset (Fin k)).image (fun i => P.vertices (i,a))
    S ⊆ X a ∧ S.card = k := by
  refine ⟨?_,?_⟩
  · intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact P.mem i a
  · rw [card_image_of_injective _ (fun x y h => congrArg (fun z : Fin k × Fin p => z.1)
      (P.vertices.injective h)),card_univ,Fintype.card_fin]

omit [Fintype V] in
theorem LayeredTilePacking.covers_part {p k : ℕ} {X : Fin p → Finset V}
    {E : Fin p → Fin p → Bool} {R : Fin p → Fin p → Digraph V}
    (P : LayeredTilePacking X E R k) (a : Fin p) (hSize : (X a).card = k) (v : V)
    (hv : v ∈ X a) : ∃ i, P.vertices (i,a) = v := by
  obtain ⟨hS,hCard⟩ := P.slot_range a
  have hEq := eq_of_subset_of_card_le hS (by rw [hCard,hSize])
  obtain ⟨i,_,hi⟩ := mem_image.mp (hEq.symm ▸ hv)
  exact ⟨i,hi⟩

private theorem geometric_room {n : ℕ} {K η s : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hs : 0 ≤ s) (hK : K < η^n*s) {j : ℕ} (hj : j ≤ n) : K < η^j*s :=
  hK.trans_le (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hη hη₁ hj) hs)

/-- The degrees supply the initial candidates for a repair, and each
lower rectangle bound survives transport through the old packing.
The exponents account for intersections in the two greedy embeddings. -/
theorem exists_spanning_layered_tile_packing {p h m : ℕ} (X : Fin p → Finset V)
    (E : Fin p → Fin p → Bool) (R : Fin p → Fin p → Digraph V)
    (shift : Fin p → Fin (h+1)) (S : TileShiftPattern E shift)
    (r : ℕ) (η δ small : ℝ)
    (hr : 0 < r) (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : δ ≤ 1)
    (hSmall : 0 ≤ small) (hSeed : 0 ≤ δ*(m:ℝ)-small)
    (hAdd : ((p*r+p : ℕ):ℝ) < η^p*small)
    (hRepair : ((h*r+h : ℕ):ℝ) < η^h*(δ*(m:ℝ)-small))
    (hSize : ∀ a, (X a).card = m)
    (hDisj : ∀ a b, a ≠ b → Disjoint (X a) (X b))
    (hOrder : ∀ a b, E a b = true → a < b)
    (hSym : ∀ a b u v, (R a b).Adj u v ↔ (R b a).Adj v u)
    (hRect : ∀ a b, tilesTouch E a b → TileRectangleBound (R a b) (X a) (X b) r η)
    (hDeg : ∀ a b, tilesTouch E a b → ∀ v ∈ X a, δ*(m:ℝ) ≤ (outTo (R a b) (X b) v:ℝ)) :
    Nonempty (LayeredTilePacking X E R m) := by
  let sizes := (range (m+1)).filter (fun k => Nonempty (LayeredTilePacking X E R k))
  have hZero : 0 ∈ sizes := mem_filter.mpr ⟨mem_range.mpr (by omega),⟨
    ⟨⟨fun z => z.1.elim0,fun ⟨i,_⟩ => i.elim0⟩,fun i => i.elim0,fun i => i.elim0⟩⟩⟩
  obtain ⟨k,hk,hMax⟩ := exists_max_image sizes id ⟨0,hZero⟩
  obtain ⟨hkM,⟨P⟩⟩ := mem_filter.mp hk
  have hkLe : k ≤ m := by have := mem_range.mp hkM; omega
  by_cases heq : k = m
  · subst m
    exact ⟨P⟩
  let used (a : Fin p) := (univ : Finset (Fin k)).image (fun i => P.vertices (i,a))
  let free (a : Fin p) := X a \ used a
  have hUsed (a : Fin p) : used a ⊆ X a := (P.slot_range a).1
  have hFree (a : Fin p) : (free a).card = m-k := by
    rw [show free a = X a \ used a from rfl,card_sdiff_of_subset (hUsed a),hSize,(P.slot_range a).2]
  have hFreeApart {a b : Fin p} (v : V) (hv : v ∈ free a) (i : Fin k) :
      v ≠ P.vertices (i,b) := by
    intro h
    have hvA : v ∈ X a := (mem_sdiff.mp hv).1
    have hvB : v ∈ X b := h ▸ P.mem i b
    have hab : a = b := by
      by_contra hn
      exact (disjoint_left.mp (hDisj a b hn)) hvA hvB
    subst b
    exact (mem_sdiff.mp hv).2 (mem_image.mpr ⟨i,mem_univ _,h.symm⟩)
  suffices hAug : Nonempty (LayeredTilePacking X E R (k+1)) by
    have h := hMax (k+1) (mem_filter.mpr ⟨mem_range.mpr (by omega),hAug⟩)
    change k+1 ≤ k at h
    omega
  by_cases hLarge : small ≤ ((m-k : ℕ):ℝ)
  · let Q (a b : Fin p) (u v : V) := if E a b = true then (R a b).Adj u v else True
    have hBad (a b : Fin p) (_ : a < b) (Y : Finset V) (hY : Y ⊆ free b) (hYC : r ≤ Y.card) :
        ((free a).filter (fun x => ((@Finset.filter _ (Q a b x) (Classical.decPred _) Y).card:ℝ) <
          η*(Y.card:ℝ))).card ≤ r := by
      by_cases hab : E a b = true
      · have h := card_bad_rows_of_rectangle (R a b) (free a) (X b) Y r η hr
          (hY.trans sdiff_subset) hYC ((hRect a b (.inl hab)).restrict sdiff_subset (fun _ h => h))
        have hCount (x : V) : (@Finset.filter _ (Q a b x) (Classical.decPred _) Y).card =
            outTo (R a b) Y x := by
          unfold outTo
          apply congrArg Finset.card
          ext v
          simp only [mem_filter,Q,if_pos hab]
        simpa only [hCount] using h.le
      · have hNot : ¬ (Y.card:ℝ) < η*(Y.card:ℝ) := not_lt_of_ge (by
          simpa using mul_le_mul_of_nonneg_right hη₁ (Nat.cast_nonneg (α := ℝ) Y.card))
        have hFilter (x : V) : @Finset.filter _ (Q a b x) (Classical.decPred _) Y = Y := by
          ext v
          simp only [mem_filter,Q,if_neg hab,and_true]
        simp [hFilter,hNot]
    obtain ⟨f,hInject,hMem,hEdges⟩ := exists_injective_greedy_embedding free Q r η (fun n => η^n*small) hη
      (fun a => by simpa only [pow_zero,one_mul,hFree] using hLarge)
      (fun _ hn => geometric_room hη hη₁ hSmall hAdd hn)
      (fun n _ => by apply le_of_eq; rw [pow_succ]; ring) hBad
    let root : Fin p ↪ V := ⟨f,hInject⟩
    let old : Fin 0 ↪ Fin k := ⟨Fin.elim0,fun i => i.elim0⟩
    refine ⟨P.augmentByShift root (fun a => (mem_sdiff.mp (hMem a)).1)
      (fun a i b => hFreeApart _ (hMem a) i) old (fun _ => 0) ?_⟩
    intro i a b hab
    have hi : i = 0 := Fin.ext (by have := i.isLt; change i.val = 0; omega)
    subst i
    simp only [add_zero,LayeredTilePacking.augmentationVertex,Fin.cases_zero]
    change (R a b).Adj (f a) (f b)
    simpa only [Q,if_pos hab] using hEdges a b (hOrder a b hab)
  · have hSmallFree (a : Fin p) : ((free a).card:ℝ) < small := by
      rw [hFree]
      exact lt_of_not_ge hLarge
    have hPos (a : Fin p) : 0 < (free a).card := by rw [hFree]; omega
    choose f hf using fun a => card_pos.mp (hPos a)
    have hfInj : Injective f := by
      intro a b he
      by_contra hn
      exact (disjoint_left.mp (hDisj a b hn)) (mem_sdiff.mp (hf a)).1 (he ▸ (mem_sdiff.mp (hf b)).1)
    let root : Fin p ↪ V := ⟨f,hfInj⟩
    have hPool : δ*(m:ℝ)-small ≤ (k:ℝ) := by
      have hM : (m:ℝ) = (k:ℝ) + ((m-k:ℕ):ℝ) := by exact_mod_cast (Nat.add_sub_cancel' hkLe).symm
      have hLower := mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (α := ℝ) m)
      have hSmall' := lt_of_not_ge hLarge
      linarith only [hM,hLower,hSmall']
    have hNeighbour (a b : Fin p) (hab : tilesTouch E a b) :
        δ*(m:ℝ)-small ≤ (((univ : Finset (Fin k)).filter
          (fun j => (R a b).Adj (root a) (P.vertices (j,b)))).card:ℝ) := by
      let w := root a
      let N := (X b).filter ((R a b).Adj w)
      let C := (univ : Finset (Fin k)).filter (fun j => (R a b).Adj w (P.vertices (j,b)))
      have hUsedCard : ((used b).filter ((R a b).Adj w)).card = C.card := by
        change ((univ.image (fun j => P.vertices (j,b))).filter ((R a b).Adj w)).card = C.card
        rw [filter_image, card_image_of_injective _ (fun x y h =>
          congrArg (fun z : Fin k × Fin p => z.1) (P.vertices.injective h))]
      have hN : N.card ≤ (free b).card + C.card := by
        have hSub : N ⊆ free b ∪ (used b).filter ((R a b).Adj w) := by
          intro y hy
          obtain ⟨hyX,hyN⟩ := mem_filter.mp hy
          by_cases h : y ∈ used b
          · exact mem_union_right _ (mem_filter.mpr ⟨h,hyN⟩)
          · exact mem_union_left _ (mem_sdiff.mpr ⟨hyX,h⟩)
        exact (card_le_card hSub).trans ((card_union_le _ _).trans_eq (by rw [hUsedCard]))
      have hNC : (N.card:ℝ) ≤ ((free b).card:ℝ)+(C.card:ℝ) := by exact_mod_cast hN
      have hD : δ*(m:ℝ) ≤ (N.card:ℝ) := hDeg a b hab _ (mem_sdiff.mp (hf a)).1
      have hUnused := hSmallFree b
      change δ*(m:ℝ)-small ≤ (C.card:ℝ)
      linarith only [hNC,hD,hUnused]
    exact P.exists_augmentation_of_root_neighbours root (fun a => (mem_sdiff.mp (hf a)).1)
      (fun a i b => hFreeApart _ (hf a) i) shift S r η (fun n => η^n*(δ*(m:ℝ)-small))
      hr hη hη₁ (fun _ hn => geometric_room hη hη₁ hSeed hRepair hn)
      (fun n _ => by apply le_of_eq; rw [pow_succ]; ring)
      (by simpa only [pow_zero,one_mul] using hPool) hSym hRect
      (fun a b hab => by simpa only [pow_zero,one_mul] using hNeighbour a b hab)

end OverfullWork.DirectedRobustExpansion
