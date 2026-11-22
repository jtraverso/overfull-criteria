module

public import OverfullWork.BalancedCutPerturbation

@[expose] public section


/-! # Construct the heavy-neighbour adjustment of CMS Case 2, Step 1

Two actual balanced repairs are constructed, one near each orientation
of the original cut. Their total centre weight is at most the total
weight. One therefore has centre weight at most one half, while every
heavy neighbour and the second anchor lie opposite the centre.
-/
namespace OverfullWork.HeavyNeighbourCutRepair
open Finset BalancedCutPerturbation
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

theorem pool_card (A Z : Finset V) (a : V) (ha : a ∈ A) (haZ : a ∉ Z) :
    (A\insert a Z).card+(Z∩A).card+1 = A.card := by
  have hi : A∩insert a Z = insert a (Z∩A) := by
    ext x
    by_cases hx : x = a
    · subst x; simp [ha]
    · simp [hx];tauto
  have hs := card_sdiff_add_card_inter A (insert a Z)
  rw [hi, card_insert_of_notMem (by simp [haZ])] at hs
  omega

theorem exists_repaired_cut (A Z : Finset V) (a b : V) (m L : ℕ) (w : V → ℕ)
    (hA : A.card = m) (hAc : Aᶜ.card = m) (ha : a ∈ A) (hb : b ∉ A)
    (haZ : a ∉ Z) (hbZ : b ∉ Z) (hwa : w a = 0)
    (hHeavy : ∀ z ∈ Z, L ≤ w z)
    (hLight : ∀ z, z ∉ Z → z ≠ a → z ≠ b → w z ≤ L)
    (hRoom : Z.card+1 ≤ m) :
    ∃ B : Finset V, B.card = m ∧ Bᶜ.card = m ∧ a ∈ B ∧ b ∉ B ∧
      Disjoint B Z ∧ (∑ z ∈ B, w z) ≤ ∑ z ∈ Bᶜ, w z ∧
      (Close A B (Z.card+1) ∨ Close Aᶜ B (Z.card+1)) := by
  let zl := (Z∩A).card
  let zr := (Z∩Aᶜ).card
  have hz : zl+zr = Z.card := by
    have h := card_sdiff_add_card_inter Z A
    have he : Z\A = Z∩Aᶜ := by ext x; simp
    rw [he] at h
    dsimp only [zl,zr]
    omega
  have hLP := pool_card A Z a ha haZ
  have hRP := pool_card Aᶜ Z b (mem_compl.mpr hb) hbZ
  obtain ⟨P,hPsub,hPcard⟩ := exists_subset_card_eq
    (show zr ≤ (A\insert a Z).card by dsimp only [zl,zr] at *; omega)
  obtain ⟨T,hTsub,hTcard⟩ := exists_subset_card_eq
    (show zl ≤ (Aᶜ\insert b Z).card by dsimp only [zl,zr] at *; omega)
  have hP : ∀ x ∈ P, x ∈ A ∧ x ∉ Z ∧ x ≠ a := by
    intro x hx
    have hp := mem_sdiff.mp (hPsub hx)
    exact ⟨hp.1,fun hz => hp.2 (mem_insert_of_mem hz),fun he => hp.2 (he ▸ mem_insert_self a Z)⟩
  have hT : ∀ x ∈ T, x ∉ A ∧ x ∉ Z ∧ x ≠ b := by
    intro x hx
    have ht := mem_sdiff.mp (hTsub hx)
    exact ⟨mem_compl.mp ht.1,fun hz => ht.2 (mem_insert_of_mem hz),
      fun he => ht.2 (he ▸ mem_insert_self b Z)⟩
  have haP : a ∉ P := fun h => (hP a h).2.2 rfl
  have haT : a ∉ T := fun h => (hT a h).1 ha
  have hPT : Disjoint P T := disjoint_left.mpr (fun x hp ht => (hT x ht).1 (hP x hp).1)
  let B₁ := (A\Z)∪T
  let B₂ := (Aᶜ\insert b Z)∪insert a P
  have hDis₁ : Disjoint (A\Z) T := disjoint_left.mpr
    (fun x hx ht => (hT x ht).1 (mem_sdiff.mp hx).1)
  have hDis₂ : Disjoint (Aᶜ\insert b Z) (insert a P) := by
    apply disjoint_left.mpr
    intro x hx hp
    have hxA := mem_compl.mp (mem_sdiff.mp hx).1
    rcases mem_insert.mp hp with rfl | hp
    · exact hxA ha
    · exact hxA (hP x hp).1
  have hB₁ : B₁.card = m := by
    dsimp only [B₁]
    rw [card_union_of_disjoint hDis₁,hTcard]
    have hs := card_sdiff_add_card_inter A Z
    rw [inter_comm A Z,hA] at hs
    exact hs
  have hB₂ : B₂.card = m := by
    dsimp only [B₂]
    rw [card_union_of_disjoint hDis₂,card_insert_of_notMem haP,hPcard]
    omega
  have hB₁a : a ∈ B₁ := mem_union_left _ (mem_sdiff.mpr ⟨ha,haZ⟩)
  have hB₂a : a ∈ B₂ := mem_union_right _ (mem_insert_self _ _)
  have hB₁b : b ∉ B₁ := by
    intro h
    rcases mem_union.mp h with h | h
    · exact hb (mem_sdiff.mp h).1
    · exact (hT b h).2.2 rfl
  have hB₂b : b ∉ B₂ := by
    intro h
    rcases mem_union.mp h with h | h
    · exact (mem_sdiff.mp h).2 (mem_insert_self _ _)
    · rcases mem_insert.mp h with h | h
      · exact hb (h ▸ ha)
      · exact hb (hP b h).1
  have hB₁Z : Disjoint B₁ Z := by
    apply disjoint_left.mpr
    intro x hx hz
    rcases mem_union.mp hx with h | h
    · exact (mem_sdiff.mp h).2 hz
    · exact (hT x h).2.1 hz
  have hB₂Z : Disjoint B₂ Z := by
    apply disjoint_left.mpr
    intro x hx hz
    rcases mem_union.mp hx with h | h
    · exact (mem_sdiff.mp h).2 (mem_insert_of_mem hz)
    · rcases mem_insert.mp h with rfl | h
      · exact haZ hz
      · exact (hP x h).2.1 hz
  have hUnion : B₁∪B₂ = (insert b Z)ᶜ := by
    ext x
    constructor
    · intro hx
      have hnot : x ∉ Z ∧ x ≠ b := by
        rcases mem_union.mp hx with hx₁ | hx₂
        · exact ⟨fun hz => disjoint_left.mp hB₁Z hx₁ hz,fun he => hB₁b (he ▸ hx₁)⟩
        · exact ⟨fun hz => disjoint_left.mp hB₂Z hx₂ hz,fun he => hB₂b (he ▸ hx₂)⟩
      exact mem_compl.mpr (by simp [hnot.1,hnot.2])
    · intro hx
      have hn : x ≠ b ∧ x ∉ Z := by simpa using (mem_compl.mp hx)
      by_cases hxA : x ∈ A
      · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨hxA,hn.2⟩))
      · exact mem_union_right _ (mem_union_left _
          (mem_sdiff.mpr ⟨mem_compl.mpr hxA,by simp [hn.1,hn.2]⟩))
  have hInter : B₁∩B₂ = insert a (P∪T) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx₁,hx₂⟩ := mem_inter.mp hx
      rcases mem_union.mp hx₁ with hxA | hxT
      · rcases mem_union.mp hx₂ with hxAc | hxP
        · exact False.elim ((mem_compl.mp (mem_sdiff.mp hxAc).1) (mem_sdiff.mp hxA).1)
        · rcases mem_insert.mp hxP with he | hp
          · exact mem_insert.mpr (Or.inl he)
          · exact mem_insert_of_mem (mem_union_left _ hp)
      · exact mem_insert_of_mem (mem_union_right _ hxT)
    · intro hx
      rcases mem_insert.mp hx with he | hpT
      · subst x; exact mem_inter.mpr ⟨hB₁a,hB₂a⟩
      · rcases mem_union.mp hpT with hp | ht
        · exact mem_inter.mpr ⟨mem_union_left _ (mem_sdiff.mpr ⟨(hP x hp).1,(hP x hp).2.1⟩),
            mem_union_right _ (mem_insert_of_mem hp)⟩
        · exact mem_inter.mpr ⟨mem_union_right _ ht,mem_union_left _ (hTsub ht)⟩
  have hPw : (∑ x ∈ P, w x) ≤ L*P.card := by
    calc
      _ ≤ ∑ _x ∈ P, L := sum_le_sum (fun x hx => hLight x (hP x hx).2.1
        (hP x hx).2.2 (fun he => hb (he ▸ (hP x hx).1)))
      _ = _ := by simp [Nat.mul_comm]
  have hTw : (∑ x ∈ T, w x) ≤ L*T.card := by
    calc
      _ ≤ ∑ _x ∈ T, L := sum_le_sum (fun x hx => hLight x (hT x hx).2.1
        (fun he => (hT x hx).1 (he ▸ ha)) (hT x hx).2.2)
      _ = _ := by simp [Nat.mul_comm]
  have hZw : L*Z.card ≤ ∑ x ∈ Z, w x := by
    calc
      _ = ∑ _x ∈ Z, L := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum hHeavy
  have hInterw : (∑ x ∈ B₁∩B₂, w x) ≤ ∑ x ∈ insert b Z, w x := by
    rw [hInter,sum_insert (by simp [haP,haT]),hwa,zero_add,sum_union hPT,
      sum_insert hbZ]
    rw [hPcard] at hPw
    rw [hTcard] at hTw
    have he : L*zr+L*zl = L*Z.card := by rw [←mul_add];congr 1;omega
    omega
  have hSums : (∑ x ∈ B₁, w x)+(∑ x ∈ B₂, w x) ≤ ∑ x, w x := by
    have hsum := sum_union_inter (s₁ := B₁) (s₂ := B₂) (f := w)
    rw [hUnion] at hsum
    have ht := sum_add_sum_compl (insert b Z) w
    omega
  have hCl₁ : Close A B₁ (Z.card+1) := by
    have hsub : B₁\A ⊆ T := by
      intro x hx
      rcases mem_union.mp (mem_sdiff.mp hx).1 with h | h
      · exact False.elim ((mem_sdiff.mp hx).2 (mem_sdiff.mp h).1)
      · exact h
    have hn : (B₁\A).card ≤ Z.card+1 := by
      have hh := card_le_card hsub
      rw [hTcard] at hh
      omega
    exact ⟨by rw [difference_card_eq A B₁ (hA.trans hB₁.symm)];exact hn,hn⟩
  have hCl₂ : Close Aᶜ B₂ (Z.card+1) := by
    have hsub : B₂\Aᶜ ⊆ insert a P := by
      intro x hx
      rcases mem_union.mp (mem_sdiff.mp hx).1 with h | h
      · exact False.elim ((mem_sdiff.mp hx).2 (mem_sdiff.mp h).1)
      · exact h
    have hn : (B₂\Aᶜ).card ≤ Z.card+1 := by
      have hh := card_le_card hsub
      rw [card_insert_of_notMem haP,hPcard] at hh
      omega
    exact ⟨by rw [difference_card_eq Aᶜ B₂ (hAc.trans hB₂.symm)];exact hn,hn⟩
  have hTotal := card_add_card_compl A
  by_cases hHalf : 2*(∑ x ∈ B₁, w x) ≤ ∑ x, w x
  · refine ⟨B₁,hB₁,?_,hB₁a,hB₁b,hB₁Z,?_,Or.inl hCl₁⟩
    · simp only [card_compl];omega
    · have hs := sum_add_sum_compl B₁ w;omega
  · refine ⟨B₂,hB₂,?_,hB₂a,hB₂b,hB₂Z,?_,Or.inr hCl₂⟩
    · simp only [card_compl];omega
    · have hs := sum_add_sum_compl B₂ w;omega

end OverfullWork.HeavyNeighbourCutRepair
