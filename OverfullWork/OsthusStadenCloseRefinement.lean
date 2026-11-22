module

public import OverfullWork.OsthusStadenUniformRefinement

@[expose] public section


/-! The exact-size redistribution step in Osthus–Staden Lemma 3.12.
Disjoint retained cores are kept and only the remaining vertices are assigned. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset UniformSubsetSampling
open scoped Classical

/-- Complete disjoint cores inside a cluster to a partition into cells
of size `m`, keeping each core in its own cell. -/
theorem exists_refinement_preserving_cores {V I : Type*} [Fintype I]
    (U : Finset V) (K : I → Finset V) (m : ℕ)
    (hSize : U.card = Fintype.card I*m)
    (hSub : ∀ i, K i ⊆ U) (hCard : ∀ i, (K i).card ≤ m)
    (hDis : ∀ i j, i ≠ j → Disjoint (K i) (K j)) :
    ∃ cells : I → Finset V,
      (∀ i, K i ⊆ cells i ∧ (cells i).card = m) ∧
      (∀ i j, i ≠ j → Disjoint (cells i) (cells j)) ∧
      univ.biUnion cells = U := by
  classical
  let S := univ.biUnion K
  let R := U \ S
  have hSU : S ⊆ U := by
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    exact hSub i hi
  have hS : S.card = ∑ i, (K i).card := by
    exact card_biUnion (fun i _ j _ hij => hDis i j hij)
  let deficit := fun i => m-(K i).card
  have hSum : (∑ i, deficit i) = Fintype.card {x // x ∈ R} := by
    have hBalance : (∑ i, deficit i) + ∑ i, (K i).card = U.card := by
      rw [← sum_add_distrib, hSize]
      simp only [deficit, Nat.sub_add_cancel (hCard _),sum_const, card_univ,Nat.nsmul_eq_mul]
    rw [Fintype.card_coe,card_sdiff_of_subset hSU,hS]
    omega
  have hBad : (∑ i, probability (deficit i) (fun _ : Finset {x // x ∈ R} => False)) < 1 := by
    simp [probability]
  obtain ⟨rank,hRank⟩ := exists_partition_avoiding deficit hSum
    (fun _ _ => False) hBad
  let E (i : I) := (slice rank i).map (Function.Embedding.subtype (· ∈ R))
  have hE : ∀ i x, x ∈ E i ↔ ∃ hx : x ∈ R, rank ⟨x,hx⟩ = i := by
    intro i x
    simp only [E,mem_map,mem_slice,Function.Embedding.subtype_apply,Subtype.exists]
    constructor
    · rintro ⟨y,hy,hy',rfl⟩
      exact ⟨hy,hy'⟩
    · rintro ⟨hx,hx'⟩
      exact ⟨x,hx,hx',rfl⟩
  have hKE (i j : I) : Disjoint (K i) (E j) := by
    rw [disjoint_left]
    intro x hx hy
    obtain ⟨hy,_⟩ := (hE j x).mp hy
    exact (mem_sdiff.mp hy).2 (mem_biUnion.mpr ⟨i,mem_univ _,hx⟩)
  refine ⟨fun i => K i ∪ E i,?_,?_,?_⟩
  · intro i
    refine ⟨subset_union_left,?_⟩
    rw [card_union_of_disjoint (hKE i i),show (E i).card = deficit i by
      exact (card_map _).trans (hRank i).1]
    exact Nat.add_sub_of_le (hCard i)
  · intro i j hij
    rw [disjoint_union_left,disjoint_union_right,disjoint_union_right]
    refine ⟨⟨hDis i j hij,hKE i j⟩,⟨(hKE j i).symm,?_⟩⟩
    rw [disjoint_left]
    intro x hx hy
    obtain ⟨hr,hi⟩ := (hE i x).mp hx
    obtain ⟨_,hj⟩ := (hE j x).mp hy
    exact hij (hi.symm.trans hj)
  · ext x
    constructor
    · intro hx
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
      rcases mem_union.mp hi with h | h
      · exact hSub i h
      · exact (mem_sdiff.mp ((hE _ _).mp h).choose).1
    · intro hx
      by_cases h : x ∈ S
      · obtain ⟨i,hi,hi'⟩ := mem_biUnion.mp h
        exact mem_biUnion.mpr ⟨i,hi,mem_union_left _ hi'⟩
      · have hr : x ∈ R := mem_sdiff.mpr ⟨hx,h⟩
        exact mem_biUnion.mpr ⟨rank ⟨x,hr⟩,mem_univ _,mem_union_right _ ((hE _ _).mpr ⟨hr,rfl⟩)⟩

/-- If the aligned old cells each overlap the new cluster in at least
`m−d` vertices, its refinement has overlap at least `m−d` in each cell. -/
theorem exists_close_refinement {V I : Type*} [Fintype I]
    (U : Finset V) (old : I → Finset V) (m d : ℕ)
    (hSize : U.card = Fintype.card I*m)
    (hOverlap : ∀ i, m-d ≤ (old i ∩ U).card)
    (hDis : ∀ i j, i ≠ j → Disjoint (old i) (old j)) :
    ∃ cells : I → Finset V,
      (∀ i, (cells i).card = m ∧ m-d ≤ (cells i ∩ old i).card) ∧
      (∀ i j, i ≠ j → Disjoint (cells i) (cells j)) ∧
      univ.biUnion cells = U := by
  choose K hK hCard using fun i => exists_subset_card_eq (hOverlap i)
  obtain ⟨cells,hCells,hCellsDis,hUnion⟩ := exists_refinement_preserving_cores U K m hSize
    (fun i => (hK i).trans inter_subset_right) (fun i => (hCard i).le.trans (Nat.sub_le _ _))
    (fun i j h => (hDis i j h).mono ((hK i).trans inter_subset_left) ((hK j).trans inter_subset_left))
  refine ⟨cells,fun i => ⟨(hCells i).2,?_⟩,hCellsDis,hUnion⟩
  rw [← hCard i]
  exact card_le_card (subset_inter (hCells i).1 ((hK i).trans inter_subset_left))

/-- A profile count changes by at most the larger of the losses on
the two sides when a cell is replaced by an aligned cell. -/
theorem profile_count_dist_le {V : Type*} (A B Q : Finset V) :
    |((A ∩ Q).card : ℝ) - (B ∩ Q).card| ≤
      (max (A \ B).card (B \ A).card : ℕ) := by
  have hBound (X Y : Finset V) : (X ∩ Q).card ≤ (Y ∩ Q).card + (X \ Y).card := by
    have hSub : (X ∩ Q) \ (Y ∩ Q) ⊆ X \ Y := by
      intro x hx
      simp only [mem_sdiff,mem_inter] at hx ⊢
      exact ⟨hx.1.1, fun hy => hx.2 ⟨hy,hx.1.2⟩⟩
    have h₁ := card_le_card_sdiff_add_card (s := X ∩ Q) (t := Y ∩ Q)
    have h₂ := card_le_card hSub
    omega
  have hAB : (A ∩ Q).card ≤ (B ∩ Q).card + max (A \ B).card (B \ A).card :=
    (hBound A B).trans (Nat.add_le_add_left (le_max_left _ _) _)
  have hBA : (B ∩ Q).card ≤ (A ∩ Q).card + max (A \ B).card (B \ A).card :=
    (hBound B A).trans (Nat.add_le_add_left (le_max_right _ _) _)
  rw [abs_le]
  constructor
  · exact neg_le_sub_iff_le_add.mpr (by exact_mod_cast hBA)
  · exact sub_le_iff_le_add.mpr (by
      rw [add_comm]; exact_mod_cast hAB)

end OverfullWork.DirectedRobustExpansion
