module

public import OverfullWork.KuhnOsthusSparseSuccessorPairs
public import OverfullWork.KuhnOsthusChordCandidates
public import OverfullWork.OsthusStadenNestedRefinement

@[expose] public section


/-! The style split and the restriction of successor pairs in
Kühn–Osthus Lemma 8.3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset UniformSubsetSampling
open scoped Classical

/-- Choose 24 chord styles and preserve 21 untouched styles after
accounting for the at most five styles of the basic paths. -/
theorem exists_extender_style_allocation (J : Finset (Fin 50)) (hJ : J.card ≤ 5) :
    ∃ A B : Finset (Fin 50), A.card = 24 ∧ B.card = 21 ∧
      Disjoint J A ∧ Disjoint J B ∧ Disjoint A B := by
  classical
  have hFree (L : Finset (Fin 50)) : (univ \ L).card = 50-L.card := by
    rw [card_sdiff_of_subset (subset_univ L)]
    simp
  obtain ⟨A,hA,h24⟩ := exists_subset_card_eq
    (show 24 ≤ (univ \ J).card by rw [hFree]; omega)
  have hLeft := card_union_le J A
  obtain ⟨B,hB,h21⟩ := exists_subset_card_eq
    (show 21 ≤ (univ \ (J ∪ A)).card by rw [hFree]; omega)
  refine ⟨A,B,h24,h21,?_,?_,?_⟩
  · exact disjoint_left.mpr fun _ hx hy => (mem_sdiff.mp (hA hy)).2 hx
  · exact disjoint_left.mpr fun _ hx hy => (mem_sdiff.mp (hB hy)).2 (mem_union_left _ hx)
  · exact disjoint_left.mpr fun _ hx hy => (mem_sdiff.mp (hB hy)).2 (mem_union_right _ hx)

/-- The union of any selected styles of a uniform refinement has
exactly the sum of their sizes. -/
theorem UniformRefinementOf.card_style_union {V J : Type*} {profiles : J → Finset V}
    {P : Finset V} {u : ℕ} {δ : ℝ}
    (R : UniformRefinementOf (I := Fin 50) profiles P u δ) (B : Finset (Fin 50)) :
    (B.biUnion R.cells).card = B.card*u := by
  rw [card_biUnion (fun i _ j _ hij => R.disjoint i j hij)]
  simp [R.size]

/-- Uniform refinement keeps a third of each sufficiently large
neighbourhood inside any 21 of the 50 styles. -/
theorem UniformRefinementOf.one_third_in_untouched_styles {V J : Type*}
    {profiles : J → Finset V} {P : Finset V} {u : ℕ} {δ : ℝ}
    (R : UniformRefinementOf (I := Fin 50) profiles P u δ)
    (B : Finset (Fin 50)) (hB : B.card = 21) (hδ : δ ≤ 1/5)
    (j : J) (hj : δ*(P.card:ℝ) ≤ profileCount P (profiles j)) :
    profileCount P (profiles j)/3 ≤ profileCount (B.biUnion R.cells) (profiles j) := by
  classical
  have hCount : profileCount (B.biUnion R.cells) (profiles j) =
      ∑ i ∈ B, profileCount (R.cells i) (profiles j) := by
    have he : (B.biUnion R.cells) ∩ profiles j = B.biUnion (fun i => R.cells i ∩ profiles j) := by
      ext x
      simp only [mem_inter,mem_biUnion]
      exact ⟨fun ⟨⟨i,hi,hx⟩,hp⟩ => ⟨i,hi,hx,hp⟩,
        fun ⟨i,hi,hx,hp⟩ => ⟨⟨i,hi,hx⟩,hp⟩⟩
    unfold profileCount
    rw [he,card_biUnion (fun i _ k _ hik =>
      (R.disjoint i k hik).mono inter_subset_left inter_subset_left),Nat.cast_sum]
  rw [hCount]
  let n := profileCount P (profiles j)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hCells (i : Fin 50) : (4/5:ℝ)*(n/50) ≤ profileCount (R.cells i) (profiles j) := by
    have h := (abs_le.mp (R.uniform i j hj)).1
    simp only [Fintype.card_fin,Nat.cast_ofNat] at h
    have hδn := mul_le_mul_of_nonneg_right hδ (div_nonneg hn (by norm_num : (0:ℝ) ≤ 50))
    linarith only [h,hδn]
  calc
    n/3 ≤ 21*((4/5:ℝ)*(n/50)) := by linarith only [hn]
    _ = ∑ _i ∈ B, (4/5:ℝ)*(n/50) := by simp [hB,nsmul_eq_mul]
    _ ≤ _ := sum_le_sum fun i _ => hCells i

/-- Restrict a successor pair to the unused sources and targets.
Losing at most two thirds of the labels changes the rectangle
threshold and codegree parameter by a factor of three. -/
theorem sparse_successor_restriction {V : Type*} [Fintype V]
    (D : Digraph V) (S T : Finset V) (e : S ≃ T) (d ε μ ζ : ℝ)
    (hd : 0 ≤ d) (hε : 0 ≤ ε) (hμ : 0 < μ) (hζ : 0 ≤ ζ)
    (h : SparseSuccessorPairBounds D d ε μ ζ)
    (hSize : (Fintype.card V:ℝ) ≤ 3*(S.card:ℝ))
    (hIn : ∀ y ∈ T, (ζ/3)*d*(Fintype.card V:ℝ) ≤ (inNeighbours D S y:ℝ))
    (hOut : ∀ x ∈ S, (ζ/3)*d*(Fintype.card V:ℝ) ≤ (outTo D T x:ℝ)) :
    SparseSuccessorPairBounds (pairOnSources D S T e) d (3*ε) (μ/3) (ζ/3) := by
  classical
  have hS : (S.card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ S
  have hMin := mul_le_mul_of_nonneg_left hS (mul_nonneg (by positivity : 0 ≤ ζ/3) hd)
  have hCodeg : (d/μ)^2*(Fintype.card V:ℝ) ≤ (d/(μ/3))^2*(S.card:ℝ) := by
    have heq : d/(μ/3) = 3*(d/μ) := by field_simp
    rw [heq]
    have hScale := mul_le_mul_of_nonneg_left hSize (sq_nonneg (d/μ))
    have hPos := mul_nonneg (sq_nonneg (d/μ)) (Nat.cast_nonneg S.card : (0:ℝ) ≤ S.card)
    nlinarith only [hScale,hPos]
  have hCut : ε*(Fintype.card V:ℝ) ≤ 3*ε*(S.card:ℝ) := by
    calc
      _ ≤ ε*(3*(S.card:ℝ)) := mul_le_mul_of_nonneg_left hSize hε
      _ = _ := by ring
  apply sparse_pair_bounds_of_physical D S T e d (3*ε) (μ/3) (ζ/3)
  · exact fun y hy => hMin.trans (hIn y hy)
  · exact fun x hx => hMin.trans (hOut x hx)
  · intro x _ y _ hxy
    refine (Nat.cast_le.mpr (card_le_card (fun u hu => ?_))).trans
      ((h.in_codegree x y hxy).trans hCodeg)
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩
  · intro x _ y _ hxy
    refine (Nat.cast_le.mpr (card_le_card (fun u hu => ?_))).trans
      ((h.out_codegree x y hxy).trans hCodeg)
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩
  · intro X _ Y _ hx hy
    have hScale : (1-3*ε)*d ≤ (1-ε)*d := mul_le_mul_of_nonneg_right (by linarith) hd
    have hXY := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg X.card)) (Nat.cast_nonneg Y.card)
    exact hXY.trans (h.rectangle X Y (hCut.trans hx) (hCut.trans hy))

/-- The unused source and target sets contain all 21 untouched
styles. Apply the regularity estimates on these actual remaining sets. -/
theorem sparse_successor_restriction_of_untouched_styles {V : Type*} [Fintype V]
    (D : Digraph V) (S T : Finset V) (e : S ≃ T) (d ε μ ζ δ : ℝ)
    (hd : 0 ≤ d) (hε : 0 ≤ ε) (hμ : 0 < μ) (hζ : 0 ≤ ζ)
    (hδ : δ ≤ 1/5) (hThresh : δ ≤ ζ*d)
    (h : SparseSuccessorPairBounds D d ε μ ζ) (u : ℕ)
    (R : UniformRefinementOf (I := Fin 50)
      (fun j : V ⊕ V => j.elim
        (fun y => univ.filter (fun x => D.Adj x y))
        (fun x => univ.filter (D.Adj x))) univ u δ)
    (B : Finset (Fin 50)) (hB : B.card = 21)
    (hS : B.biUnion R.cells ⊆ S) (hT : B.biUnion R.cells ⊆ T) :
    SparseSuccessorPairBounds (pairOnSources D S T e) d (3*ε) (μ/3) (ζ/3) := by
  classical
  have hm : Fintype.card V = 50*u := by
    simpa only [card_univ,Fintype.card_fin] using R.card_parent
  have hP : (B.biUnion R.cells).card = 21*u := by
    rw [R.card_style_union,hB]
  have hSize : (Fintype.card V:ℝ) ≤ 3*(S.card:ℝ) := by
    have hPS := card_le_card hS
    rw [hP] at hPS
    exact_mod_cast (show Fintype.card V ≤ 3*S.card by rw [hm]; omega)
  have hProfile (A : Finset V) (p : V → Prop) :
      profileCount A (univ.filter p) = ((A.filter p).card:ℝ) := by
    unfold profileCount
    congr 2
    ext x
    simp
  have hLower (P : Finset V) (j : V ⊕ V) (hPool : B.biUnion R.cells ⊆ P)
      (hD : ζ*d*(Fintype.card V:ℝ) ≤ profileCount univ
        (j.elim (fun y => univ.filter (fun x => D.Adj x y)) (fun x => univ.filter (D.Adj x)))) :
      (ζ/3)*d*(Fintype.card V:ℝ) ≤ profileCount P
        (j.elim (fun y => univ.filter (fun x => D.Adj x y)) (fun x => univ.filter (D.Adj x))) := by
    have hTwice := R.one_third_in_untouched_styles B hB hδ j
      (by simpa only [card_univ] using
        (mul_le_mul_of_nonneg_right hThresh (Nat.cast_nonneg (Fintype.card V))).trans hD)
    have hMon : ∀ Q : Finset V, profileCount (B.biUnion R.cells) Q ≤ profileCount P Q := by
      intro Q
      unfold profileCount
      exact_mod_cast card_le_card (inter_subset_inter hPool (Subset.refl Q))
    calc
      _ = (ζ*d*(Fintype.card V:ℝ))/3 := by ring
      _ ≤ _ := ((div_le_div_of_nonneg_right hD (by norm_num : (0:ℝ) ≤ 3)).trans hTwice).trans (hMon _)
  apply sparse_successor_restriction D S T e d ε μ ζ hd hε hμ hζ h hSize
  · intro y _
    have hy : ζ*d*(Fintype.card V:ℝ) ≤ profileCount univ
        (univ.filter (fun x => D.Adj x y)) := by
      rw [hProfile]
      exact h.in_degree y
    have hh := hLower S (Sum.inl y) hS hy
    rw [Sum.elim_inl,hProfile] at hh
    exact hh
  · intro x _
    have hx : ζ*d*(Fintype.card V:ℝ) ≤ profileCount univ (univ.filter (D.Adj x)) := by
      rw [hProfile]
      exact h.out_degree x
    have hh := hLower T (Sum.inr x) hT hx
    rw [Sum.elim_inr,hProfile] at hh
    exact hh

/-- The 24 chord styles leave a candidate matching of size at
least (23m/50), as in the proof of Lemma 8.3. -/
theorem exists_chord_candidate_on_styles {V J : Type*} [Fintype V]
    (D : Digraph V) (profiles : J → Finset V) (U W : Finset V)
    (u e : ℕ) (δ d ε : ℝ)
    (L : UniformRefinementOf (I := Fin 50) profiles U u δ)
    (R : UniformRefinementOf (I := Fin 50) profiles W u δ)
    (A : Finset (Fin 50)) (hA : A.card = 24)
    (hUW : Disjoint U W) (he : e ≤ u) (hd : 0 < d) (hε : ε < 1)
    (hCut : ε*(50*(u:ℝ)) ≤ (e:ℝ)+1)
    (hRelative : ∀ X ⊆ U, ∀ Y ⊆ W,
      ε*(U.card:ℝ) ≤ X.card → ε*(W.card:ℝ) ≤ Y.card →
      (1-ε)*d ≤ DirectedRegularPairs.density D X Y) :
    ∃ M : Finset (V × V), 23*(50*u) ≤ 50*M.card ∧
      (∀ z ∈ M, z.1 ∈ A.biUnion L.cells ∧ z.2 ∈ A.biUnion R.cells ∧
        D.Adj z.1 z.2 ∧ z.1 ≠ z.2) ∧
      Set.InjOn Prod.fst (↑M : Set (V × V)) ∧ Set.InjOn Prod.snd (↑M : Set (V × V)) := by
  have hS (P : Finset V) (B : UniformRefinementOf (I := Fin 50) profiles P u δ) :
      A.biUnion B.cells ⊆ P := by
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    exact B.subset i hi
  apply exists_chord_candidate_matching D _ _ (50*u) e
  · rw [L.card_style_union,R.card_style_union]
  · rw [L.card_style_union,hA]
    omega
  · omega
  · exact hUW.mono (hS U L) (hS W R)
  · apply chord_rectangles_of_relative_density D U W _ _ d ε e hd hε (hS U L) (hS W R)
    · simpa only [L.card_parent,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using hCut
    · simpa only [R.card_parent,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using hCut
    · exact hRelative

end OverfullWork.DirectedRobustExpansion
