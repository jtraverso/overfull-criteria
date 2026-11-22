module

public import OverfullWork.KuhnOsthusPreprocessingAssembly
public import OverfullWork.HamiltonResidueAssembly
public import OverfullWork.KuhnOsthusLemma105
public import OverfullWork.KuhnOsthusWalkBlowup
public import OverfullWork.OsthusStadenH1Profile

@[expose] public section


/-! The physical degree formula (10.1) for the parity reserve. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {V Z : Type*} [Fintype V] [Fintype Z]

/-- Restricting the graph to ordinary vertices only decreases each
semidegree at an ordinary vertex. -/
theorem ordinaryCycleHost_semidegrees_le (D : Digraph (V ⊕ Z)) (v : V) :
    inDegree (ordinaryCycleHost D) v ≤ inDegree D (.inl v) ∧
    outDegree (ordinaryCycleHost D) v ≤ outDegree D (.inl v) := by
  let e : V ↪ V ⊕ Z := ⟨Sum.inl,Sum.inl_injective⟩
  constructor
  · change pairSemidegree false (pullDirectedPair e e D) v ≤ _
    rw [pullDirectedPair_semidegree]
    exact card_le_card (filter_subset_filter _ (subset_univ _))
  · change pairSemidegree true (pullDirectedPair e e D) v ≤ _
    rw [pullDirectedPair_semidegree]
    exact card_le_card (filter_subset_filter _ (subset_univ _))

/-- A perfect matching in each successor pair gives a single winding
permutation supported in the same physical digraph. -/
theorem exists_winding_permutation_of_superregular_pairs {k : ℕ}
    (D : Digraph V) (X : Fin k → Finset V) (m r : ℕ) (ε d : ℝ)
    (hCover : ∀ x, ∃ i, x ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = m)
    (hr : 0 < r) (hGap : 2*ε < d)
    (hCut : (m:ℝ)*ε ≤ (r:ℝ)) (hDegree : (r:ℝ) ≤ (d-ε)*(m:ℝ))
    (hPairs : ∀ i, IsLowerSuperregularPair D ε d (X i) (X (finRotate k i))) :
    ∃ σ : Equiv.Perm V, (∀ i x, x ∈ X i → σ x ∈ X (finRotate k i)) ∧
      ∀ x, D.Adj x (σ x) := by
  have hMatch (i : Fin k) : ∃ f : X i ≃ X (finRotate k i), ∀ a : X i, D.Adj a (f a) := by
    obtain ⟨d',hd',_,hPair⟩ := hPairs i
    apply IsSuperregularPair.exists_perfect_matching D _ _ d' ε r (hGap.trans_le hd') hr
    · rw [hSize,hSize]
    · rwa [hSize]
    · rw [hSize]
      exact hDegree.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hd' _) (Nat.cast_nonneg _))
    · exact hPair
  choose f hf using hMatch
  let M (i : Fin k) (_ : Fin 1) := f i
  let B := successorCellMatchingUnion X (finRotate k) M
  have hReg x : inDegree B x = 1 ∧ outDegree B x = 1 := by
    obtain ⟨i,hi⟩ := hCover x
    exact successor_cell_matching_union_degrees X _ M hDis
      (fun _ b c h _ => (h (Subsingleton.elim b c)).elim) i ⟨x,hi⟩
  obtain ⟨F,hF,_⟩ := exists_permutation_factorization_of_regular B 1 hReg
  have hB (x : V) : B.Adj x (F 0 x) := by
    rw [←hF]
    exact ⟨0,rfl⟩
  refine ⟨F 0,?_,?_⟩
  · intro i x hi
    obtain ⟨j,b,a,rfl,hy⟩ := hB x
    have he : j = i := by
      by_contra hn
      exact Finset.disjoint_left.mp (hDis j i hn) a.prop hi
    subst j
    exact hy ▸ (M i b a).prop
  · intro x
    obtain ⟨i,_,a,rfl,hy⟩ := hB x
    exact hy ▸ hf i a

/-- Applying the original parity absorber to a disjoint winding
permutation determines its degrees on ordinary and exceptional vertices. -/
theorem AbsorbsWindingFactor.exact_semidegrees {k : ℕ} {X : Fin k → Finset V}
    {P : Digraph (V ⊕ Z)} {E : Fin 7 → Digraph (V ⊕ Z)}
    (hP : AbsorbsWindingFactor X P E) (σ : Equiv.Perm V)
    (hWind : ∀ i x, x ∈ X i → σ x ∈ X (finRotate k i))
    (hDis : Disjoint (liftOrdinaryCycleArcs Z ⟨fun x y => σ x = y⟩) P) (v : V ⊕ Z) :
    let d := match v with | .inl _ => 6 | .inr _ => 7
    inDegree P v = d ∧ outDegree P v = d := by
  let O : Digraph V := matchingUnion (fun _ : Fin 1 => σ)
  let R := liftOrdinaryCycleArcs Z O
  have hO : O = ⟨fun x y => σ x = y⟩ := by
    ext x y
    exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨0,h⟩⟩
  have hLift : R = liftDirectedPair (⟨Sum.inl,Sum.inl_injective⟩ : V ↪ V ⊕ Z)
      ⟨Sum.inl,Sum.inl_injective⟩ O := by
    ext x y
    cases x <;> cases y <;> simp [R,liftOrdinaryCycleArcs,liftDirectedPair]
  obtain ⟨F,hF,hApart,_,_⟩ := hP σ hWind hDis
  have hApart' : Disjoint R P := by simpa only [R,hO] using hDis
  have hUnion : matchingUnion F = R ⊔ P := by simpa only [R,hO] using hF
  obtain ⟨hI,hO'⟩ := matchingUnion_exact_semidegrees F hApart v
  rw [hUnion] at hI hO'
  obtain ⟨hout,hin⟩ := degrees_sup_of_disjoint R P (disjoint_iff_inf_le.mp hApart') v
  rw [hin] at hI
  rw [hout] at hO'
  cases v with
  | inl x =>
    obtain ⟨hvi,hvo⟩ := matchingUnion_exact_semidegrees (fun _ : Fin 1 => σ)
      (fun a b h _ => (h (Subsingleton.elim a b)).elim) x
    have hRi : inDegree R (.inl x) = 1 := by
      rw [hLift]
      exact (lift_pair_semidegree ⟨Sum.inl,Sum.inl_injective⟩ ⟨Sum.inl,Sum.inl_injective⟩
        O false x).trans hvi
    have hRo : outDegree R (.inl x) = 1 := by
      rw [hLift]
      exact (lift_pair_semidegree ⟨Sum.inl,Sum.inl_injective⟩ ⟨Sum.inl,Sum.inl_injective⟩
        O true x).trans hvo
    change inDegree P (.inl x) = 6 ∧ outDegree P (.inl x) = 6
    omega
  | inr x =>
    have hRi : inDegree R (.inr x) = 0 := by
      rw [inDegree,inNeighbours,card_eq_zero,filter_eq_empty_iff]
      rintro (a | z) _ h <;> exact h
    have hRo : outDegree R (.inr x) = 0 := by
      rw [outDegree,card_eq_zero,filter_eq_empty_iff]
      rintro (a | z) _ h <;> exact h
    change inDegree P (.inr x) = 7 ∧ outDegree P (.inr x) = 7
    omega

/-- The successor pairs in the ordinary complement yield the
degree of every physical block simultaneously. Since the blocks
have disjoint arcs, their union has degrees (10.1). -/
theorem parity_reserve_semidegrees_of_residual_pairs {k n : ℕ}
    (X : Fin k → Finset V) (D : Digraph V) (P : Fin n → Digraph (V ⊕ Z))
    (E : Fin n → Fin 7 → Digraph (V ⊕ Z))
    (m r : ℕ) (ε d : ℝ) (hCover : ∀ x, ∃ i, x ∈ X i)
    (hCells : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = m)
    (hr : 0 < r) (hGap : 2*ε < d)
    (hCut : (m:ℝ)*ε ≤ (r:ℝ)) (hDegree : (r:ℝ) ≤ (d-ε)*(m:ℝ))
    (hPairs : ∀ i, IsLowerSuperregularPair (D \ ordinaryCycleHost (⨆ a, P a))
      ε d (X i) (X (finRotate k i)))
    (hP : ∀ a, AbsorbsWindingFactor X (P a) (E a))
    (hDis : Pairwise fun a b => Disjoint (P a) (P b))
    (v : V ⊕ Z) :
    let d := match v with | .inl _ => 6*n | .inr _ => 7*n
    inDegree (⨆ a, P a) v = d ∧ outDegree (⨆ a, P a) v = d := by
  obtain ⟨σ,hWind,hσ⟩ := exists_winding_permutation_of_superregular_pairs _ X m r ε d
    hCover hCells hSize hr hGap hCut hDegree hPairs
  have hApart (a : Fin n) : Disjoint (liftOrdinaryCycleArcs Z ⟨fun x y => σ x = y⟩) (P a) := by
    rw [disjoint_iff_inf_le]
    rintro (x | x) (y | y) ⟨hxy,h⟩
    · change σ x = y at hxy
      subst y
      exact (hσ x).2 (Digraph.iSup_adj.mpr ⟨a,h⟩)
    · exact hxy
    · exact hxy
    · exact hxy
  have hDeg (a : Fin n) := AbsorbsWindingFactor.exact_semidegrees (hP a) σ hWind (hApart a) v
  have he : (⨆ a, P a) = indexedArcUnion univ P := by
    ext x y
    simp [Digraph.iSup_adj,indexedArcUnion]
  rw [he]
  obtain ⟨ho,hi⟩ := indexedArcUnion_semidegrees univ P (fun a _ b _ h => hDis h) v
  rw [hi,ho]
  cases v <;> simp only [(hDeg _).1,(hDeg _).2,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,Nat.mul_comm,and_self]

/-- The same six-matchings-per-block budget of Lemma 10.5 also
pays for the winding factor used to read the exact degrees. -/
theorem parity_reserve_semidegrees_of_matching_budget {k n m : ℕ}
    (X : Fin k → Finset V) (D : Digraph V) (P : Fin n → Digraph (V ⊕ Z))
    (E : Fin n → Fin 7 → Digraph (V ⊕ Z))
    (r : ℕ) (ε η d a : ℝ) (hCover : ∀ x, ∃ i, x ∈ X i)
    (hCells : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hm : 0 < m) (hSize : ∀ i, (X i).card = 2*m)
    (hr : 0 < r) (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a) (hGap : 2*η < d)
    (hCut : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ)) (hDegree : (r:ℝ) ≤ (d-η)*((2*m:ℕ):ℝ))
    (hTol : 2*(ε+a) ≤ η) (hBudget : ((n*6:ℕ):ℝ) ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPairs : ∀ i, IsLowerSuperregularPair D ε d (X i) (X (finRotate k i)))
    (hM : ∀ j, ∃ M : Fin 6 → Equiv.Perm V, ordinaryCycleHost (P j) ≤ matchingUnion M)
    (hP : ∀ j, AbsorbsWindingFactor X (P j) (E j))
    (hDis : Pairwise fun j l => Disjoint (P j) (P l))
    (v : V ⊕ Z) :
    let d := match v with | .inl _ => 6*n | .inr _ => 7*n
    inDegree (⨆ j, P j) v = d ∧ outDegree (⨆ j, P j) v = d := by
  choose F hF using hM
  let index : Fin n × Fin 6 ≃ Fin (n*6) := finProdFinEquiv
  let M (p : Fin (n*6)) := F (index.symm p).1 (index.symm p).2
  have hLe : ordinaryCycleHost (⨆ j, P j) ≤ matchingUnion M := by
    intro x y h
    obtain ⟨j,hj⟩ := Digraph.iSup_adj.mp h
    obtain ⟨i,hi⟩ := hF j hj
    exact ⟨index (j,i),by simpa only [M,Equiv.symm_apply_apply] using hi⟩
  apply parity_reserve_semidegrees_of_residual_pairs X D P E (2*m) r η d
    hCover hCells hSize hr hGap hCut hDegree _ hP hDis v
  intro i
  exact residual_pairs_after_matchings M hLe _ _ hm (hSize i) (hSize _) ε η d a
    hη hη₁ ha (by linarith) hTol hBudget (hPairs i)

end OverfullWork.DirectedRobustExpansion
