module

public import OverfullWork.NearTightOddSetGeometry
public import Mathlib.Analysis.Real.Sqrt
public import OverfullWork.LowSetEdgePreprocessing

@[expose] public section

/-! Counting preliminaries for Kühn–Lo–Osthus–Staden, Lemmas 4.1–4.2.
All sets are finite vertex sets in the ambient simple graph. -/
namespace OverfullWork.KLOS

open SimpleGraph Finset PrunedCore RobustExpansion OddCutDeficit
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Adjacency incidences directed from `S` into `T`. An edge inside `S ∩ T`
contributes twice. This is the paper's `e′(S,T)`. -/
def incidences (S T : Finset V) : ℕ := ∑ x ∈ T, neighboursIn G S x

theorem incidences_comm (S T : Finset V) : incidences G S T = incidences G T S := by
  simp only [incidences, neighboursIn_eq_filter_card, card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  simp only [G.adj_comm]

theorem incidences_mono {S S' T T' : Finset V} (hS : S ⊆ S') (hT : T ⊆ T') :
    incidences G S T ≤ incidences G S' T' := by
  unfold incidences
  exact (sum_le_sum (fun x _ => neighboursIn_mono G hS x)).trans
    (sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => Nat.zero_le _))

theorem incidences_union_right (S T W : Finset V) (hDisjoint : Disjoint T W) :
    incidences G S (T ∪ W) = incidences G S T + incidences G S W := by
  exact sum_union hDisjoint

theorem incidences_add_compl (S T : Finset V) :
    incidences G S T + incidences G S Tᶜ = ∑ x ∈ S, G.degree x := by
  unfold incidences
  rw [sum_add_sum_compl, sum_neighboursIn_eq_sum_degrees]

theorem incidences_compl_self (S : Finset V) : incidences G S Sᶜ = cutEdges G S := by
  symm
  apply MaximumOddCutPacking.cut_eq_sum_neighboursIn G S Sᶜ disjoint_compl_right
  intro _ _ y _
  by_cases hy : y ∈ S
  · exact Or.inl hy
  · exact Or.inr (mem_compl.mpr hy)

theorem incidences_self (S : Finset V) : incidences G S S = 2 * internalEdges G S := by
  have h := incidences_add_compl G S S
  rw [incidences_compl_self] at h
  have hCut := internal_cut_identity G S
  omega

theorem incidences_le_card_mul (S T : Finset V) : incidences G S T ≤ S.card * T.card := by
  calc
    _ ≤ ∑ _ ∈ T, S.card := sum_le_sum (fun v _ => neighboursIn_le_card G S v)
    _ = _ := by simp [Nat.mul_comm]

/-- The size and boundary conditions for a `ρ`-component. -/
def IsSparseComponent (ρ : ℝ) (U : Finset V) : Prop :=
  Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (U.card : ℝ) ∧
    (cutEdges G U : ℝ) ≤ ρ * (Fintype.card V : ℝ) ^ 2

/-- Conditions (C1)–(C3), with the boundary expressed using disjoint edge
sets. The whole component is `A ∪ B`. -/
def CloseToBipartite (ρ : ℝ) (A B : Finset V) : Prop :=
  Disjoint A B ∧ Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (A.card : ℝ) ∧
    Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (B.card : ℝ) ∧
    |(A.card : ℝ) - (B.card : ℝ)| ≤ ρ * (Fintype.card V : ℝ) ∧
    (internalEdges G A : ℝ) + internalEdges G B + cutEdges G (A ∪ B) ≤
      ρ * (Fintype.card V : ℝ) ^ 2

private theorem minDegree_mul_card_le_sum (S : Finset V) :
    G.minDegree * S.card ≤ ∑ x ∈ S, G.degree x := by
  rw [← sum_neighboursIn_eq_sum_degrees]
  exact minDegree_mul_card_le_sum_neighboursIn G S

omit [DecidableEq V] in
private theorem sqrt_budget_le_card (ρ : ℝ) (hρ : 0 ≤ ρ) {s : ℝ}
    (hs : Real.sqrt ρ * (Fintype.card V : ℝ) ≤ s) :
    ρ * (Fintype.card V : ℝ) ^ 2 ≤ Real.sqrt ρ * (Fintype.card V : ℝ) * s := by
  have h := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (Real.sqrt_nonneg ρ) (Nat.cast_nonneg (Fintype.card V)))
  calc
    _ = (Real.sqrt ρ * (Fintype.card V : ℝ)) * (Real.sqrt ρ * (Fintype.card V : ℝ)) := by
      rw [← pow_two, mul_pow, Real.sq_sqrt hρ]
    _ ≤ _ := h

/-- Lemma 4.1(i), with a minimum-degree lower bound in place of regularity. -/
theorem sparseComponent_card_lower (ρ : ℝ) (U : Finset V) (hρ : 0 < ρ)
    (hn : 0 < Fintype.card V) (hU : IsSparseComponent G ρ U) :
    (G.minDegree : ℝ) - Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (U.card : ℝ) := by
  have hPositive : (0 : ℝ) < U.card :=
    (mul_pos (Real.sqrt_pos.2 hρ) (by exact_mod_cast hn)).trans_le hU.1
  have hNat : G.minDegree * U.card ≤ U.card * U.card + cutEdges G U := by
    exact (minDegree_mul_card_le_sum G U).trans (by
      rw [← internal_cut_identity, ← incidences_self]
      exact Nat.add_le_add_right (incidences_le_card_mul G U U) _)
  have hReal : (G.minDegree : ℝ) * (U.card : ℝ) ≤ (U.card : ℝ) * (U.card : ℝ) +
      (cutEdges G U : ℝ) := by exact_mod_cast hNat
  have hBoundary := hU.2.trans (sqrt_budget_le_card (V := V) ρ hρ.le hU.1)
  apply (mul_le_mul_iff_of_pos_right hPositive).mp
  linarith only [hReal, hBoundary]

private theorem compl_eq_union_compl_union (W W' : Finset V) (hDisjoint : Disjoint W W') :
    W'ᶜ = W ∪ (W ∪ W')ᶜ := by
  ext v
  simp only [mem_compl, mem_union]
  have h := fun hv : v ∈ W => fun hv' : v ∈ W' => Finset.disjoint_left.mp hDisjoint hv hv'
  tauto

/-- A cut of either subpart costs at most the cut of the whole and that of
the other subpart. This is the counting step of Lemma 4.1(ii). -/
theorem cutEdges_split_le (W W' : Finset V) (hDisjoint : Disjoint W W') :
    cutEdges G W' ≤ cutEdges G W + cutEdges G (W ∪ W') := by
  have hOuter : Disjoint W (W ∪ W')ᶜ := by
    exact Disjoint.mono_left subset_union_left disjoint_compl_right
  calc
    _ = incidences G W' W + incidences G W' (W ∪ W')ᶜ := by
      rw [← incidences_compl_self, compl_eq_union_compl_union W W' hDisjoint,
        incidences_union_right G _ _ _ hOuter]
    _ ≤ _ := by
      apply Nat.add_le_add
      · rw [incidences_comm G W' W, ← incidences_compl_self]
        exact incidences_mono G (Subset.rfl) (by
          intro v hv
          exact mem_compl.mpr (fun hv' => Finset.disjoint_left.mp hDisjoint hv' hv))
      · rw [← incidences_compl_self]
        exact incidences_mono G subset_union_right (Subset.rfl)

/-- The boundary estimate of Lemma 4.1(ii) in the paper's normalization. -/
theorem sparseComponent_split_boundary (W W' : Finset V) (hDisjoint : Disjoint W W')
    (ρ ρ' γ : ℝ) (hγ : ρ + ρ' ≤ γ)
    (hWhole : IsSparseComponent G ρ (W ∪ W')) (hW : IsSparseComponent G ρ' W) :
    (cutEdges G W' : ℝ) ≤ γ * (Fintype.card V : ℝ) ^ 2 := by
  have hCut : (cutEdges G W' : ℝ) ≤ (cutEdges G W : ℝ) + cutEdges G (W ∪ W') := by
    exact_mod_cast cutEdges_split_le G W W' hDisjoint
  have hScale := mul_le_mul_of_nonneg_right hγ (sq_nonneg (Fintype.card V : ℝ))
  linarith only [hCut, hWhole.2, hW.2, hScale]

/-- Lemma 4.1(iii), allowing the error parameter to increase. -/
theorem sparseComponent_relax (U : Finset V) (ρ ρ' : ℝ) (hρ : 0 < ρ) (hOrder : 0 < Fintype.card V)
    (hScale : ρ ≤ ρ') (hDegree : 2 * Real.sqrt ρ' * (Fintype.card V : ℝ) ≤ G.minDegree)
    (hU : IsSparseComponent G ρ U) : IsSparseComponent G ρ' U := by
  have hSize := sparseComponent_card_lower G ρ U hρ hOrder hU
  have hSqrt := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hScale)
    (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ Fintype.card V)
  refine ⟨by linarith only [hSize, hSqrt, hDegree], ?_⟩
  exact hU.2.trans (mul_le_mul_of_nonneg_right hScale (sq_nonneg _))

theorem closeToBipartite_comm {ρ : ℝ} {A B : Finset V} (h : CloseToBipartite G ρ A B) :
    CloseToBipartite G ρ B A := by
  obtain ⟨hDisjoint, hA, hB, hBalance, hCut⟩ := h
  refine ⟨hDisjoint.symm, hB, hA, ?_, ?_⟩
  · simpa only [abs_sub_comm (B.card : ℝ) (A.card : ℝ)] using hBalance
  · simpa only [Finset.union_comm B A, add_comm (internalEdges G B : ℝ) (internalEdges G A : ℝ)]
      using hCut

private theorem bipartite_second_side_lower (ρ : ℝ) (A B : Finset V) (hρ : 0 < ρ)
    (hn : 0 < Fintype.card V) (h : CloseToBipartite G ρ A B) :
    (G.minDegree : ℝ) - 2 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (B.card : ℝ) := by
  obtain ⟨hDisjoint, hA, _, _, hCut⟩ := h
  have hPositive : (0 : ℝ) < A.card :=
    (mul_pos (Real.sqrt_pos.2 hρ) (by exact_mod_cast hn)).trans_le hA
  have hOuter : Disjoint A (A ∪ B)ᶜ := Disjoint.mono_left subset_union_left disjoint_compl_right
  have hSum := incidences_add_compl G A B
  rw [compl_eq_union_compl_union A B hDisjoint, incidences_union_right G _ _ _ hOuter,
    incidences_self] at hSum
  have hExternal : incidences G A (A ∪ B)ᶜ ≤ cutEdges G (A ∪ B) := by
    rw [← incidences_compl_self]
    exact incidences_mono G subset_union_left (Subset.rfl)
  have hNat : G.minDegree * A.card ≤ A.card * B.card + 2 * internalEdges G A + cutEdges G (A ∪ B) := by
    have hMin := minDegree_mul_card_le_sum G A
    have hAcross := incidences_le_card_mul G A B
    omega
  have hReal : (G.minDegree : ℝ) * (A.card : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) +
      2 * (internalEdges G A : ℝ) + cutEdges G (A ∪ B) := by exact_mod_cast hNat
  have hAbsorb := sqrt_budget_le_card (V := V) ρ hρ.le hA
  apply (mul_le_mul_iff_of_pos_right hPositive).mp
  linarith only [hReal, hCut, hAbsorb, Nat.cast_nonneg (α := ℝ) (internalEdges G B),
    Nat.cast_nonneg (α := ℝ) (cutEdges G (A ∪ B))]

/-- Lemma 4.1(iv), for a simple graph with the given minimum degree. -/
theorem bipartite_sides_lower (ρ : ℝ) (A B : Finset V) (hρ : 0 < ρ)
    (hn : 0 < Fintype.card V) (h : CloseToBipartite G ρ A B) :
    (G.minDegree : ℝ) - 2 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (A.card : ℝ) ∧
      (G.minDegree : ℝ) - 2 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (B.card : ℝ) :=
  ⟨bipartite_second_side_lower G ρ B A hρ hn (closeToBipartite_comm G h),
    bipartite_second_side_lower G ρ A B hρ hn h⟩

/-- Lemma 4.1(v), relaxing the bipartite error. -/
theorem closeToBipartite_relax (A B : Finset V) (ρ ρ' : ℝ) (hρ : 0 < ρ) (hOrder : 0 < Fintype.card V)
    (hScale : ρ ≤ ρ') (hDegree : 3 * Real.sqrt ρ' * (Fintype.card V : ℝ) ≤ G.minDegree)
    (h : CloseToBipartite G ρ A B) : CloseToBipartite G ρ' A B := by
  obtain ⟨hA, hB⟩ := bipartite_sides_lower G ρ A B hρ hOrder h
  have hSqrt := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hScale)
    (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ Fintype.card V)
  exact ⟨h.1, by linarith only [hA, hDegree, hSqrt], by linarith only [hB, hDegree, hSqrt],
    h.2.2.2.1.trans (mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg _)),
    h.2.2.2.2.trans (mul_le_mul_of_nonneg_right hScale (sq_nonneg _))⟩

/-- Robust neighbours are taken inside `U`, with the threshold measured
relative to `|U|`. -/
noncomputable def robustNeighbourhoodIn (ν : ℝ) (U S : Finset V) : Finset V :=
  U.filter fun v => ν * (U.card : ℝ) ≤ (neighboursIn G S v : ℝ)

theorem robustNeighbourhoodIn_subset (ν : ℝ) (U S : Finset V) :
    robustNeighbourhoodIn G ν U S ⊆ U := filter_subset _ _

private theorem incidences_nonrobust_in (ν : ℝ) (U S T : Finset V)
    (hT : T ⊆ U \ robustNeighbourhoodIn G ν U S) :
    (incidences G S T : ℝ) ≤ ν * (U.card : ℝ) * (T.card : ℝ) := by
  unfold incidences
  push_cast
  calc
    _ ≤ ∑ _ ∈ T, ν * (U.card : ℝ) := by
      apply sum_le_sum
      intro v hv
      obtain ⟨hvU, hvN⟩ := mem_sdiff.mp (hT hv)
      apply le_of_lt
      exact lt_of_not_ge (fun h => hvN (mem_filter.mpr ⟨hvU, h⟩))
    _ = _ := by simp [mul_comm]

/-- Inequality (4.2) of Lemma 4.2. The two contributions to the discarded
incidences come from non-robust vertices in `U` and the boundary of `U`. -/
theorem incidences_outside_robustNeighbourhoodIn (ρ ν : ℝ) (U S : Finset V)
    (hν : 0 ≤ ν) (hU : IsSparseComponent G ρ U) (hS : S ⊆ U) :
    (incidences G S (robustNeighbourhoodIn G ν U S)ᶜ : ℝ) ≤
      (ν + ρ) * (Fintype.card V : ℝ) ^ 2 := by
  let N := robustNeighbourhoodIn G ν U S
  have hN : N ⊆ U := robustNeighbourhoodIn_subset G ν U S
  have hPartition : Nᶜ = (U \ N) ∪ Uᶜ := by
    ext v
    simp only [mem_compl, mem_union, mem_sdiff]
    have := @hN v
    tauto
  have hDisjoint : Disjoint (U \ N) Uᶜ := Disjoint.mono_left sdiff_subset disjoint_compl_right
  have hWithin := incidences_nonrobust_in G ν U S (U \ N) (Subset.rfl)
  have hSize : (ν * (U.card : ℝ)) * ((U \ N).card : ℝ) ≤ ν * (Fintype.card V : ℝ) ^ 2 := by
    rw [pow_two, ← mul_assoc]
    gcongr <;> exact_mod_cast Finset.card_le_univ _
  have hEdge : (incidences G S Uᶜ : ℝ) ≤ cutEdges G U := by
    rw [← incidences_compl_self]
    exact_mod_cast incidences_mono G hS (Subset.rfl : Uᶜ ⊆ Uᶜ)
  change (incidences G S Nᶜ : ℝ) ≤ _
  rw [hPartition, incidences_union_right G _ _ _ hDisjoint, Nat.cast_add]
  linarith only [hWithin, hSize, hEdge, hU.2]

omit [DecidableEq V] in
private theorem minDegree_eq_of_regular (D : ℕ) (hRegular : ∀ v, G.degree v = D)
    (hn : 0 < Fintype.card V) : G.minDegree = D := by
  have : Nonempty V := Fintype.card_pos_iff.mp hn
  apply le_antisymm
  · obtain ⟨v⟩ := (inferInstance : Nonempty V)
    simpa only [hRegular v] using G.minDegree_le_degree v
  · exact G.le_minDegree_of_forall_le_degree D (fun v => (hRegular v).ge)

private theorem incidences_add_compl_of_regular (D : ℕ) (hRegular : ∀ v, G.degree v = D)
    (S T : Finset V) :
    (incidences G S T : ℝ) + (incidences G S Tᶜ : ℝ) = (D : ℝ) * (S.card : ℝ) := by
  have h := incidences_add_compl G S T
  simp only [hRegular, sum_const, nsmul_eq_mul, Nat.mul_comm] at h
  exact_mod_cast h

/-- Lemma 4.2 at explicit scales. The interval lower bound on `S` and the
gap between the scales imply both lower bounds on the robust neighbourhood. -/
theorem robustNeighbourhoodIn_lower (D : ℕ) (hRegular : ∀ v, G.degree v = D)
    (ρ ν τ : ℝ) (U S : Finset V) (hn : 0 < Fintype.card V)
    (hρ : 0 < ρ) (hρν : ρ ≤ ν) (hτ : 0 < τ) (hτOne : τ ≤ 1)
    (hU : IsSparseComponent G ρ U) (hS : S ⊆ U)
    (hSize : τ * (U.card : ℝ) ≤ (S.card : ℝ))
    (hMin : 2 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (D : ℝ))
    (hScale : 4 * Real.sqrt ν * (Fintype.card V : ℝ) ≤ τ * (D : ℝ)) :
    let N := robustNeighbourhoodIn G ν U S
    (incidences G S (S \ N) : ℝ) ≤ ν * (Fintype.card V : ℝ) ^ 2 ∧
      (incidences G S (S ∪ N)ᶜ : ℝ) ≤ 2 * ν * (Fintype.card V : ℝ) ^ 2 ∧
      (S.card : ℝ) - Real.sqrt ν * (Fintype.card V : ℝ) ≤ (N.card : ℝ) ∧
      (D : ℝ) - Real.sqrt ν * (Fintype.card V : ℝ) ≤ (N.card : ℝ) := by
  intro N
  let n := (Fintype.card V : ℝ)
  have hnR : (0 : ℝ) < n := by dsimp [n]; exact_mod_cast hn
  have hν : 0 < ν := hρ.trans_le hρν
  have hD : (0 : ℝ) < D := by linarith only [hMin, mul_pos (Real.sqrt_pos.2 hρ) hnR]
  have hMinDegree := minDegree_eq_of_regular G D hRegular hn
  have hUSize := sparseComponent_card_lower G ρ U hρ hn hU
  rw [hMinDegree] at hUSize
  have hSSize : (τ * (D : ℝ)) / 2 ≤ (S.card : ℝ) := by
    have hHalf : (D : ℝ) / 2 ≤ (U.card : ℝ) := by linarith only [hUSize, hMin]
    have h := mul_le_mul_of_nonneg_left hHalf hτ.le
    linarith only [hSize, h]
  have hSPositive : (0 : ℝ) < S.card := (by positivity : 0 < τ * (D : ℝ) / 2).trans_le hSSize
  have hSqrt : 0 ≤ Real.sqrt ν * n := by positivity
  have hSDouble : 2 * (Real.sqrt ν * n) ≤ (S.card : ℝ) := by
    linarith only [hScale, hSSize]
  have hDDouble : 2 * (Real.sqrt ν * n) ≤ (D : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hτOne hD.le
    linarith only [hScale, h, hSqrt]
  have hLoss : (incidences G S Nᶜ : ℝ) ≤ 2 * ν * n ^ 2 := by
    have h := incidences_outside_robustNeighbourhoodIn G ρ ν U S hν.le hU hS
    have hρn := mul_le_mul_of_nonneg_right hρν (sq_nonneg n)
    linarith only [h, hρn]
  have hExact := incidences_add_compl_of_regular G D hRegular S N
  have hCapD : (incidences G S N : ℝ) ≤ (D : ℝ) * (N.card : ℝ) := by
    have hNat : incidences G S N ≤ D * N.card := by
      calc
        _ ≤ ∑ v ∈ N, D := by
          apply sum_le_sum
          intro v _
          rw [← hRegular v, ← card_neighborFinset_eq_degree]
          exact card_le_card (filter_subset _ _)
        _ = _ := by simp [Nat.mul_comm]
    exact_mod_cast hNat
  have hCapS : (incidences G S N : ℝ) ≤ (S.card : ℝ) * (N.card : ℝ) := by
    exact_mod_cast incidences_le_card_mul G S N
  have hSquare : (Real.sqrt ν * n) ^ 2 = ν * n ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hν.le]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := incidences_nonrobust_in G ν U S (S \ N) (by
      intro v hv
      exact mem_sdiff.mpr ⟨hS (mem_sdiff.mp hv).1, (mem_sdiff.mp hv).2⟩)
    refine h.trans ?_
    rw [pow_two, ← mul_assoc]
    gcongr <;> exact_mod_cast Finset.card_le_univ _
  · have h := incidences_mono G (Subset.rfl : S ⊆ S)
      (compl_subset_compl.mpr (subset_union_right : N ⊆ S ∪ N))
    exact (by exact_mod_cast h : (incidences G S (S ∪ N)ᶜ : ℝ) ≤ incidences G S Nᶜ).trans hLoss
  · apply (mul_le_mul_iff_of_pos_right hD).mp
    have h := mul_le_mul_of_nonneg_right hDDouble hSqrt
    linarith only [hExact, hCapD, hLoss, h, hSquare]
  · apply (mul_le_mul_iff_of_pos_right hSPositive).mp
    have h := mul_le_mul_of_nonneg_right hSDouble hSqrt
    linarith only [hExact, hCapS, hLoss, h, hSquare]

/-- Case 1 of Lemma 4.6. With a small `S \ N`, the two components are
`S ∪ N` and its complement in `U`. -/
theorem split_of_small_neighbourhood_difference (D : ℕ) (hRegular : ∀ v, G.degree v = D)
    (ρ ν ρ' τ : ℝ) (U S : Finset V) (hn : 0 < Fintype.card V)
    (hρ : 0 < ρ) (hρν : ρ ≤ ν) (hνQuarter : ν ≤ 1 / 4) (hτ : 0 < τ) (hτOne : τ ≤ 1)
    (hU : IsSparseComponent G ρ U) (hS : S ⊆ U)
    (hLower : τ * (U.card : ℝ) ≤ (S.card : ℝ))
    (hUpper : (S.card : ℝ) ≤ (1 - τ) * (U.card : ℝ))
    (hMin : 2 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (D : ℝ))
    (hScale : 8 * Real.sqrt ν * (Fintype.card V : ℝ) ≤ τ * (D : ℝ))
    (hCutScale : ρ + 3 * Real.sqrt ν ≤ ρ')
    (hFirstSize : (Real.sqrt ρ' + Real.sqrt ν) * (Fintype.card V : ℝ) ≤ (D : ℝ))
    (hSecondSize : Real.sqrt ρ' * (Fintype.card V : ℝ) ≤ τ * (D : ℝ) / 4) :
    let N := robustNeighbourhoodIn G ν U S
    (N.card : ℝ) ≤ (S.card : ℝ) + ν * (U.card : ℝ) →
    ((S \ N).card : ℝ) ≤ Real.sqrt ν * (Fintype.card V : ℝ) →
    let U₁ := S ∪ N
    let U₂ := U \ U₁
    Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = U ∧
      IsSparseComponent G ρ' U₁ ∧ IsSparseComponent G ρ' U₂ := by
  intro N hNonExpand hSmall U₁ U₂
  let n := (Fintype.card V : ℝ)
  let Z := N \ S
  have hRootNonneg : 0 ≤ Real.sqrt ν * n := by positivity
  have hScale' : 4 * Real.sqrt ν * n ≤ τ * (D : ℝ) := by linarith only [hScale, hRootNonneg]
  obtain ⟨_, hFar, _, hNear⟩ := robustNeighbourhoodIn_lower G D hRegular ρ ν τ U S hn
    hρ hρν hτ hτOne hU hS hLower hMin hScale'
  have hνRoot : ν ≤ Real.sqrt ν := Real.le_sqrt_self_iff.mpr (hνQuarter.trans (by norm_num))
  have hνU : ν * (U.card : ℝ) ≤ Real.sqrt ν * n := by
    have hCard : (U.card : ℝ) ≤ n := by dsimp [n]; exact_mod_cast U.card_le_univ
    exact mul_le_mul hνRoot hCard (Nat.cast_nonneg _) (Real.sqrt_nonneg ν)
  have hZCard : (Z.card : ℝ) ≤ 2 * (Real.sqrt ν * n) := by
    have h₁ : (((S \ N).card : ℝ) + ((S ∩ N).card : ℝ)) = S.card := by
      exact_mod_cast card_sdiff_add_card_inter S N
    have h₂ : (Z.card : ℝ) + ((S ∩ N).card : ℝ) = N.card := by
      have h := card_sdiff_add_card_inter N S
      rw [inter_comm N S] at h
      exact_mod_cast h
    linarith only [hNonExpand, hSmall, hνU, h₁, h₂]
  have hDisjoint : Disjoint S Z := by
    exact Finset.disjoint_left.mpr (fun _ hv hz => (mem_sdiff.mp hz).2 hv)
  have hSplit : S ∪ Z = U₁ := by
    ext v
    simp only [Z, U₁, mem_union, mem_sdiff]
    tauto
  have hInside : U₁ ⊆ U := union_subset hS (robustNeighbourhoodIn_subset G ν U S)
  have hDisjParts : Disjoint U₁ U₂ := by
    exact Finset.disjoint_left.mpr (fun _ hv hu => (mem_sdiff.mp hu).2 hv)
  have hUnionParts : U₁ ∪ U₂ = U := by
    ext v
    simp only [U₂, mem_union, mem_sdiff]
    have := @hInside v
    tauto
  have hU₁size : Real.sqrt ρ' * n ≤ (U₁.card : ℝ) := by
    have hCard : (N.card : ℝ) ≤ U₁.card := by
      exact_mod_cast card_le_card (subset_union_right : N ⊆ U₁)
    linarith only [hNear, hFirstSize, hCard]
  have hU₂size : Real.sqrt ρ' * n ≤ (U₂.card : ℝ) := by
    have hULower := sparseComponent_card_lower G ρ U hρ hn hU
    rw [minDegree_eq_of_regular G D hRegular hn] at hULower
    have hHalf : (D : ℝ) / 2 ≤ (U.card : ℝ) := by linarith only [hULower, hMin]
    have hTauHalf := mul_le_mul_of_nonneg_left hHalf hτ.le
    have h₁ : (U₁.card : ℝ) = (S.card : ℝ) + (Z.card : ℝ) := by
      exact_mod_cast (hSplit ▸ card_union_of_disjoint hDisjoint)
    have h₂ : (U₂.card : ℝ) + (U₁.card : ℝ) = U.card := by
      have hNat : U₂.card + U₁.card = U.card := by
        rw [show U₂ = U \ U₁ from rfl, card_sdiff_of_subset hInside]
        exact Nat.sub_add_cancel (card_le_card hInside)
      exact_mod_cast hNat
    linarith only [h₂, h₁, hZCard, hUpper, hTauHalf, hScale, hSecondSize]
  have hU₁cut : (cutEdges G U₁ : ℝ) ≤ (3 * Real.sqrt ν) * n ^ 2 := by
    have hEq : cutEdges G U₁ = incidences G S U₁ᶜ + incidences G Z U₁ᶜ := by
      calc
        _ = incidences G U₁ᶜ (S ∪ Z) := by rw [hSplit, incidences_comm, incidences_compl_self]
        _ = _ := by rw [incidences_union_right G _ _ _ hDisjoint,
          incidences_comm G U₁ᶜ S, incidences_comm G U₁ᶜ Z]
    have hIntoZ : (incidences G Z U₁ᶜ : ℝ) ≤ (Z.card : ℝ) * n := by
      have h := (incidences_le_card_mul G Z U₁ᶜ).trans
        (Nat.mul_le_mul_left Z.card (U₁ᶜ).card_le_univ)
      dsimp [n]
      exact_mod_cast h
    rw [hEq, Nat.cast_add]
    have hZ := mul_le_mul_of_nonneg_right hZCard (show 0 ≤ n by positivity)
    have hRootHalf : Real.sqrt ν ≤ 1 / 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa only [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
        using hνQuarter⟩
    have hDouble : 2 * ν ≤ Real.sqrt ν := by
      have h := mul_le_mul_of_nonneg_left hRootHalf (Real.sqrt_nonneg ν)
      linarith only [h, Real.sq_sqrt (hρ.le.trans hρν)]
    have hν := mul_le_mul_of_nonneg_right hDouble (sq_nonneg n)
    linarith only [hFar, hIntoZ, hZ, hν]
  have hCut₁ := mul_le_mul_of_nonneg_right
    (show 3 * Real.sqrt ν ≤ ρ' by linarith only [hρ, hCutScale]) (sq_nonneg n)
  have hCut₂ : (cutEdges G U₂ : ℝ) ≤ (cutEdges G U₁ : ℝ) + cutEdges G U := by
    have h := cutEdges_split_le G U₁ U₂ hDisjParts
    rw [hUnionParts] at h
    exact_mod_cast h
  have hBudget := mul_le_mul_of_nonneg_right hCutScale (sq_nonneg n)
  exact ⟨hDisjParts, hUnionParts, ⟨hU₁size, hU₁cut.trans hCut₁⟩,
    ⟨hU₂size, by linarith only [hCut₂, hU.2, hU₁cut, hBudget]⟩⟩

private theorem incidences_away_sum (A B : Finset V) (hDisjoint : Disjoint A B) :
    incidences G A Bᶜ + incidences G B Aᶜ =
      2 * internalEdges G A + 2 * internalEdges G B + cutEdges G (A ∪ B) := by
  let W := (A ∪ B)ᶜ
  have hA : Disjoint A W := Disjoint.mono_left subset_union_left disjoint_compl_right
  have hB : Disjoint B W := Disjoint.mono_left subset_union_right disjoint_compl_right
  have hAc : Aᶜ = B ∪ W := by
    simpa only [W, union_comm B A] using compl_eq_union_compl_union B A hDisjoint.symm
  have h₁ : incidences G A Bᶜ = 2 * internalEdges G A + incidences G A W := by
    rw [compl_eq_union_compl_union A B hDisjoint, incidences_union_right G _ _ _ hA, incidences_self]
  have h₂ : incidences G B Aᶜ = 2 * internalEdges G B + incidences G B W := by
    rw [hAc, incidences_union_right G _ _ _ hB, incidences_self]
  have h₃ : cutEdges G (A ∪ B) = incidences G A W + incidences G B W := by
    rw [← incidences_compl_self, incidences_comm, incidences_union_right G _ _ _ hDisjoint,
      incidences_comm G W A, incidences_comm G W B]
  omega

/-- Lemma 4.4 with explicit inequalities for the scales. If a witness to
failure of ordinary expansion has large `S \ N`, the two differences
`S \ N` and `N \ S` give a close-to-bipartite set. -/
theorem bipartite_of_large_neighbourhood_difference (D : ℕ) (hRegular : ∀ v, G.degree v = D)
    (ρ ν θ τ : ℝ) (U S : Finset V) (hn : 0 < Fintype.card V)
    (hρ : 0 < ρ) (hρν : ρ ≤ ν) (hνOne : ν ≤ 1) (hτ : 0 < τ) (hτOne : τ ≤ 1)
    (hU : IsSparseComponent G ρ U) (hS : S ⊆ U)
    (hLower : τ * (U.card : ℝ) ≤ (S.card : ℝ))
    (hMin : 2 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (D : ℝ))
    (hScale : 4 * Real.sqrt ν * (Fintype.card V : ℝ) ≤ τ * (D : ℝ))
    (hBoundaryScale : Real.sqrt ν + 6 * ν ≤ θ)
    (hSideScale : (Real.sqrt θ + 4 * Real.sqrt ν) * (Fintype.card V : ℝ) ≤ (D : ℝ)) :
    let N := robustNeighbourhoodIn G ν U S
    (N.card : ℝ) ≤ (S.card : ℝ) + ν * (U.card : ℝ) →
    let Y := S \ N
    let Z := N \ S
    |(Y.card : ℝ) - (Z.card : ℝ)| ≤ Real.sqrt ν * (Fintype.card V : ℝ) ∧
      (Real.sqrt ν * (Fintype.card V : ℝ) < (Y.card : ℝ) → CloseToBipartite G θ Y Z) := by
  intro N hNonExpand Y Z
  let n := (Fintype.card V : ℝ)
  let W := (S ∪ N)ᶜ
  have hnR : (0 : ℝ) < n := by dsimp [n]; exact_mod_cast hn
  have hν : 0 < ν := hρ.trans_le hρν
  have hνU : ν * (U.card : ℝ) ≤ Real.sqrt ν * n := by
    have hCard : (U.card : ℝ) ≤ n := by dsimp [n]; exact_mod_cast U.card_le_univ
    exact mul_le_mul (Real.le_sqrt_self_iff.mpr hνOne) hCard (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨hToY, hFar, hNear, _⟩ := robustNeighbourhoodIn_lower G D hRegular ρ ν τ U S hn
    hρ hρν hτ hτOne hU hS hLower hMin hScale
  have hBalance : |(Y.card : ℝ) - (Z.card : ℝ)| ≤ Real.sqrt ν * n := by
    have h₁ : (Y.card : ℝ) + ((S ∩ N).card : ℝ) = S.card := by
      exact_mod_cast card_sdiff_add_card_inter S N
    have h₂ : (Z.card : ℝ) + ((S ∩ N).card : ℝ) = N.card := by
      have h := card_sdiff_add_card_inter N S
      rw [inter_comm N S] at h
      exact_mod_cast h
    exact abs_le.mpr ⟨by linarith only [h₁, h₂, hNonExpand, hνU], by linarith only [h₁, h₂, hNear]⟩
  refine ⟨hBalance, ?_⟩
  intro hYLarge
  have hYZ : Disjoint Y Z := Finset.disjoint_left.mpr (fun _ hy hz => (mem_sdiff.mp hz).2 (mem_sdiff.mp hy).1)
  have hW : Disjoint S W := Disjoint.mono_left subset_union_left disjoint_compl_right
  have hZCompl : Zᶜ = S ∪ W := by
    ext v
    simp only [Z, W, mem_compl, mem_sdiff, mem_union]
    tauto
  have hAway : (incidences G Y Zᶜ : ℝ) ≤ 3 * ν * n ^ 2 := by
    rw [hZCompl, incidences_union_right G _ _ _ hW, Nat.cast_add, incidences_comm G Y S]
    have hNat := incidences_mono G (show Y ⊆ S from sdiff_subset) (Subset.rfl : W ⊆ W)
    have hYW : (incidences G Y W : ℝ) ≤ incidences G S W := by exact_mod_cast hNat
    linarith only [hToY, hFar, hYW]
  have hCross := incidences_add_compl_of_regular G D hRegular Y Z
  have hCrossUpper : (incidences G Y Z : ℝ) ≤ (Y.card : ℝ) * (Z.card : ℝ) := by
    exact_mod_cast incidences_le_card_mul G Y Z
  have hCharge : 3 * ν * n ^ 2 ≤ (3 * Real.sqrt ν * n) * (Y.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hYLarge.le (show 0 ≤ 3 * Real.sqrt ν * n by positivity)
    have hEq : 3 * Real.sqrt ν * n * (Real.sqrt ν * n) = 3 * ν * n ^ 2 := by
      calc
        _ = 3 * (Real.sqrt ν) ^ 2 * n ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hν.le]
    rwa [hEq] at h
  have hZ : (D : ℝ) - 3 * Real.sqrt ν * n ≤ (Z.card : ℝ) := by
    have hPositive : 0 < (Y.card : ℝ) := (mul_pos (Real.sqrt_pos.mpr hν) hnR).trans hYLarge
    apply (mul_le_mul_iff_of_pos_right hPositive).mp
    linarith only [hCross, hCrossUpper, hAway, hCharge]
  have hDUpper : (D : ℝ) ≤ n := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hn
    have h := (G.degree_lt_card_verts v).le
    rw [hRegular v] at h
    dsimp [n]
    exact_mod_cast h
  have hRev := incidences_add_compl_of_regular G D hRegular Z Y
  rw [incidences_comm G Z Y] at hRev
  have hRevAway : (incidences G Z Yᶜ : ℝ) ≤ Real.sqrt ν * n ^ 2 + 3 * ν * n ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (abs_le.mp hBalance).1 (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    have hD := mul_le_mul_of_nonneg_left hDUpper (show 0 ≤ Real.sqrt ν * n by positivity)
    linarith only [hRev, hCross, hAway, h, hD]
  have hUnionCount : (incidences G Y Zᶜ : ℝ) + (incidences G Z Yᶜ : ℝ) =
      2 * (internalEdges G Y : ℝ) + 2 * (internalEdges G Z : ℝ) + cutEdges G (Y ∪ Z) := by
    exact_mod_cast incidences_away_sum G Y Z hYZ
  have hScaleCut := mul_le_mul_of_nonneg_right hBoundaryScale (sq_nonneg n)
  have hScaleBalance : Real.sqrt ν * n ≤ θ * n := by
    have h : Real.sqrt ν ≤ θ := by linarith only [hν, hBoundaryScale]
    exact mul_le_mul_of_nonneg_right h hnR.le
  refine ⟨hYZ, ?_, ?_, hBalance.trans hScaleBalance, ?_⟩
  · linarith only [hZ, (abs_le.mp hBalance).1, hSideScale]
  · linarith only [hZ, hSideScale, mul_nonneg (Real.sqrt_nonneg ν) hnR.le]
  · have hY := Nat.cast_nonneg (α := ℝ) (internalEdges G Y)
    have hZ' := Nat.cast_nonneg (α := ℝ) (internalEdges G Z)
    linarith only [hAway, hRevAway, hUnionCount, hScaleCut, hY, hZ']

private theorem internalEdges_union_le (A W : Finset V) (hAW : Disjoint A W) :
    internalEdges G (A ∪ W) ≤ internalEdges G A + W.card * Fintype.card V := by
  have hA : incidences G (A ∪ W) A = incidences G A A + incidences G W A := by
    rw [incidences_comm G (A ∪ W) A, incidences_union_right G _ _ _ hAW, incidences_comm G A W]
  have hW : incidences G (A ∪ W) W = incidences G A W + incidences G W W := by
    rw [incidences_comm G (A ∪ W) W, incidences_union_right G _ _ _ hAW, incidences_comm G W A]
  have hU := incidences_union_right G (A ∪ W) A W hAW
  rw [incidences_self, hA, hW, incidences_self, incidences_self, incidences_comm G A W] at hU
  have hOne := incidences_le_card_mul G W A
  have hTwo := incidences_le_card_mul G W W
  rw [incidences_self] at hTwo
  have hCard := Nat.mul_le_mul_left W.card (A ∪ W).card_le_univ
  rw [card_union_of_disjoint hAW] at hCard
  nlinarith only [hU, hOne, hTwo, hCard,
    show 0 ≤ W.card * W.card by positivity]

/-- Case 2 of Lemma 4.6 after finding the close-to-bipartite subset:
either its complement in `U` is a second component or it can be added
to one side of the bipartition. -/
theorem split_or_extend_closeToBipartite (ρ θ ρ' : ℝ) (U A B : Finset V)
    (hn : 0 < Fintype.card V) (hρ : 0 < ρ) (hθ : 0 < θ) (hρ' : 0 < ρ') (hρ'One : ρ' ≤ 1)
    (hU : IsSparseComponent G ρ U) (hSub : A ∪ B ⊆ U) (hBip : CloseToBipartite G θ A B)
    (hScale : ρ + θ ≤ (ρ' / 3) ^ 2)
    (hDegree : (Real.sqrt ρ' + 2 * Real.sqrt θ + ρ' / 3) * (Fintype.card V : ℝ) ≤ G.minDegree) :
    let W := U \ (A ∪ B)
    (Disjoint (A ∪ B) W ∧ (A ∪ B) ∪ W = U ∧
      IsSparseComponent G ρ' (A ∪ B) ∧ IsSparseComponent G ρ' W) ∨
      ((A ∪ W) ∪ B = U ∧ CloseToBipartite G ρ' (A ∪ W) B) := by
  intro W
  let n := (Fintype.card V : ℝ)
  have hnR : (0 : ℝ) < n := by dsimp [n]; exact_mod_cast hn
  have hDisjoint : Disjoint (A ∪ B) W :=
    Finset.disjoint_left.mpr (fun _ hv hw => (mem_sdiff.mp hw).2 hv)
  have hUnion : (A ∪ B) ∪ W = U := by
    ext v
    simp only [W, mem_union, mem_sdiff]
    have := @hSub v
    simp only [mem_union] at this
    tauto
  have hBudget : ρ + θ + ρ' / 3 ≤ ρ' := by
    have h := mul_nonneg hρ'.le (sub_nonneg.mpr hρ'One)
    nlinarith only [hScale, h, hρ']
  have hθρ' : θ ≤ ρ' := by linarith only [hBudget, hρ, hρ']
  have hCut : (cutEdges G (A ∪ B) : ℝ) ≤ θ * n ^ 2 := by
    have hA := Nat.cast_nonneg (α := ℝ) (internalEdges G A)
    have hB := Nat.cast_nonneg (α := ℝ) (internalEdges G B)
    linarith only [hBip.2.2.2.2, hA, hB]
  have hWCut : (cutEdges G W : ℝ) ≤ (ρ' / 3) ^ 2 * n ^ 2 := by
    have hNat := cutEdges_split_le G (A ∪ B) W hDisjoint
    rw [hUnion] at hNat
    have h : (cutEdges G W : ℝ) ≤ (cutEdges G (A ∪ B) : ℝ) + cutEdges G U := by exact_mod_cast hNat
    have hScale' := mul_le_mul_of_nonneg_right hScale (sq_nonneg n)
    linarith only [h, hCut, hU.2, hScale']
  obtain ⟨hA, hB⟩ := bipartite_sides_lower G θ A B hθ hn hBip
  have hA' : Real.sqrt ρ' * n ≤ (A.card : ℝ) := by
    have h := mul_nonneg (div_nonneg hρ'.le (by norm_num : (0 : ℝ) ≤ 3)) hnR.le
    linarith only [hA, hDegree, h]
  have hB' : Real.sqrt ρ' * n ≤ (B.card : ℝ) := by
    have h := mul_nonneg (div_nonneg hρ'.le (by norm_num : (0 : ℝ) ≤ 3)) hnR.le
    linarith only [hB, hDegree, h]
  by_cases hSize : (ρ' / 3) * n ≤ (W.card : ℝ)
  · left
    have hSmallComponent : IsSparseComponent G ((ρ' / 3) ^ 2) W :=
      ⟨by rwa [Real.sqrt_sq (by positivity)], hWCut⟩
    have hWSize := sparseComponent_card_lower G ((ρ' / 3) ^ 2) W (by positivity) hn hSmallComponent
    rw [Real.sqrt_sq (by positivity)] at hWSize
    have hRoot := mul_nonneg (Real.sqrt_nonneg θ) hnR.le
    have hWScale : (ρ' / 3) ^ 2 ≤ ρ' := by
      have h := mul_nonneg hρ'.le (sub_nonneg.mpr hρ'One)
      nlinarith only [h, hρ']
    refine ⟨hDisjoint, hUnion, ⟨?_, hCut.trans (mul_le_mul_of_nonneg_right hθρ' (sq_nonneg n))⟩,
      ⟨by linarith only [hWSize, hDegree, hRoot], hWCut.trans (mul_le_mul_of_nonneg_right hWScale (sq_nonneg n))⟩⟩
    exact hA'.trans (by exact_mod_cast card_le_card (subset_union_left : A ⊆ A ∪ B))
  · right
    have hAW := Disjoint.mono_left (subset_union_left : A ⊆ A ∪ B) hDisjoint
    have hWB := (Disjoint.mono_left (subset_union_right : B ⊆ A ∪ B) hDisjoint).symm
    have hWhole : (A ∪ W) ∪ B = U := by simpa only [union_right_comm A W B] using hUnion
    have hCard : ((A ∪ W).card : ℝ) = (A.card : ℝ) + W.card := by
      exact_mod_cast card_union_of_disjoint hAW
    refine ⟨hWhole, disjoint_union_left.mpr ⟨hBip.1, hWB⟩,
      hA'.trans (by exact_mod_cast card_le_card (subset_union_left : A ⊆ A ∪ W)), hB', ?_, ?_⟩
    · have hScale' := mul_le_mul_of_nonneg_right hBudget hnR.le
      have hρn : 0 ≤ ρ * n := by positivity
      have hW := Nat.cast_nonneg (α := ℝ) W.card
      obtain ⟨hLower, hUpper⟩ := abs_le.mp hBip.2.2.2.1
      exact abs_le.mpr ⟨by linarith only [hCard, hW, hLower, hScale', hρn, hSize],
        by linarith only [hCard, hUpper, hScale', hρn, hSize]⟩
    · rw [hWhole]
      have hIncrease : (internalEdges G (A ∪ W) : ℝ) ≤ (internalEdges G A : ℝ) + (W.card : ℝ) * n := by
        dsimp [n]
        exact_mod_cast internalEdges_union_le G A W hAW
      have hSize' := mul_le_mul_of_nonneg_right (le_of_not_ge hSize) hnR.le
      have hScale' := mul_le_mul_of_nonneg_right hBudget (sq_nonneg n)
      have hOldCut := Nat.cast_nonneg (α := ℝ) (cutEdges G (A ∪ B))
      linarith only [hIncrease, hSize', hU.2, hBip.2.2.2.2, hOldCut, hScale']

/-- Ordinary robust expansion on `U`, with the paper's normalization. -/
def ExpandsInside (ν τ : ℝ) (U : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ U → τ * (U.card : ℝ) ≤ (S.card : ℝ) →
    (S.card : ℝ) ≤ (1 - τ) * (U.card : ℝ) →
    (S.card : ℝ) + ν * (U.card : ℝ) ≤ ((robustNeighbourhoodIn G ν U S).card : ℝ)

/-- Lemma 4.6 with explicit sufficient numerical inequalities in place of
the asymptotic hierarchy. `θ` is the intermediate bipartite error. -/
theorem split_or_closeToBipartite_of_not_expanding (D : ℕ) (hRegular : ∀ v, G.degree v = D)
    (ρ ν θ ρ' τ : ℝ) (U : Finset V) (hn : 0 < Fintype.card V)
    (hρ : 0 < ρ) (hρν : ρ ≤ ν) (hνQuarter : ν ≤ 1 / 4)
    (hρ' : 0 < ρ') (hρ'One : ρ' ≤ 1) (hτ : 0 < τ) (hτOne : τ ≤ 1)
    (hU : IsSparseComponent G ρ U) (hNot : ¬ ExpandsInside G ν τ U)
    (hMin : 2 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (D : ℝ))
    (hScale : 8 * Real.sqrt ν * (Fintype.card V : ℝ) ≤ τ * (D : ℝ))
    (hCutScale : ρ + 3 * Real.sqrt ν ≤ ρ')
    (hSecondSize : Real.sqrt ρ' * (Fintype.card V : ℝ) ≤ τ * (D : ℝ) / 4)
    (hBoundaryScale : Real.sqrt ν + 6 * ν ≤ θ)
    (hSideScale : (Real.sqrt θ + 4 * Real.sqrt ν) * (Fintype.card V : ℝ) ≤ (D : ℝ))
    (hExtendScale : ρ + θ ≤ (ρ' / 3) ^ 2)
    (hDegree : (Real.sqrt ρ' + 2 * Real.sqrt θ + ρ' / 3) * (Fintype.card V : ℝ) ≤ (D : ℝ)) :
    (∃ U₁ U₂ : Finset V, Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = U ∧
      IsSparseComponent G ρ' U₁ ∧ IsSparseComponent G ρ' U₂) ∨
      ∃ A B : Finset V, A ∪ B = U ∧ CloseToBipartite G ρ' A B := by
  unfold ExpandsInside at hNot
  push Not at hNot
  obtain ⟨S, hS, hLower, hUpper, hNonExpand⟩ := hNot
  let N := robustNeighbourhoodIn G ν U S
  let n := (Fintype.card V : ℝ)
  have hν := hρ.trans_le hρν
  have hνOne : ν ≤ 1 := hνQuarter.trans (by norm_num)
  have hSqrt : Real.sqrt ν ≤ Real.sqrt θ := by
    apply Real.sqrt_le_sqrt
    have h := Real.le_sqrt_self_iff.mpr hνOne
    linarith only [h, hν, hBoundaryScale]
  have hθ : 0 < θ := by linarith only [hν, hBoundaryScale, Real.sqrt_nonneg ν]
  by_cases hDiff : ((S \ N).card : ℝ) ≤ Real.sqrt ν * n
  · left
    have hFirstSize : (Real.sqrt ρ' + Real.sqrt ν) * n ≤ (D : ℝ) := by
      refine le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) hDegree
      linarith only [hSqrt, Real.sqrt_nonneg θ, hρ']
    exact ⟨S ∪ N, U \ (S ∪ N), split_of_small_neighbourhood_difference G D hRegular
      ρ ν ρ' τ U S hn hρ hρν hνQuarter hτ hτOne hU hS hLower hUpper
      hMin hScale hCutScale hFirstSize hSecondSize hNonExpand.le hDiff⟩
  · let A := S \ N
    let B := N \ S
    have hScale' : 4 * Real.sqrt ν * n ≤ τ * (D : ℝ) := by
      have h := mul_nonneg (Real.sqrt_nonneg ν) (show 0 ≤ n by positivity)
      linarith only [h, hScale]
    have hBip := (bipartite_of_large_neighbourhood_difference G D hRegular ρ ν θ τ U S hn
      hρ hρν hνOne hτ hτOne hU hS hLower hMin hScale' hBoundaryScale hSideScale hNonExpand.le).2
        (lt_of_not_ge hDiff)
    have hSub : A ∪ B ⊆ U := union_subset (sdiff_subset.trans hS)
      (sdiff_subset.trans (robustNeighbourhoodIn_subset G ν U S))
    rw [← minDegree_eq_of_regular G D hRegular hn] at hDegree
    rcases split_or_extend_closeToBipartite G ρ θ ρ' U A B hn hρ hθ hρ' hρ'One
      hU hSub hBip hExtendScale hDegree with h | h
    · exact Or.inl ⟨A ∪ B, U \ (A ∪ B), h⟩
    · exact Or.inr ⟨A ∪ (U \ (A ∪ B)), B, h⟩

/-- Lemma 4.6 with the scales chosen before the graph. The final error
`ρ'` is fixed below the range and minimum-degree scales. -/
theorem exists_nonexpanding_split_scale (α τ ρ' : ℝ)
    (hα : 0 < α) (hτ : 0 < τ) (hτOne : τ ≤ 1) (hρ' : 0 < ρ') (hρ'One : ρ' ≤ 1)
    (hFinal : 4 * Real.sqrt ρ' ≤ τ * α) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ρ : ℝ, ν ≤ ν₀ → 0 < ρ → ρ ≤ ν →
      ∀ {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
        (D : ℕ) (U : Finset W),
        0 < Fintype.card W → (∀ v, H.degree v = D) → α * (Fintype.card W : ℝ) ≤ (D : ℝ) →
        IsSparseComponent H ρ U → ¬ ExpandsInside H ν τ U →
        (∃ U₁ U₂ : Finset W, Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = U ∧
          IsSparseComponent H ρ' U₁ ∧ IsSparseComponent H ρ' U₂) ∨
          ∃ A B : Finset W, A ∪ B = U ∧ CloseToBipartite H ρ' A B := by
  let b := min (1 / 2 : ℝ) (min (ρ' / 4) (min ((ρ' / 3) ^ 2 / 8)
    (min (τ * α / 8) ((α / 8) ^ 2 / 7))))
  have hb : 0 < b := by
    unfold b
    exact lt_min (by norm_num) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  refine ⟨b ^ 2, by positivity, ?_⟩
  intro ν ρ hνBudget hρ hρν W _ _ H _ D U hn hRegular hDense hU hNot
  let t := Real.sqrt ν
  let θ := 7 * t
  let n := (Fintype.card W : ℝ)
  have ht : t ≤ b := Real.sqrt_le_iff.mpr ⟨hb.le, hνBudget⟩
  have htHalf : t ≤ 1 / 2 := ht.trans (by simp [b, min_le_iff])
  have htCut : t ≤ ρ' / 4 := ht.trans (by simp [b, min_le_iff])
  have htExtend : t ≤ (ρ' / 3) ^ 2 / 8 := ht.trans (by simp [b, min_le_iff])
  have htRange : t ≤ τ * α / 8 := ht.trans (by simp [b, min_le_iff])
  have htSide : t ≤ (α / 8) ^ 2 / 7 := ht.trans (by simp [b, min_le_iff])
  have hν : 0 < ν := hρ.trans_le hρν
  have hνQuarter : ν ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg ν) htHalf 2
    change (Real.sqrt ν) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 at h
    rw [Real.sq_sqrt hν.le] at h
    norm_num at h
    exact h
  have hνt : ν ≤ t := Real.le_sqrt_self_iff.mpr (hνQuarter.trans (by norm_num))
  have hRoot : Real.sqrt ρ ≤ t := Real.sqrt_le_sqrt hρν
  have hθRoot : Real.sqrt θ ≤ α / 8 := by
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by dsimp [θ]; linarith only [htSide]⟩
  have hτα : τ * α ≤ α := by simpa using mul_le_mul_of_nonneg_right hτOne hα.le
  have hρ'Root : ρ' ≤ Real.sqrt ρ' := Real.le_sqrt_self_iff.mpr hρ'One
  have hn₀ : 0 ≤ n := by positivity
  have hτDense := mul_le_mul_of_nonneg_left hDense hτ.le
  have hMin : 2 * Real.sqrt ρ * n ≤ D :=
    (mul_le_mul_of_nonneg_right (by linarith only [hRoot, htRange, hτα, hα]) hn₀).trans hDense
  have hScale : 8 * t * n ≤ τ * (D : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (show 8 * t ≤ τ * α by linarith only [htRange]) hn₀
    linarith only [h, hτDense]
  have hSecond : Real.sqrt ρ' * n ≤ τ * (D : ℝ) / 4 := by
    have h := mul_le_mul_of_nonneg_right hFinal hn₀
    linarith only [h, hτDense]
  refine split_or_closeToBipartite_of_not_expanding H D hRegular ρ ν θ ρ' τ U hn hρ hρν
    hνQuarter hρ' hρ'One hτ hτOne hU hNot hMin hScale ?_ hSecond ?_ ?_ ?_ ?_
  · linarith only [hρν, hνt, htCut]
  · dsimp only [θ]
    linarith only [hνt]
  · exact (mul_le_mul_of_nonneg_right (by linarith only [hθRoot, htRange, hτα, hα]) hn₀).trans hDense
  · dsimp only [θ]
    linarith only [hρν, hνt, htExtend]
  · exact (mul_le_mul_of_nonneg_right (by linarith only [hθRoot, hFinal, hρ'Root, hτα, hα]) hn₀).trans hDense

/-- Equation (3.4.14) in Staden's thesis. Few robust neighbours of a set
in `A` can also lie in `A`, since these incidences consume internal edges. -/
theorem same_side_robustNeighbourhood_bound (ρ ν : ℝ) (A B S : Finset V)
    (hn : 0 < Fintype.card V) (hρ : 0 < ρ) (hS : S ⊆ A)
    (hBip : CloseToBipartite G ρ A B)
    (hScale : 2 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ ν * ((A ∪ B).card : ℝ)) :
    (((robustNeighbourhoodIn G ν (A ∪ B) S) ∩ A).card : ℝ) ≤
      Real.sqrt ρ * (Fintype.card V : ℝ) := by
  let T := (robustNeighbourhoodIn G ν (A ∪ B) S) ∩ A
  let n := (Fintype.card V : ℝ)
  have hnR : (0 : ℝ) < n := by dsimp [n]; exact_mod_cast hn
  have hLocal : ν * ((A ∪ B).card : ℝ) * (T.card : ℝ) ≤ (incidences G S T : ℝ) := by
    unfold incidences
    push_cast
    calc
      _ = ∑ _ ∈ T, ν * ((A ∪ B).card : ℝ) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => (mem_filter.mp (mem_inter.mp hv).1).2)
  have hInc : (incidences G S T : ℝ) ≤ 2 * (internalEdges G A : ℝ) := by
    have h := incidences_mono G hS (inter_subset_right : T ⊆ A)
    rw [incidences_self] at h
    exact_mod_cast h
  have hMass : (internalEdges G A : ℝ) ≤ ρ * n ^ 2 := by
    have hB := Nat.cast_nonneg (α := ℝ) (internalEdges G B)
    have hCut := Nat.cast_nonneg (α := ℝ) (cutEdges G (A ∪ B))
    linarith only [hBip.2.2.2.2, hB, hCut]
  have hScale' := mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg (α := ℝ) T.card)
  have hRoot : 0 < 2 * Real.sqrt ρ * n := by positivity
  have hSq : (Real.sqrt ρ * n) ^ 2 = ρ * n ^ 2 := by rw [mul_pow, Real.sq_sqrt hρ.le]
  change (T.card : ℝ) ≤ Real.sqrt ρ * n
  apply (mul_le_mul_iff_of_pos_left hRoot).mp
  linarith only [hScale', hLocal, hInc, hMass, hSq]

/-- Bipartite robust expansion with the range measured on the source
side and the threshold and surplus measured on both sides together. -/
def ExpandsAcross (ν τ : ℝ) (A B : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ A → τ * (A.card : ℝ) ≤ (S.card : ℝ) →
    (S.card : ℝ) ≤ (1 - τ) * (A.card : ℝ) →
    (S.card : ℝ) + ν * ((A ∪ B).card : ℝ) ≤
      (((robustNeighbourhoodIn G ν (A ∪ B) S) ∩ B).card : ℝ)

/-- Lemma 4.7 with explicit scales, following Staden's Lemma 3.4.7.
The ordinary neighbourhood uses the larger threshold `μ`. -/
theorem split_of_not_expanding_across (D : ℕ) (hRegular : ∀ v, G.degree v = D)
    (ρ ν μ θ ρ' τ : ℝ) (A B : Finset V) (hn : 0 < Fintype.card V)
    (hρ : 0 < ρ) (hνμ : ν ≤ μ) (hμOne : μ ≤ 1) (hτ : 0 < τ) (hτOne : τ ≤ 1)
    (hBip : CloseToBipartite G ρ A B) (hNot : ¬ ExpandsAcross G ν τ A B)
    (hSmall : Real.sqrt ρ ≤ ν)
    (hDense : 4 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (D : ℝ))
    (hSame : 2 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ ν * (D : ℝ))
    (hPay : 2 * ν * (Fintype.card V : ℝ) ≤ μ * (D : ℝ))
    (hScale : 12 * Real.sqrt μ * (Fintype.card V : ℝ) ≤ τ * (D : ℝ))
    (hDiff : (Real.sqrt ρ + Real.sqrt μ) * (Fintype.card V : ℝ) < τ * (D : ℝ) / 2)
    (hBipCut : Real.sqrt μ + 6 * μ ≤ θ)
    (hBipSize : (Real.sqrt θ + 4 * Real.sqrt μ) * (Fintype.card V : ℝ) ≤ (D : ℝ))
    (hCut : ρ + θ ≤ ρ')
    (hFirst : (Real.sqrt ρ' + 2 * Real.sqrt θ) * (Fintype.card V : ℝ) ≤ (D : ℝ))
    (hSecond : (Real.sqrt ρ' + ρ + 2 * ν) * (Fintype.card V : ℝ) ≤ τ * (D : ℝ)) :
    ∃ U₁ U₂ : Finset V, Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = A ∪ B ∧
      IsSparseComponent G ρ' U₁ ∧ IsSparseComponent G ρ' U₂ := by
  unfold ExpandsAcross at hNot
  push Not at hNot
  obtain ⟨S, hS, hSLower, hSUpper, hFailure⟩ := hNot
  let U := A ∪ B
  let n := (Fintype.card V : ℝ)
  let N := robustNeighbourhoodIn G ν U S
  let M := robustNeighbourhoodIn G μ U S
  let Y := S \ M
  let Z := M \ S
  let U₁ := Y ∪ Z
  let U₂ := U \ U₁
  have hn₀ : 0 ≤ n := by positivity
  have hν : 0 < ν := (Real.sqrt_pos.mpr hρ).trans_le hSmall
  have hμ : 0 < μ := hν.trans_le hνμ
  have hρRoot : ρ ≤ Real.sqrt ρ := Real.le_sqrt_self_iff.mpr (by
    have h := hSmall.trans (hνμ.trans hμOne)
    exact (Real.sqrt_le_sqrt_iff (by norm_num : (0 : ℝ) ≤ 1)).mp (by simpa using h))
  have hρν : ρ ≤ ν := hρRoot.trans hSmall
  have hReg := minDegree_eq_of_regular G D hRegular hn
  obtain ⟨hA, hB⟩ := bipartite_sides_lower G ρ A B hρ hn hBip
  rw [hReg] at hA hB
  have hu : (U.card : ℝ) = (A.card : ℝ) + B.card := by
    exact_mod_cast card_union_of_disjoint hBip.1
  have hHalf : (D : ℝ) / 2 ≤ (A.card : ℝ) := by linarith only [hA, hDense]
  have hUD : (D : ℝ) ≤ (U.card : ℝ) := by linarith only [hA, hB, hDense, hu]
  have hUn : (U.card : ℝ) ≤ n := by dsimp [n]; exact_mod_cast U.card_le_univ
  have hN : N ⊆ U := robustNeighbourhoodIn_subset G ν U S
  have hM : M ⊆ N := by
    intro v hv
    obtain ⟨hvU, hvμ⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨hvU, (mul_le_mul_of_nonneg_right hνμ (Nat.cast_nonneg _)).trans hvμ⟩
  have hSameBudget : 2 * Real.sqrt ρ * n ≤ ν * (U.card : ℝ) :=
    hSame.trans (mul_le_mul_of_nonneg_left hUD hν.le)
  have hNA := same_side_robustNeighbourhood_bound G ρ ν A B S hn hρ hS hBip hSameBudget
  have hNCard : (N.card : ℝ) = ((N ∩ A).card : ℝ) + (N ∩ B).card := by
    have hEq : (N ∩ A) ∪ (N ∩ B) = N := by
      ext v
      simp only [mem_union, mem_inter]
      have hv := @hN v
      change v ∈ N → v ∈ A ∪ B at hv
      rw [mem_union] at hv
      tauto
    have hDisj := hBip.1.mono (inter_subset_right : N ∩ A ⊆ A) (inter_subset_right : N ∩ B ⊆ B)
    exact_mod_cast (hEq ▸ card_union_of_disjoint hDisj)
  have hMSize : (M.card : ℝ) ≤ (S.card : ℝ) + 2 * ν * n := by
    have h := mul_le_mul_of_nonneg_left hUn hν.le
    have h' := mul_le_mul_of_nonneg_right hSmall hn₀
    have hMN : (M.card : ℝ) ≤ N.card := by exact_mod_cast card_le_card hM
    linarith only [h, h', hMN, hNCard, hFailure, hNA]
  have hFailμ : (M.card : ℝ) ≤ (S.card : ℝ) + μ * (U.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hUD hμ.le
    linarith only [h, hMSize, hPay]
  have hLargeY : Real.sqrt μ * n < (Y.card : ℝ) := by
    have hInt : (S ∩ M).card ≤ (N ∩ A).card := by
      apply card_le_card
      intro v hv
      exact mem_inter.mpr ⟨hM (mem_inter.mp hv).2, hS (mem_inter.mp hv).1⟩
    have hIntR : ((S ∩ M).card : ℝ) ≤ (N ∩ A).card := by exact_mod_cast hInt
    have hSum : (Y.card : ℝ) + (S ∩ M).card = S.card := by exact_mod_cast card_sdiff_add_card_inter S M
    have h := mul_le_mul_of_nonneg_left hHalf hτ.le
    linarith only [hIntR, hSum, hNA, hSLower, h, hDiff]
  have hU : IsSparseComponent G ρ U := by
    have hA' : (A.card : ℝ) ≤ U.card := by exact_mod_cast card_le_card (subset_union_left : A ⊆ U)
    have h₁ := Nat.cast_nonneg (α := ℝ) (internalEdges G A)
    have h₂ := Nat.cast_nonneg (α := ℝ) (internalEdges G B)
    exact ⟨hBip.2.1.trans hA', by linarith only [hBip.2.2.2.2, h₁, h₂]⟩
  have hOrdLower : (τ / 3) * (U.card : ℝ) ≤ (S.card : ℝ) := by
    have hRho := mul_le_mul_of_nonneg_right hρRoot hn₀
    have hUSize : (U.card : ℝ) ≤ 3 * (A.card : ℝ) := by
      linarith only [hu, (abs_le.mp hBip.2.2.2.1).1, hHalf, hDense, hRho]
    have h := mul_le_mul_of_nonneg_left hUSize (show 0 ≤ τ / 3 by positivity)
    linarith only [h, hSLower]
  have hOrdScale : 4 * Real.sqrt μ * n ≤ (τ / 3) * (D : ℝ) := by linarith only [hScale]
  have hBip' := (bipartite_of_large_neighbourhood_difference G D hRegular ρ μ θ (τ / 3) U S hn
    hρ (hρν.trans hνμ) hμOne (by positivity) (by linarith only [hτOne])
    hU (hS.trans subset_union_left) hOrdLower (by linarith only [hDense, show 0 ≤ Real.sqrt ρ * n by positivity])
    hOrdScale hBipCut hBipSize hFailμ).2 hLargeY
  have hθ : 0 < θ := by linarith only [hBipCut, hμ, Real.sqrt_nonneg μ]
  have hInside : U₁ ⊆ U := union_subset (sdiff_subset.trans (hS.trans subset_union_left))
    (sdiff_subset.trans (hM.trans hN))
  have hDisj : Disjoint U₁ U₂ := Finset.disjoint_left.mpr (fun _ hv hw => (mem_sdiff.mp hw).2 hv)
  have hUnion : U₁ ∪ U₂ = U := by
    ext v
    simp only [U₂, mem_union, mem_sdiff]
    have := @hInside v
    tauto
  have hU₁Theta : IsSparseComponent G θ U₁ := by
    have hSide : (Y.card : ℝ) ≤ U₁.card := by exact_mod_cast card_le_card (subset_union_left : Y ⊆ U₁)
    have h₁ := Nat.cast_nonneg (α := ℝ) (internalEdges G Y)
    have h₂ := Nat.cast_nonneg (α := ℝ) (internalEdges G Z)
    exact ⟨hBip'.2.1.trans hSide, by linarith only [hBip'.2.2.2.2, h₁, h₂]⟩
  have hU₁size : Real.sqrt ρ' * n ≤ (U₁.card : ℝ) := by
    have hSide := (bipartite_sides_lower G θ Y Z hθ hn hBip').1
    rw [hReg] at hSide
    have hCard : (Y.card : ℝ) ≤ U₁.card := by exact_mod_cast card_le_card (subset_union_left : Y ⊆ U₁)
    linarith only [hSide, hCard, hFirst]
  have hU₂size : Real.sqrt ρ' * n ≤ (U₂.card : ℝ) := by
    have hParts : (U₁.card : ℝ) + U₂.card = U.card := by
      exact_mod_cast (hUnion ▸ card_union_of_disjoint hDisj).symm
    have hY : (Y.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card (sdiff_subset : Y ⊆ S)
    have hZ : (Z.card : ℝ) ≤ M.card := by exact_mod_cast card_le_card (sdiff_subset : Z ⊆ M)
    have hU₁ : (U₁.card : ℝ) ≤ (Y.card : ℝ) + Z.card := by exact_mod_cast card_union_le Y Z
    have h := mul_le_mul_of_nonneg_left hHalf hτ.le
    linarith only [hParts, hu, hY, hZ, hU₁, hMSize, hSUpper, h,
      (abs_le.mp hBip.2.2.2.1).2, hSecond]
  exact ⟨U₁, U₂, hDisj, hUnion, ⟨hU₁size, hU₁Theta.2.trans (mul_le_mul_of_nonneg_right
    (by linarith only [hCut, hρ]) (sq_nonneg n))⟩,
    ⟨hU₂size, sparseComponent_split_boundary G U₁ U₂ hDisj ρ θ ρ' hCut
      (hUnion.symm ▸ hU) hU₁Theta⟩⟩

/-- Lemma 4.7 with a cutoff for the two input errors chosen before
the graph and witness. This uses the rescaling `μ = 2ν / α`. -/
theorem exists_bipartite_split_scale (α τ ρ' : ℝ)
    (hα : 0 < α) (hαOne : α ≤ 1) (hτ : 0 < τ) (hτOne : τ ≤ 1)
    (hρ' : 0 < ρ') (hFinal : 4 * Real.sqrt ρ' ≤ τ * α) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ρ : ℝ, ν ≤ ν₀ → 0 < ρ → ρ ≤ (α * ν / 2) ^ 2 → 0 < ν →
      ∀ {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
        (D : ℕ) (A B : Finset W), 0 < Fintype.card W → (∀ v, H.degree v = D) →
        α * (Fintype.card W : ℝ) ≤ (D : ℝ) →
        CloseToBipartite H ρ A B → ¬ ExpandsAcross H ν τ A B →
        ∃ U₁ U₂ : Finset W, Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = A ∪ B ∧
          IsSparseComponent H ρ' U₁ ∧ IsSparseComponent H ρ' U₂ := by
  let b := min (1 / 2 : ℝ) (min (τ * α / 24) (min (ρ' / 8) ((α / 8) ^ 2 / 7)))
  have hb : 0 < b := by
    unfold b
    exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  refine ⟨α * b ^ 2 / 2, by positivity, ?_⟩
  intro ν ρ hνBudget hρ hρBudget hν W _ _ H _ D A B hn hRegular hDense hBip hNot
  let μ := 2 * ν / α
  let t := Real.sqrt μ
  let θ := 7 * t
  let n := (Fintype.card W : ℝ)
  have hnR : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμEq : μ * α = 2 * ν := div_mul_cancel₀ _ hα.ne'
  have hμBudget : μ ≤ b ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hα).mp
    rw [hμEq]
    linarith only [hνBudget]
  have ht : t ≤ b := Real.sqrt_le_iff.mpr ⟨hb.le, hμBudget⟩
  have htHalf : t ≤ 1 / 2 := ht.trans (by simp [b, min_le_iff])
  have htRange : t ≤ τ * α / 24 := ht.trans (by simp [b, min_le_iff])
  have htCut : t ≤ ρ' / 8 := ht.trans (by simp [b, min_le_iff])
  have htSide : t ≤ (α / 8) ^ 2 / 7 := ht.trans (by simp [b, min_le_iff])
  have hμOne : μ ≤ 1 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg μ) htHalf 2
    change (Real.sqrt μ) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 at h
    rw [Real.sq_sqrt hμ.le] at h
    linarith only [h]
  have hνTwo : 2 * ν ≤ μ := by
    have h := mul_le_mul_of_nonneg_left hαOne hμ.le
    linarith only [h, hμEq]
  have hνμ : ν ≤ μ := by linarith only [hνTwo, hν]
  have hRoot : Real.sqrt ρ ≤ α * ν / 2 := Real.sqrt_le_iff.mpr ⟨by positivity, hρBudget⟩
  have hαν := mul_le_mul_of_nonneg_right hαOne hν.le
  have hSmall : Real.sqrt ρ ≤ ν := by linarith only [hRoot, hαν, hν]
  have hμt : μ ≤ t := Real.le_sqrt_self_iff.mpr hμOne
  have hρRoot : ρ ≤ Real.sqrt ρ := Real.le_sqrt_self_iff.mpr (by
    apply (Real.sqrt_le_sqrt_iff (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa using hSmall.trans (hνμ.trans hμOne))
  have hθRoot : Real.sqrt θ ≤ α / 8 := Real.sqrt_le_iff.mpr
    ⟨by positivity, by dsimp [θ]; linarith only [htSide]⟩
  have hτα : τ * α ≤ α := by simpa using mul_le_mul_of_nonneg_right hτOne hα.le
  have hτDense := mul_le_mul_of_nonneg_left hDense hτ.le
  have hSmallT : Real.sqrt ρ ≤ t := hSmall.trans (hνμ.trans hμt)
  refine split_of_not_expanding_across H D hRegular ρ ν μ θ ρ' τ A B hn hρ hνμ hμOne
    hτ hτOne hBip hNot hSmall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (mul_le_mul_of_nonneg_right (by linarith only [hSmallT, htRange, hτα, hα]) hnR.le).trans hDense
  · have h := mul_le_mul_of_nonneg_right hRoot hnR.le
    have h' := mul_le_mul_of_nonneg_left hDense hν.le
    linarith only [h, h']
  · have h := mul_le_mul_of_nonneg_right hμEq.ge hnR.le
    have h' := mul_le_mul_of_nonneg_left hDense hμ.le
    linarith only [h, h']
  · have h := mul_le_mul_of_nonneg_right
      (show 12 * t ≤ τ * α by linarith only [htRange, mul_pos hτ hα]) hnR.le
    linarith only [h, hτDense]
  · have h := mul_lt_mul_of_pos_right
      (show Real.sqrt ρ + t < τ * α / 2 by linarith only [hSmallT, htRange, mul_pos hτ hα]) hnR
    linarith only [h, hτDense]
  · dsimp only [θ]
    linarith only [hμt]
  · exact (mul_le_mul_of_nonneg_right (by linarith only [hθRoot, htRange, hτα, hα]) hnR.le).trans hDense
  · dsimp only [θ]
    linarith only [hρRoot, hSmallT, htCut]
  · exact (mul_le_mul_of_nonneg_right (by linarith only [hθRoot, hFinal, hτα, hα]) hnR.le).trans hDense
  · have h := mul_le_mul_of_nonneg_right
      (show Real.sqrt ρ' + ρ + 2 * ν ≤ τ * α by
        linarith only [hFinal, hρRoot, hSmallT, hνTwo, hμt, htRange, mul_pos hτ hα]) hnR.le
    linarith only [h, hτDense]

/-- The movable set for the bipartition adjustment. A vertex is marked
when its degree outside the opposite side reaches four square-root units. -/
noncomputable def bipartitionExceptions (ρ : ℝ) (A B : Finset V) : Finset V :=
  (A.filter fun v => 4 * (Real.sqrt ρ * (Fintype.card V : ℝ)) ≤ (neighboursIn G Bᶜ v : ℝ)) ∪
    (B.filter fun v => 4 * (Real.sqrt ρ * (Fintype.card V : ℝ)) ≤ (neighboursIn G Aᶜ v : ℝ))

/-- The incidence budget for Lemma 4.12. The larger marking threshold
pays for counting each moved vertex in the edits of both sides. -/
theorem bipartitionExceptions_card (ρ : ℝ) (A B : Finset V)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V) (hBip : CloseToBipartite G ρ A B) :
    ((bipartitionExceptions G ρ A B).card : ℝ) ≤ Real.sqrt ρ * (Fintype.card V : ℝ) / 2 := by
  let n := (Fintype.card V : ℝ)
  let t := Real.sqrt ρ * n
  let E (P Q : Finset V) := P.filter fun v => 4 * t ≤ (neighboursIn G Qᶜ v : ℝ)
  have hnR : 0 < n := by dsimp [n]; exact_mod_cast hn
  have ht : 0 < t := mul_pos (Real.sqrt_pos.mpr hρ) hnR
  have hMass (P Q : Finset V) : 4 * t * ((E P Q).card : ℝ) ≤ incidences G Qᶜ P := by
    have hMark : 4 * t * ((E P Q).card : ℝ) ≤ incidences G Qᶜ (E P Q) := by
      unfold incidences
      push_cast
      calc
        _ = ∑ _ ∈ E P Q, 4 * t := by simp [mul_comm]
        _ ≤ _ := sum_le_sum fun v hv => (mem_filter.mp hv).2
    exact hMark.trans (by exact_mod_cast incidences_mono G (Subset.rfl : Qᶜ ⊆ Qᶜ) (filter_subset _ _))
  have hCount : ((bipartitionExceptions G ρ A B).card : ℝ) ≤ ((E A B).card : ℝ) + (E B A).card := by
    exact_mod_cast card_union_le (E A B) (E B A)
  have hBudget : (incidences G Bᶜ A : ℝ) + incidences G Aᶜ B ≤ 2 * ρ * n ^ 2 := by
    rw [incidences_comm G Bᶜ A, incidences_comm G Aᶜ B]
    have h := incidences_away_sum G A B hBip.1
    have h' : (incidences G A Bᶜ : ℝ) + incidences G B Aᶜ =
        2 * (internalEdges G A : ℝ) + 2 * (internalEdges G B : ℝ) + (cutEdges G (A ∪ B) : ℝ) := by
      exact_mod_cast h
    have hNonneg := Nat.cast_nonneg (α := ℝ) (cutEdges G (A ∪ B))
    linarith only [h', hBip.2.2.2.2, hNonneg]
  have hMultiply := mul_le_mul_of_nonneg_left hCount (show 0 ≤ 4 * t by positivity)
  have hSquare : t ^ 2 = ρ * n ^ 2 := by dsimp [t]; rw [mul_pow, Real.sq_sqrt hρ.le]
  change ((bipartitionExceptions G ρ A B).card : ℝ) ≤ t / 2
  apply (mul_le_mul_iff_of_pos_left (show 0 < 4 * t by positivity)).mp
  linarith only [hMultiply, hMass A B, hMass B A, hBudget, hSquare]

/-- After the marked vertices have been removed, each fixed vertex has
at least half its ambient degree in the opposite fixed side. -/
theorem bipartitionExceptions_retained_degree (ρ : ℝ) (A B : Finset V)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V) (hBip : CloseToBipartite G ρ A B)
    (v : V) (hv : v ∈ A) (hFixed : v ∉ bipartitionExceptions G ρ A B)
    (hDense : 9 * (Real.sqrt ρ * (Fintype.card V : ℝ)) ≤ (G.degree v : ℝ)) :
    G.degree v ≤ 2 * neighboursIn G (B \ bipartitionExceptions G ρ A B) v := by
  let X := bipartitionExceptions G ρ A B
  let t := Real.sqrt ρ * (Fintype.card V : ℝ)
  have hOutside : (neighboursIn G Bᶜ v : ℝ) < 4 * t := by
    apply lt_of_not_ge
    intro h
    exact hFixed (mem_union.mpr (Or.inl (mem_filter.mpr ⟨hv, h⟩)))
  have hAdd := LowSetEdgePreprocessing.neighboursIn_add_compl G B v
  have hAddR : (neighboursIn G B v : ℝ) + (neighboursIn G Bᶜ v : ℝ) = G.degree v := by
    exact_mod_cast hAdd
  have hCount := bipartitionExceptions_card G ρ A B hρ hn hBip
  have hLoss : (neighboursIn G B v : ℝ) ≤ (neighboursIn G (B \ X) v : ℝ) + X.card := by
    have he : (B.filter fun w => G.Adj v w) \ X = (B \ X).filter (fun w => G.Adj v w) := by
      ext w
      simp only [mem_sdiff, mem_filter]
      tauto
    rw [neighboursIn_eq_filter_card, neighboursIn_eq_filter_card]
    exact_mod_cast (show (B.filter fun w => G.Adj v w).card ≤
      ((B \ X).filter fun w => G.Adj v w).card + X.card from
        he ▸ card_le_card_sdiff_add_card (s := B.filter fun w => G.Adj v w) (t := X))
  exact_mod_cast (show (G.degree v : ℝ) ≤ 2 * (neighboursIn G (B \ X) v : ℝ) by
    linarith only [hOutside, hAddR, hCount, hLoss, hDense])

private theorem cutEdges_le_of_edit (U W : Finset V) :
    cutEdges G W ≤ cutEdges G U + (W \ U).card * Fintype.card V +
      (U \ W).card * Fintype.card V := by
  have hDifference (P Q : Finset V) : P ⊆ Q ∪ (P \ Q) := by
    intro v hv
    by_cases h : v ∈ Q
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hv, h⟩)
  have hDis (P Q : Finset V) : Disjoint Q (P \ Q) :=
    Finset.disjoint_left.mpr (fun _ hq hp => (mem_sdiff.mp hp).2 hq)
  have hComplements : Wᶜ \ Uᶜ = U \ W := by
    ext v
    simp only [mem_sdiff, mem_compl, not_not]
    exact and_comm
  have hAdded := incidences_mono G (hDifference W U) (Subset.rfl : Wᶜ ⊆ Wᶜ)
  rw [incidences_comm G (U ∪ (W \ U)) Wᶜ,
    incidences_union_right G _ _ _ (hDis W U), incidences_comm G Wᶜ U] at hAdded
  have hRemoved := incidences_mono G (Subset.rfl : U ⊆ U) (hDifference Wᶜ Uᶜ)
  rw [incidences_union_right G _ _ _ (hDis Wᶜ Uᶜ), hComplements] at hRemoved
  have h₁ := (incidences_le_card_mul G Wᶜ (W \ U)).trans
    (Nat.mul_le_mul_right _ (card_le_univ _))
  have h₂ := (incidences_le_card_mul G U (U \ W)).trans
    (Nat.mul_le_mul_right _ (card_le_univ _))
  rw [← incidences_compl_self G W, ← incidences_compl_self G U]
  rw [Nat.mul_comm (Fintype.card V) ((W \ U).card)] at h₁
  rw [Nat.mul_comm (Fintype.card V) ((U \ W).card)] at h₂
  omega

/-- Editing the sides of a fixed component preserves closeness to
bipartite under explicit size and edge budgets. -/
private theorem closeToBipartite_of_edit_budget (ρ η κ ρ' : ℝ) (A B A' B' : Finset V)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V) (hOld : CloseToBipartite G ρ A B)
    (hNew : Disjoint A' B')
    (hCut : (cutEdges G (A' ∪ B') : ℝ) ≤ cutEdges G (A ∪ B) +
      κ * (Fintype.card V : ℝ) ^ 2)
    (hEdit : ((A \ A').card : ℝ) + ((A' \ A).card : ℝ) +
      ((B \ B').card : ℝ) + ((B' \ B).card : ℝ) ≤ η * (Fintype.card V : ℝ))
    (hScale : ρ + η ≤ ρ') (hCutScale : ρ + η + κ ≤ ρ')
    (hSize : (Real.sqrt ρ' + 2 * Real.sqrt ρ + η) * (Fintype.card V : ℝ) ≤ G.minDegree) :
    CloseToBipartite G ρ' A' B' := by
  let n := (Fintype.card V : ℝ)
  have hn₀ : 0 ≤ n := by positivity
  have hN (P Q : Finset V) : (P.card : ℝ) ≤ (Q.card : ℝ) + ((P \ Q).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := P) (t := Q)).trans_eq (Nat.add_comm _ _)
  have hEdges (P Q : Finset V) :
      (internalEdges G Q : ℝ) ≤ (internalEdges G P : ℝ) + ((Q \ P).card : ℝ) * n := by
    have hSub : Q ⊆ P ∪ (Q \ P) := by
      intro v hv
      by_cases hp : v ∈ P
      · exact mem_union.mpr (Or.inl hp)
      · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hv, hp⟩))
    have hMono : internalEdges G Q ≤ internalEdges G (P ∪ (Q \ P)) := by
      unfold internalEdges
      apply card_le_card
      intro x hx
      obtain ⟨he, hs⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨he, hs.trans hSub⟩
    have hDis : Disjoint P (Q \ P) := Finset.disjoint_left.mpr (fun _ h₁ h₂ => (mem_sdiff.mp h₂).2 h₁)
    dsimp [n]
    exact_mod_cast hMono.trans (internalEdges_union_le G P (Q \ P) hDis)
  have ha := hN A A'
  have ha' := hN A' A
  have hb := hN B B'
  have hb' := hN B' B
  have h₁ := Nat.cast_nonneg (α := ℝ) (A \ A').card
  have h₂ := Nat.cast_nonneg (α := ℝ) (A' \ A).card
  have h₃ := Nat.cast_nonneg (α := ℝ) (B \ B').card
  have h₄ := Nat.cast_nonneg (α := ℝ) (B' \ B).card
  obtain ⟨hALower, hBLower⟩ := bipartite_sides_lower G ρ A B hρ hn hOld
  have hScaleN := mul_le_mul_of_nonneg_right hScale hn₀
  refine ⟨hNew, ?_, ?_, ?_, ?_⟩
  · linarith only [hALower, hSize, ha, hEdit, h₂, h₃, h₄]
  · linarith only [hBLower, hSize, hb, hEdit, h₁, h₂, h₄]
  · obtain ⟨hBalL, hBalR⟩ := abs_le.mp hOld.2.2.2.1
    exact abs_le.mpr ⟨by linarith only [hBalL, ha, hb', hEdit, h₂, h₃, hScaleN],
      by linarith only [hBalR, ha', hb, hEdit, h₁, h₄, hScaleN]⟩
  · have hSum : ((A' \ A).card : ℝ) + ((B' \ B).card : ℝ) ≤ η * n := by
      linarith only [hEdit, h₁, h₃]
    have hPay := mul_le_mul_of_nonneg_right hSum hn₀
    have hBound := mul_le_mul_of_nonneg_right hCutScale (sq_nonneg n)
    have hMul : (η * n) * n = η * n ^ 2 := by ring
    rw [add_mul, hMul] at hPay
    rw [add_mul, add_mul] at hBound
    have hAEdges := hEdges A A'
    have hBEdges := hEdges B B'
    dsimp only [n] at hAEdges hBEdges hPay hBound
    linarith only [hAEdges, hBEdges, hPay, hCut, hBound, hOld.2.2.2.2]

/-- Editing the sides of a fixed component preserves closeness to
bipartite under explicit size and edge budgets. -/
theorem closeToBipartite_of_same_union_edit (ρ η ρ' : ℝ) (A B A' B' : Finset V)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V) (hOld : CloseToBipartite G ρ A B)
    (hNew : Disjoint A' B') (hUnion : A' ∪ B' = A ∪ B)
    (hEdit : ((A \ A').card : ℝ) + ((A' \ A).card : ℝ) +
      ((B \ B').card : ℝ) + ((B' \ B).card : ℝ) ≤ η * (Fintype.card V : ℝ))
    (hScale : ρ + η ≤ ρ')
    (hSize : (Real.sqrt ρ' + 2 * Real.sqrt ρ + η) * (Fintype.card V : ℝ) ≤ G.minDegree) :
    CloseToBipartite G ρ' A' B' := by
  apply closeToBipartite_of_edit_budget G ρ η 0 ρ' A B A' B' hρ hn hOld hNew
    (by simp [hUnion]) hEdit hScale (by simpa using hScale) hSize

/-- Small edits may also change the vertex set of the whole component.
The second edit budget pays for the change in its boundary. -/
theorem closeToBipartite_of_small_edit (ρ η ρ' : ℝ) (A B A' B' : Finset V)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V) (hOld : CloseToBipartite G ρ A B)
    (hNew : Disjoint A' B')
    (hEdit : ((A \ A').card : ℝ) + ((A' \ A).card : ℝ) +
      ((B \ B').card : ℝ) + ((B' \ B).card : ℝ) ≤ η * (Fintype.card V : ℝ))
    (hScale : ρ + 2 * η ≤ ρ')
    (hSize : (Real.sqrt ρ' + 2 * Real.sqrt ρ + η) * (Fintype.card V : ℝ) ≤ G.minDegree) :
    CloseToBipartite G ρ' A' B' := by
  have hη : 0 ≤ η := by
    apply nonneg_of_mul_nonneg_left (hEdit.trans' (by positivity))
    exact_mod_cast hn
  have hDiff (P Q R S : Finset V) : (P ∪ Q) \ (R ∪ S) ⊆ (P \ R) ∪ (Q \ S) := by
    intro v hv
    simp only [mem_union, mem_sdiff] at hv ⊢
    tauto
  have hCount (P Q R S : Finset V) :
      ((((P ∪ Q) \ (R ∪ S)).card : ℕ) : ℝ) ≤ ((P \ R).card : ℝ) + ((Q \ S).card : ℝ) := by
    exact_mod_cast (card_le_card (hDiff P Q R S)).trans (card_union_le _ _)
  have hTotal : (((A' ∪ B') \ (A ∪ B)).card : ℝ) + (((A ∪ B) \ (A' ∪ B')).card : ℝ)
      ≤ η * (Fintype.card V : ℝ) := by
    linarith only [hCount A' B' A B, hCount A B A' B', hEdit]
  have hCut := cutEdges_le_of_edit G (A ∪ B) (A' ∪ B')
  have hCut' : (cutEdges G (A' ∪ B') : ℝ) ≤ cutEdges G (A ∪ B) +
      ((((A' ∪ B') \ (A ∪ B)).card : ℝ) + (((A ∪ B) \ (A' ∪ B')).card : ℝ)) *
        (Fintype.card V : ℝ) := by
    rw [add_mul, ← add_assoc]
    exact_mod_cast hCut
  have hBudget := mul_le_mul_of_nonneg_right hTotal (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
  rw [mul_assoc, ← pow_two] at hBudget
  apply closeToBipartite_of_edit_budget G ρ η η ρ' A B A' B' hρ hn hOld hNew
    (hCut'.trans (add_le_add_right hBudget _)) hEdit (by linarith) (by linarith) hSize

end OverfullWork.KLOS
