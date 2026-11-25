module

public import OverfullWork.KLOSRefinement
public import OverfullWork.LowSetEdgePreprocessing

@[expose] public section

/-! The initial vertex deletion in Kühn–Lo–Osthus–Staden, Lemma 4.11. -/
namespace OverfullWork.KLOS

open SimpleGraph Finset PrunedCore RobustExpansion
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices of a part whose external degree reaches the square-root threshold. -/
noncomputable def boundaryExceptions (ρ : ℝ) (U : Finset V) : Finset V :=
  U.filter fun v => Real.sqrt ρ * (Fintype.card V : ℝ) ≤ (neighboursIn G Uᶜ v : ℝ)

/-- The cut bound pays for all vertices omitted in the first step of Lemma 4.11.
Each remaining vertex loses at most twice the square-root threshold. -/
theorem trim_sparse_part (ρ : ℝ) (U : Finset V)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V) (hU : IsSparseComponent G ρ U) :
    let X := boundaryExceptions G ρ U
    (X.card : ℝ) ≤ Real.sqrt ρ * (Fintype.card V : ℝ) ∧
      ∀ v ∈ U \ X, (G.degree v : ℝ) - 2 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤
        (neighboursIn G (U \ X) v : ℝ) := by
  intro X
  let n := (Fintype.card V : ℝ)
  let t := Real.sqrt ρ * n
  have hX : X ⊆ U := filter_subset _ _
  have ht : 0 < t := mul_pos (Real.sqrt_pos.mpr hρ) (by dsimp [n]; exact_mod_cast hn)
  have hMass : t * (X.card : ℝ) ≤ (incidences G Uᶜ X : ℝ) := by
    unfold incidences
    push_cast
    calc
      _ = ∑ _ ∈ X, t := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun v hv => (mem_filter.mp hv).2
  have hCut : (incidences G Uᶜ X : ℝ) ≤ (OddCutDeficit.cutEdges G U : ℝ) := by
    rw [← incidences_compl_self, incidences_comm G U Uᶜ]
    exact_mod_cast incidences_mono G (Subset.rfl : Uᶜ ⊆ Uᶜ) hX
  have htSq : t * t = ρ * n ^ 2 := by
    rw [← pow_two]
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt hρ.le]
  have hCount : (X.card : ℝ) ≤ t := by
    apply (mul_le_mul_iff_of_pos_left ht).mp
    exact (hMass.trans (hCut.trans hU.2)).trans_eq htSq.symm
  refine ⟨hCount, ?_⟩
  intro v hv
  have hOutside : (neighboursIn G Uᶜ v : ℝ) < t := by
    exact lt_of_not_ge (fun h => (mem_sdiff.mp hv).2
      (mem_filter.mpr ⟨(mem_sdiff.mp hv).1, h⟩))
  have hComplement : (U \ X)ᶜ = Uᶜ ∪ X := by
    ext w
    simp only [mem_compl, mem_sdiff, mem_union]
    have := @hX w
    tauto
  have hUnion : neighboursIn G (Uᶜ ∪ X) v ≤ neighboursIn G Uᶜ v + X.card := by
    simp only [neighboursIn_eq_filter_card, filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add_left (card_filter_le _ _) _)
  have hAdd := LowSetEdgePreprocessing.neighboursIn_add_compl G (U \ X) v
  rw [hComplement] at hAdd
  have hNat : G.degree v ≤ neighboursIn G (U \ X) v + neighboursIn G Uᶜ v + X.card := by
    omega
  have hReal : (G.degree v : ℝ) ≤ (neighboursIn G (U \ X) v : ℝ) +
      (neighboursIn G Uᶜ v : ℝ) + X.card := by exact_mod_cast hNat
  dsimp only [t, n] at hCount hOutside
  linarith only [hCount, hOutside, hReal]

section Reassignment

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The part whose label is `i` in the assignment `f`. -/
def assignmentPart (f : V → I) (i : I) : Finset V := univ.filter (fun v => f v = i)

def internalAdjacency (f : V → I) (v w : V) : ℕ :=
  if G.Adj v w ∧ f v = f w then 1 else 0

/-- The number of directed incidences remaining inside parts. Maximizing
this score is equivalent to minimizing the total boundary. -/
def internalScore (f : V → I) : ℕ := ∑ v : V, ∑ w : V, internalAdjacency G f v w

omit [Fintype V] [DecidableEq V] [Fintype I] in
private theorem internalAdjacency_comm (f : V → I) (v w : V) :
    internalAdjacency G f v w = internalAdjacency G f w v := by
  simp only [internalAdjacency, G.adj_comm, eq_comm]

omit [Fintype V] [DecidableEq V] [Fintype I] in
private theorem internalAdjacency_self (f : V → I) (v : V) :
    internalAdjacency G f v v = 0 := by simp [internalAdjacency]

omit [Fintype I] in
private theorem sum_internalAdjacency (f : V → I) (v : V) :
    (∑ w : V, internalAdjacency G f v w) = neighboursIn G (assignmentPart f (f v)) v := by
  rw [neighboursIn_eq_filter_card]
  simp only [assignmentPart, filter_filter, card_filter]
  apply sum_congr rfl
  intro w _
  simp only [internalAdjacency, and_comm, eq_comm]

omit [Fintype I] in
private theorem internalScore_split (f : V → I) (v : V) :
    internalScore G f =
      (∑ x ∈ univ.erase v, ∑ y ∈ univ.erase v, internalAdjacency G f x y) +
      2 * neighboursIn G (assignmentPart f (f v)) v := by
  have hRow (x : V) : (∑ y : V, internalAdjacency G f x y) =
      (∑ y ∈ univ.erase v, internalAdjacency G f x y) + internalAdjacency G f x v :=
    (sum_erase_add univ _ (mem_univ v)).symm
  have hColumn : (∑ x ∈ univ.erase v, internalAdjacency G f x v) =
      (∑ y : V, internalAdjacency G f v y) := by
    simp_rw [internalAdjacency_comm G f _ v]
    rw [hRow v, internalAdjacency_self, Nat.add_zero]
  unfold internalScore
  rw [← sum_erase_add univ (fun x => ∑ y : V, internalAdjacency G f x y) (mem_univ v)]
  have hSplit : (∑ x ∈ univ.erase v, ∑ y : V, internalAdjacency G f x y) =
      (∑ x ∈ univ.erase v, ∑ y ∈ univ.erase v, internalAdjacency G f x y) +
      (∑ x ∈ univ.erase v, internalAdjacency G f x v) := by
    simp_rw [hRow]
    exact sum_add_distrib
  rw [hSplit, hColumn, sum_internalAdjacency]
  omega

omit [Fintype I] in
private theorem neighboursIn_update_part (f : V → I) (v : V) (i : I) :
    neighboursIn G (assignmentPart (Function.update f v i) i) v =
      neighboursIn G (assignmentPart f i) v := by
  unfold neighboursIn
  congr 1
  ext w
  by_cases h : w = v
  · subst w
    simp
  · simp [assignmentPart, Function.update_of_ne h]

omit [Fintype I] in
private theorem internalScore_update (f : V → I) (v : V) (i : I) :
    internalScore G (Function.update f v i) + 2 * neighboursIn G (assignmentPart f (f v)) v =
      internalScore G f + 2 * neighboursIn G (assignmentPart f i) v := by
  rw [internalScore_split G (Function.update f v i) v, internalScore_split G f v,
    Function.update_self, neighboursIn_update_part]
  have hRest :
      (∑ x ∈ univ.erase v, ∑ y ∈ univ.erase v, internalAdjacency G (Function.update f v i) x y) =
      (∑ x ∈ univ.erase v, ∑ y ∈ univ.erase v, internalAdjacency G f x y) := by
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro y hy
    simp only [internalAdjacency, Function.update_of_ne (mem_erase.mp hx).1,
      Function.update_of_ne (mem_erase.mp hy).1]
  omega

/-- Internal incidences and the sum of the part boundaries account for
the full degree sum. -/
theorem internalScore_add_total_boundary (f : V → I) :
    internalScore G f + (∑ i : I, OddCutDeficit.cutEdges G (assignmentPart f i)) =
      ∑ v : V, G.degree v := by
  have hBound : (∑ i : I, OddCutDeficit.cutEdges G (assignmentPart f i)) =
      ∑ v : V, neighboursIn G (assignmentPart f (f v))ᶜ v := by
    rw [← sum_fiberwise univ f (fun v => neighboursIn G (assignmentPart f (f v))ᶜ v)]
    apply sum_congr rfl
    intro i _
    rw [← incidences_compl_self, incidences_comm G (assignmentPart f i)]
    unfold incidences
    apply sum_congr rfl
    intro v hv
    exact congrArg (fun j => neighboursIn G (assignmentPart f j)ᶜ v) (mem_filter.mp hv).2.symm
  rw [hBound]
  unfold internalScore
  simp_rw [sum_internalAdjacency]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun v _ => LowSetEdgePreprocessing.neighboursIn_add_compl G (assignmentPart f (f v)) v

/-- Maximize the number of internal incidences while fixing the labels
of vertices outside `X`. Every vertex allowed to move then has as many
neighbours in its assigned part as in any other part. -/
theorem exists_optimal_reassignment (initial : V → I) (X : Finset V) :
    ∃ f : V → I, (∀ v ∉ X, f v = initial v) ∧
      internalScore G initial ≤ internalScore G f ∧
      ∀ v ∈ X, ∀ i : I, neighboursIn G (assignmentPart f i) v ≤
        neighboursIn G (assignmentPart f (f v)) v := by
  classical
  let F : Finset (V → I) := univ.filter fun f => ∀ v ∉ X, f v = initial v
  have hInitial : initial ∈ F := mem_filter.mpr ⟨mem_univ _, fun _ _ => rfl⟩
  obtain ⟨f, hf, hMax⟩ := F.exists_max_image (internalScore G) ⟨initial, hInitial⟩
  have hFixed := (mem_filter.mp hf).2
  refine ⟨f, hFixed, hMax initial hInitial, ?_⟩
  intro v hv i
  let f' := Function.update f v i
  have hf' : f' ∈ F := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro w hw
    have hne : w ≠ v := fun h => hw (h ▸ hv)
    exact (Function.update_of_ne hne _ _).trans (hFixed w hw)
  have hScore := hMax f' hf'
  have hMove := internalScore_update G f v i
  change internalScore G f' + _ = _ at hMove
  omega

/-- Lemma 4.11 for a partition represented by its part labels and with
an explicit error budget `η`. The four conclusions give the size of the
move, a sparse boundary, local degree dominance, and a high-degree core. -/
theorem adjust_regular_partition (initial : V → I) (D : ℕ) (hRegular : ∀ v, G.degree v = D)
    (ρ η : ℝ) (hρ : 0 < ρ) (hn : 0 < Fintype.card V)
    (hSparse : ∀ i, IsSparseComponent G ρ (assignmentPart initial i))
    (hMoveScale : (Fintype.card I : ℝ) * Real.sqrt ρ ≤ η)
    (hCutScale : (Fintype.card I : ℝ) * ρ ≤ η)
    (hSize : (Real.sqrt η + 2 * Real.sqrt ρ) * (Fintype.card V : ℝ) ≤ D)
    (hDominance : 4 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ D) :
    ∃ f : V → I,
      (∀ i, let U := assignmentPart initial i; let W := assignmentPart f i
        (((U \ W) ∪ (W \ U)).card : ℝ) ≤ η * (Fintype.card V : ℝ)) ∧
      (∀ i, IsSparseComponent G η (assignmentPart f i)) ∧
      (∀ v j, neighboursIn G (assignmentPart f j) v ≤ neighboursIn G (assignmentPart f (f v)) v) ∧
      ∀ i, let W := assignmentPart f i
        ((W.filter fun v => (neighboursIn G W v : ℝ) <
          (D : ℝ) - 2 * Real.sqrt ρ * (Fintype.card V : ℝ)).card : ℝ) ≤ η * (Fintype.card V : ℝ) := by
  let U := assignmentPart initial
  let E := fun i => boundaryExceptions G ρ (U i)
  let X := (univ : Finset I).biUnion E
  let n := (Fintype.card V : ℝ)
  have hn₀ : 0 ≤ n := by positivity
  have hTrim i := trim_sparse_part G ρ (U i) hρ hn (hSparse i)
  have hEU (i : I) : E i ⊆ U i := filter_subset _ _
  have hX : (X.card : ℝ) ≤ η * n := by
    have h : (X.card : ℝ) ≤ ∑ i : I, ((E i).card : ℝ) := by
      exact_mod_cast (card_biUnion_le : X.card ≤ ∑ i : I, (E i).card)
    calc
      _ ≤ _ := h
      _ ≤ ∑ _ : I, Real.sqrt ρ * n := sum_le_sum fun i _ => (hTrim i).1
      _ = ((Fintype.card I : ℝ) * Real.sqrt ρ) * n := by simp [mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right hMoveScale hn₀
  obtain ⟨f, hFixed, hScore, hOpt⟩ := exists_optimal_reassignment G initial X
  let W := assignmentPart f
  have hRemoved (i : I) {v : V} (hv : v ∈ U i \ E i) : v ∉ X := by
    intro hvX
    obtain ⟨j, _, hvj⟩ := mem_biUnion.mp hvX
    have hi : initial v = i := (mem_filter.mp (mem_sdiff.mp hv).1).2
    have hj : initial v = j := (mem_filter.mp (hEU j hvj)).2
    have hji : j = i := hj.symm.trans hi
    exact (mem_sdiff.mp hv).2 (hji ▸ hvj)
  have hKept (i : I) : U i \ E i ⊆ W i := by
    intro v hv
    apply mem_filter.mpr
    exact ⟨mem_univ _, (hFixed v (hRemoved i hv)).trans (mem_filter.mp (mem_sdiff.mp hv).1).2⟩
  have hHigh (i : I) (v : V) (hv : v ∈ U i \ E i) :
      (D : ℝ) - 2 * Real.sqrt ρ * n ≤ (neighboursIn G (W i) v : ℝ) := by
    have h := (hTrim i).2 v hv
    rw [hRegular] at h
    exact h.trans (by exact_mod_cast neighboursIn_mono G (hKept i) v)
  have hBoundary : ∑ i : I, OddCutDeficit.cutEdges G (W i) ≤
      ∑ i : I, OddCutDeficit.cutEdges G (U i) := by
    have hOld := internalScore_add_total_boundary G initial
    have hNew := internalScore_add_total_boundary G f
    dsimp only [W, U]
    omega
  have hBoundaryReal (i : I) : (OddCutDeficit.cutEdges G (W i) : ℝ) ≤ η * n ^ 2 := by
    have hi : OddCutDeficit.cutEdges G (W i) ≤ ∑ j : I, OddCutDeficit.cutEdges G (W j) :=
      single_le_sum (f := fun j => OddCutDeficit.cutEdges G (W j)) (fun _ _ => Nat.zero_le _) (mem_univ i)
    have hi' : (OddCutDeficit.cutEdges G (W i) : ℝ) ≤
        ∑ j : I, (OddCutDeficit.cutEdges G (U j) : ℝ) := by exact_mod_cast hi.trans hBoundary
    calc
      _ ≤ _ := hi'
      _ ≤ ∑ _ : I, ρ * n ^ 2 := sum_le_sum fun j _ => (hSparse j).2
      _ = ((Fintype.card I : ℝ) * ρ) * n ^ 2 := by simp [mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCutScale (sq_nonneg n)
  have : Nonempty V := Fintype.card_pos_iff.mp hn
  have hMin : (D : ℝ) ≤ G.minDegree := by
    exact_mod_cast G.le_minDegree_of_forall_le_degree D (fun v => (hRegular v).ge)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro i
    have h : ((U i \ W i) ∪ (W i \ U i)) ⊆ X := by
      intro v hv
      by_contra hNot
      have he : v ∈ U i ↔ v ∈ W i := by simp [U, W, assignmentPart, hFixed v hNot]
      rcases mem_union.mp hv with hv | hv
      · exact (mem_sdiff.mp hv).2 (he.mp (mem_sdiff.mp hv).1)
      · exact (mem_sdiff.mp hv).2 (he.mpr (mem_sdiff.mp hv).1)
    exact (by exact_mod_cast card_le_card h : ((((U i \ W i) ∪ (W i \ U i)).card : ℝ)) ≤ X.card).trans hX
  · intro i
    refine ⟨?_, hBoundaryReal i⟩
    have hCore := sparseComponent_card_lower G ρ (U i) hρ hn (hSparse i)
    have hCount : (((U i \ E i).card : ℝ)) + ((E i).card : ℝ) = (U i).card := by
      exact_mod_cast card_sdiff_add_card_eq_card (hEU i)
    have hInside : (((U i \ E i).card : ℝ)) ≤ (W i).card := by exact_mod_cast card_le_card (hKept i)
    have hTrimCount := (hTrim i).1
    linarith only [hCore, hCount, hInside, hTrimCount, hMin, hSize]
  · intro v j
    by_cases hv : v ∈ X
    · exact hOpt v hv j
    · by_cases hj : j = f v
      · simp [hj]
      have hf : f v = initial v := hFixed v hv
      have hc : v ∈ U (f v) \ E (f v) := by
        apply mem_sdiff.mpr
        refine ⟨mem_filter.mpr ⟨mem_univ _, hf.symm⟩, ?_⟩
        intro he
        exact hv (mem_biUnion.mpr ⟨f v, mem_univ _, he⟩)
      have hOther : W j ⊆ (W (f v))ᶜ := by
        intro w hw
        apply mem_compl.mpr
        intro h
        exact hj ((mem_filter.mp hw).2.symm.trans (mem_filter.mp h).2)
      have hAdd := LowSetEdgePreprocessing.neighboursIn_add_compl G (W (f v)) v
      have hAddR : (neighboursIn G (W (f v)) v : ℝ) +
          (neighboursIn G (W (f v))ᶜ v : ℝ) = D := by rw [← Nat.cast_add, hAdd, hRegular]
      have hHigh' := hHigh (f v) v hc
      have hMon : (neighboursIn G (W j) v : ℝ) ≤ (neighboursIn G (W (f v))ᶜ v : ℝ) := by
        exact_mod_cast neighboursIn_mono G hOther v
      exact_mod_cast (show (neighboursIn G (W j) v : ℝ) ≤ (neighboursIn G (W (f v)) v : ℝ) by
        linarith only [hHigh', hMon, hAddR, hDominance])
  · intro i
    have h : (W i).filter (fun v => (neighboursIn G (W i) v : ℝ) <
        (D : ℝ) - 2 * Real.sqrt ρ * (Fintype.card V : ℝ)) ⊆ X := by
      intro v hv
      by_contra hNot
      obtain ⟨hvW, hvLow⟩ := mem_filter.mp hv
      have hvU := (hFixed v hNot).symm.trans (mem_filter.mp hvW).2
      have hvCore : v ∈ U i \ E i := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hvU⟩,
        fun h => hNot (mem_biUnion.mpr ⟨i, mem_univ _, h⟩)⟩
      exact (not_lt_of_ge (hHigh i v hvCore)) hvLow
    exact (by exact_mod_cast card_le_card h : (((W i).filter _).card : ℝ) ≤ X.card).trans hX

/-- Use the parts of the refinement partition as labels for Lemma 4.11. -/
theorem exists_assignment_of_sparsePartition {ρ : ℝ} (P : SparsePartition G ρ) :
    ∃ initial : V → ↥P.parts, ∀ i : ↥P.parts, assignmentPart initial i = i.val := by
  have hPart (v : V) : ∃ i : ↥P.parts, v ∈ i.val := by
    have hv : v ∈ P.parts.biUnion id := by rw [P.cover]; exact mem_univ v
    obtain ⟨U, hU, hvU⟩ := mem_biUnion.mp hv
    exact ⟨⟨U, hU⟩, hvU⟩
  choose initial hInitial using hPart
  refine ⟨initial, ?_⟩
  intro i
  ext v
  simp only [assignmentPart, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    rw [← h]
    exact hInitial v
  · intro hv
    apply Subtype.ext
    by_contra h
    exact Finset.disjoint_left.mp
      (P.disjoint (initial v).val (initial v).property i.val i.property h) (hInitial v) hv

/-- Apply the adjustment of Lemma 4.11 directly to the partition produced
by refinement. The labels retain the identity of every original part. -/
theorem adjust_sparsePartition {ρ : ℝ} (P : SparsePartition G ρ)
    (D : ℕ) (hRegular : ∀ v, G.degree v = D) (η : ℝ)
    (hρ : 0 < ρ) (hn : 0 < Fintype.card V)
    (hMoveScale : (P.parts.card : ℝ) * Real.sqrt ρ ≤ η)
    (hCutScale : (P.parts.card : ℝ) * ρ ≤ η)
    (hSize : (Real.sqrt η + 2 * Real.sqrt ρ) * (Fintype.card V : ℝ) ≤ D)
    (hDominance : 4 * Real.sqrt ρ * (Fintype.card V : ℝ) ≤ D) :
    ∃ f : V → ↥P.parts,
      (∀ i, let W := assignmentPart f i
        (((i.val \ W) ∪ (W \ i.val)).card : ℝ) ≤ η * (Fintype.card V : ℝ)) ∧
      (∀ i, IsSparseComponent G η (assignmentPart f i)) ∧
      (∀ v j, neighboursIn G (assignmentPart f j) v ≤ neighboursIn G (assignmentPart f (f v)) v) ∧
      ∀ i, let W := assignmentPart f i
        ((W.filter fun v => (neighboursIn G W v : ℝ) <
          (D : ℝ) - 2 * Real.sqrt ρ * (Fintype.card V : ℝ)).card : ℝ) ≤ η * (Fintype.card V : ℝ) := by
  obtain ⟨initial, hInitial⟩ := exists_assignment_of_sparsePartition G P
  have hSparse (i : ↥P.parts) : IsSparseComponent G ρ (assignmentPart initial i) := by
    rw [hInitial]
    exact P.sparse i.val i.property
  obtain ⟨f, hEdit, hParts, hLocal, hCore⟩ :=
    adjust_regular_partition G initial D hRegular ρ η hρ hn hSparse
      (by simpa using hMoveScale) (by simpa using hCutScale) hSize hDominance
  exact ⟨f, fun i => by simpa only [hInitial i] using hEdit i, hParts, hLocal, hCore⟩

/-- The degree bound in Lemma 4.11(iii), expressed without division. -/
theorem degree_le_card_mul_of_part_dominance (f : V → I) (v : V)
    (h : ∀ i, neighboursIn G (assignmentPart f i) v ≤
      neighboursIn G (assignmentPart f (f v)) v) :
    G.degree v ≤ Fintype.card I * neighboursIn G (assignmentPart f (f v)) v := by
  have hSum : (∑ i : I, neighboursIn G (assignmentPart f i) v) = G.degree v := by
    have hFiber := sum_fiberwise (G.neighborFinset v) f (fun _ => (1 : ℕ))
    simp only [sum_const, nsmul_eq_mul, mul_one, card_neighborFinset_eq_degree] at hFiber
    simpa [neighboursIn, assignmentPart] using hFiber
  rw [← hSum]
  calc
    _ ≤ ∑ _ : I, neighboursIn G (assignmentPart f (f v)) v := sum_le_sum fun i _ => h i
    _ = _ := by simp

end Reassignment

/-- The maximum-cut reassignment step for a bipartition of `U`. Labels
outside the move set remain fixed, and degrees are measured inside `U`. -/
theorem exists_optimal_bipartition_reassignment (U X : Finset V) (initial : V → Bool) :
    ∃ f : V → Bool, (∀ v ∉ X, f v = initial v) ∧
      ∀ v ∈ X, v ∈ U →
        neighboursIn G (U ∩ assignmentPart f (f v)) v ≤
          neighboursIn G (U ∩ assignmentPart f (!(f v))) v := by
  classical
  let H : SimpleGraph V := {
    Adj := fun v w => G.Adj v w ∧ v ∈ U ∧ w ∈ U
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
    loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩ }
  let : DecidableRel H.Adj := fun v w => Classical.propDecidable (H.Adj v w)
  have hNeighbours (f : V → Bool) (v : V) (hv : v ∈ U) (i : Bool) :
      neighboursIn H (assignmentPart f i) v = neighboursIn G (U ∩ assignmentPart f i) v := by
    simp only [neighboursIn_eq_filter_card]
    congr 1
    ext w
    simp [H, hv, and_assoc, and_left_comm, and_comm]
  let F : Finset (V → Bool) := univ.filter fun f => ∀ v ∉ X, f v = initial v
  have hInitial : initial ∈ F := mem_filter.mpr ⟨mem_univ _, fun _ _ => rfl⟩
  obtain ⟨f, hf, hMin⟩ := F.exists_min_image (internalScore H) ⟨initial, hInitial⟩
  have hFixed := (mem_filter.mp hf).2
  refine ⟨f, hFixed, ?_⟩
  intro v hv hvU
  let f' := Function.update f v (!(f v))
  have hf' : f' ∈ F := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro w hw
    have hne : w ≠ v := fun h => hw (h ▸ hv)
    exact (Function.update_of_ne hne _ _).trans (hFixed w hw)
  have hScore := hMin f' hf'
  have hMove := internalScore_update H f v (!(f v))
  change internalScore H f' + _ = _ at hMove
  rw [← hNeighbours f v hvU, ← hNeighbours f v hvU]
  omega

/-- If each fixed vertex already has at least half its neighbours in the
opposite fixed side, optimizing the movable vertices gives dominance on
both sides for every vertex of the component. -/
theorem exists_bipartition_with_cross_dominance (U X : Finset V) (initial : V → Bool)
    (hCore : ∀ v ∈ U, v ∉ X →
      neighboursIn G U v ≤ 2 * neighboursIn G ((U \ X) ∩ assignmentPart initial (!(initial v))) v) :
    ∃ f : V → Bool, (∀ v ∉ X, f v = initial v) ∧
      ∀ v ∈ U, neighboursIn G (U ∩ assignmentPart f (f v)) v ≤
        neighboursIn G (U ∩ assignmentPart f (!(f v))) v := by
  obtain ⟨f, hFixed, hMoved⟩ := exists_optimal_bipartition_reassignment G U X initial
  refine ⟨f, hFixed, ?_⟩
  intro v hvU
  by_cases hvX : v ∈ X
  · exact hMoved v hvX hvU
  · let A := U ∩ assignmentPart f (f v)
    let B := U ∩ assignmentPart f (!(f v))
    have hAB : A ∪ B = U := by
      ext w
      simp only [A, B, assignmentPart, mem_union, mem_inter, mem_filter, mem_univ, true_and]
      cases f v <;> cases f w <;> simp
    have hDisjoint : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro w hwA hwB
      have ha := (mem_filter.mp (mem_inter.mp hwA).2).2
      have hb := (mem_filter.mp (mem_inter.mp hwB).2).2
      have h := ha.symm.trans hb
      cases f v <;> simp at h
    have hSub : (U \ X) ∩ assignmentPart initial (!(initial v)) ⊆ B := by
      intro w hw
      obtain ⟨hwCore, hwSide⟩ := mem_inter.mp hw
      obtain ⟨hwU, hwX⟩ := mem_sdiff.mp hwCore
      exact mem_inter.mpr ⟨hwU, mem_filter.mpr ⟨mem_univ _,
        (hFixed w hwX).trans ((mem_filter.mp hwSide).2.trans
          (congrArg Bool.not (hFixed v hvX).symm))⟩⟩
    have hOpp := neighboursIn_mono G hSub v
    have hTotal : neighboursIn G U v = neighboursIn G A v + neighboursIn G B v := by
      rw [← hAB]
      simp only [neighboursIn_eq_filter_card, filter_union]
      exact card_union_of_disjoint (hDisjoint.mono (filter_subset _ _) (filter_subset _ _))
    have hFixedHalf := hCore v hvU hvX
    change neighboursIn G A v ≤ neighboursIn G B v
    omega

end OverfullWork.KLOS
