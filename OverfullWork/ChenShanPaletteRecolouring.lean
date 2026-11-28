module

public import OverfullWork.ChenShanPaletteSubgraphColouring
public import OverfullWork.ChenShanLemma39
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset SimpleGraph MultiGraph.GeneralCopies
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem card_filter_add_sum_card_filter_of_disjoint
    {D I : Type*} [Fintype D] [Fintype I] [DecidableEq D]
    (S : I → Finset D) (hDisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (Q : D → Prop) [DecidablePred Q] :
    ((univ \ univ.biUnion S).filter Q).card +
        ∑ i, ((S i).filter Q).card = (univ.filter Q).card := by
  have hFiltered : (univ.biUnion S).filter Q = univ.biUnion (fun i => (S i).filter Q) := by
    ext x
    simp only [mem_filter, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, hQ⟩
      exact ⟨i, hi, hQ⟩
    · rintro ⟨i, hi, hQ⟩
      exact ⟨⟨i, hi⟩, hQ⟩
  have hSum : ((univ.biUnion S).filter Q).card = ∑ i, ((S i).filter Q).card := by
    rw [hFiltered, card_biUnion]
    intro i _ j _ hij
    exact (hDisj hij).mono (filter_subset _ _) (filter_subset _ _)
  rw [← hSum, ← card_union_of_disjoint]
  · rw [← filter_union, sdiff_union_of_subset (subset_univ _)]
  · exact disjoint_sdiff_self_left.mono (filter_subset _ _) (filter_subset _ _)

/-- The degrees in the chosen blocks and the complement account for
each original edge copy exactly once, even with parallel edges. -/
theorem paletteCopySubgraph_degree_add_sum_complement
    {I : Type*} [Fintype I] (M : MultiGraph V) (S : I → Finset (Copies M))
    (hDisj : Pairwise (fun i j => Disjoint (S i) (S j))) (v : V) :
    (paletteCopySubgraph M (univ \ univ.biUnion S)).degree v +
        ∑ i, (paletteCopySubgraph M (S i)).degree v = M.degree v := by
  simp_rw [paletteCopySubgraph_degree, paletteCopyDegree]
  rw [card_filter_add_sum_card_filter_of_disjoint S hDisj, ← degree_eq M v]
  unfold ShannonColouring.degree
  congr 1
  ext d
  simp only [mem_filter]

/-- Bound the total core incidence by the size and maximum degree of
the permitted support in one side of a block. -/
theorem paletteCoreDegreeSum_le_of_supported
    (G : MultiGraph V) (A block : Finset V) (a b : ℕ)
    (hZero : ∀ v ∈ A, v ∉ block → G.degree v = 0)
    (hDegree : ∀ v ∈ A ∩ block, G.degree v ≤ a)
    (hCard : (A ∩ block).card ≤ b) :
    (∑ v ∈ A, G.degree v) ≤ b*a := by
  have hSum : (∑ v ∈ A ∩ block, G.degree v) = ∑ v ∈ A, G.degree v := by
    apply sum_subset inter_subset_left
    intro v hA hOut
    exact hZero v hA (fun h => hOut (mem_inter.mpr ⟨hA, h⟩))
  rw [← hSum]
  calc
    _ ≤ ∑ _v ∈ A ∩ block, a := sum_le_sum hDegree
    _ ≤ b*a := by simpa using Nat.mul_le_mul_right a hCard

/-- Lemma 3.9 with the total core coverage bound used in (5.9).
Here the mass is an upper bound on the degree sum on one side. -/
theorem exists_balanced_palette_coloring_with_core_bound
    {k : ℕ} {G : MultiGraph V} (C : G.EdgeColoring k) (A B : Finset V) (mass : ℕ)
    (hK : 0 < k) (hAB : Disjoint A B) (hEven : Even ((A ∪ B)ᶜ.card))
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, G.degree v = k)
    (hBalance : (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v)
    (hMass : (∑ v ∈ A, G.degree v) ≤ mass) :
    ∃ D : G.EdgeColoring k,
      (∀ i, sideCount D A i = sideCount D B i) ∧
      (∀ v ∈ (A ∪ B)ᶜ, ∀ i, (D.colourGraph i).degree v = 1) ∧
      ∀ i, (sideCount D A i : ℝ) + (sideCount D B i : ℝ) ≤ 2*(mass : ℝ)/k + 4 := by
  obtain ⟨D, hBalanced, _, hCovers, hAverage⟩ :=
    exists_balanced_equitable_outside_coloring C A B hAB hEven hSat hBalance
  refine ⟨D, hBalanced, hCovers, fun i => ?_⟩
  have hKReal : 0 < (k : ℝ) := by exact_mod_cast hK
  have hAverageReal : (k : ℝ)*(sideCount D A i : ℝ) ≤
      (∑ v ∈ A, (G.degree v : ℝ)) + 2*k := by
    exact_mod_cast hAverage i
  have hMassReal : (∑ v ∈ A, (G.degree v : ℝ)) ≤ (mass : ℝ) := by exact_mod_cast hMass
  rw [← hBalanced i]
  have hScaled : (sideCount D A i : ℝ) + (sideCount D A i : ℝ) ≤
      (2*(mass : ℝ) + 4*k)/k := (le_div_iff₀ hKReal).mpr (by
    nlinarith only [hAverageReal, hMassReal])
  rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hKReal)] at hScaled
  exact hScaled

/-- Balance of the original graph and all selected blocks gives
balance of the remainder. -/
theorem paletteCopySubgraph_complement_balanced
    {I : Type*} [Fintype I] (M : MultiGraph V) (S : I → Finset (Copies M))
    (hDisj : Pairwise (fun i j => Disjoint (S i) (S j))) (A B : Finset V)
    (hOriginal : (∑ v ∈ A, M.degree v) = ∑ v ∈ B, M.degree v)
    (hSelected : ∀ i, (∑ v ∈ A, (paletteCopySubgraph M (S i)).degree v) =
      ∑ v ∈ B, (paletteCopySubgraph M (S i)).degree v) :
    (∑ v ∈ A, (paletteCopySubgraph M (univ \ univ.biUnion S)).degree v) =
      ∑ v ∈ B, (paletteCopySubgraph M (univ \ univ.biUnion S)).degree v := by
  let R := paletteCopySubgraph M (univ \ univ.biUnion S)
  have hSum (T : Finset V) : (∑ v ∈ T, R.degree v) +
      (∑ i, ∑ v ∈ T, (paletteCopySubgraph M (S i)).degree v) =
        ∑ v ∈ T, M.degree v := by
    calc
      _ = ∑ v ∈ T, (R.degree v + ∑ i, (paletteCopySubgraph M (S i)).degree v) := by
        rw [sum_add_distrib, sum_comm (s := T)]
      _ = ∑ v ∈ T, M.degree v := sum_congr rfl
        (fun v _ => paletteCopySubgraph_degree_add_sum_complement M S hDisj v)
  change (∑ v ∈ A, R.degree v) = ∑ v ∈ B, R.degree v
  have hBlocks := sum_congr (s₁ := (univ : Finset I)) rfl (fun i _ => hSelected i)
  have hLeft := hSum A
  have hRight := hSum B
  omega

/-- Recolor the selected blocks and the remainder in §5.1.4.
The input colorings can come from the retained-color criterion.
Saturation and balance of the remainder follow from the partition
of the labeled copies and the corresponding properties on the blocks. -/
theorem exists_balanced_palette_partition_recolorings
    {I : Type*} [Fintype I] (M : MultiGraph V) (S : I → Finset (Copies M))
    (A B : Finset V) (k : ℕ) (size mass : I → ℕ) (remainingMass : ℕ)
    (hDisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hAB : Disjoint A B) (hEven : Even ((A ∪ B)ᶜ.card))
    (hPositive : ∀ i, 0 < size i) (hRemaining : ∑ i, size i < k)
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, M.degree v = k)
    (hBalance : (∑ v ∈ A, M.degree v) = ∑ v ∈ B, M.degree v)
    (hBlockSat : ∀ i, ∀ v ∈ (A ∪ B)ᶜ, (paletteCopySubgraph M (S i)).degree v = size i)
    (hBlockBalance : ∀ i, (∑ v ∈ A, (paletteCopySubgraph M (S i)).degree v) =
      ∑ v ∈ B, (paletteCopySubgraph M (S i)).degree v)
    (hBlockMass : ∀ i, (∑ v ∈ A, (paletteCopySubgraph M (S i)).degree v) ≤ mass i)
    (hRemMass : (∑ v ∈ A, (paletteCopySubgraph M (univ \ univ.biUnion S)).degree v) ≤
      remainingMass)
    (hBlockColour : ∀ i, Nonempty ((paletteCopySubgraph M (S i)).EdgeColoring (size i)))
    (hRemColour : Nonempty
      ((paletteCopySubgraph M (univ \ univ.biUnion S)).EdgeColoring (k - ∑ i, size i))) :
    (∀ j, ∃ D : (paletteCopySubgraph M (S j)).EdgeColoring (size j),
      (∀ i, sideCount D A i = sideCount D B i) ∧
      (∀ v ∈ (A ∪ B)ᶜ, ∀ i, (D.colourGraph i).degree v = 1) ∧
      ∀ i, (sideCount D A i : ℝ) + (sideCount D B i : ℝ) ≤ 2*(mass j : ℝ)/size j + 4) ∧
    (∃ D : (paletteCopySubgraph M (univ \ univ.biUnion S)).EdgeColoring (k - ∑ i, size i),
      (∀ i, sideCount D A i = sideCount D B i) ∧
      (∀ v ∈ (A ∪ B)ᶜ, ∀ i, (D.colourGraph i).degree v = 1) ∧
      ∀ i, (sideCount D A i : ℝ) + (sideCount D B i : ℝ) ≤
        2*(remainingMass : ℝ)/((k - ∑ j, size j : ℕ) : ℝ) + 4) := by
  constructor
  · intro j
    obtain ⟨C⟩ := hBlockColour j
    exact exists_balanced_palette_coloring_with_core_bound C A B (mass j) (hPositive j)
      hAB hEven (hBlockSat j) (hBlockBalance j) (hBlockMass j)
  · obtain ⟨C⟩ := hRemColour
    refine exists_balanced_palette_coloring_with_core_bound C A B remainingMass
      (Nat.sub_pos_of_lt hRemaining) hAB hEven ?_
      (paletteCopySubgraph_complement_balanced M S hDisj A B hBalance hBlockBalance) hRemMass
    intro v hv
    have hPartition := paletteCopySubgraph_degree_add_sum_complement M S hDisj v
    simp_rw [hBlockSat _ v hv, hSat v hv] at hPartition
    omega

/-- If every original color meets the exceptional vertices, each
selected block saturates them with exactly the size of its palette.
The balance conclusion is for actual multigraph degree sums. -/
theorem paletteCopySubgraph_saturated_and_balanced_of_selection
    {K : Type*} [DecidableEq K] (M : MultiGraph V) (role : V → PaletteVertexRole)
    (A B block : Finset V) (P : Finset K) (colour : Copies M → K)
    (available core : Finset (Copies M))
    (hA : ∀ v, role v = .coreA ↔ v ∈ A) (hB : ∀ v, role v = .coreB ↔ v ∈ B)
    (hProper : ∀ v, Set.InjOn colour {d | v ∈ d.1})
    (hCovered : ∀ v ∈ (A ∪ B)ᶜ, ∀ j ∈ P, ∃ d, v ∈ d.1 ∧ colour d = j)
    (hSel : IsPaletteBlockSelection (ends M) role block
      (univ.filter (fun d => colour d ∈ P)) available core) :
    let G := paletteCopySubgraph M (paletteSelectedCopies (ends M) role
      (univ.filter (fun d => colour d ∈ P)) core)
    (∀ v ∈ (A ∪ B)ᶜ, G.degree v = P.card) ∧
      (∑ v ∈ A, G.degree v) = ∑ v ∈ B, G.degree v := by
  dsimp
  obtain ⟨hDegree, hBalance⟩ := paletteCopySubgraph_properties M role A B block
    (univ.filter (fun d => colour d ∈ P)) available core hA hB hSel
  refine ⟨fun v hv => ?_, hBalance⟩
  have hOutside : v ∉ A ∧ v ∉ B := by simpa using hv
  have hRole : (role v).isCore = false := by
    have hNotA := mt (hA v).mp hOutside.1
    have hNotB := mt (hB v).mp hOutside.2
    cases h : role v <;> simp_all [PaletteVertexRole.isCore]
  rw [hDegree v hRole, paletteCopySubgraph_degree]
  apply paletteCopyDegree_filter_eq_palette_card
  · intro d hd e he hEq
    exact hProper v ((incident_iff M d v).mp hd) ((incident_iff M e v).mp he) hEq
  · intro j hj
    obtain ⟨d, hd, hC⟩ := hCovered v hv j hj
    exact ⟨d, (incident_iff M d v).mpr hd, hC⟩

/-- A side count is the number of vertices of the side covered by
the matching for that color. -/
theorem sideCount_eq_card_covered {k : ℕ} {G : MultiGraph V} (D : G.EdgeColoring k)
    (T : Finset V) (i : Fin k) :
    sideCount D T i = ((T.filter (fun v => (D.colourGraph i).degree v = 1)).card : ℤ) := by
  unfold sideCount
  have hCard : (∑ _v ∈ T.filter (fun v => (D.colourGraph i).degree v = 1), (1 : ℤ)) =
      ((T.filter (fun v => (D.colourGraph i).degree v = 1)).card : ℤ) := by simp
  rw [← hCard, sum_filter]
  apply sum_congr rfl
  intro v _
  have h := D.colourGraph_degree_le_one i v
  by_cases hOne : (D.colourGraph i).degree v = 1
  · simp [hOne]
  · have hZero : (D.colourGraph i).degree v = 0 := by omega
    simp [hZero]

/-- Disjoint palettes leave exactly the number of unused colors
required by the remainder's degrees at exceptional vertices. -/
theorem palette_complement_card {I : Type*} [Fintype I] {k : ℕ}
    (P : I → Finset (Fin k)) (hDisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ((univ.biUnion P)ᶜ).card = k - ∑ i, (P i).card := by
  rw [card_compl, Fintype.card_fin, card_biUnion]
  exact fun _ _ _ _ hij => hDisj hij

omit [Fintype V] in
/-- Connect the selected rows of indexed copies to the actual degree
into the core. -/
theorem paletteCopySubgraph_degreeInto_eq_row
    (M : MultiGraph V) (S : Finset (Copies M)) (role : V → PaletteVertexRole)
    (U : Finset V) (hU : ∀ u, (role u).isCore = true ↔ u ∈ U) (v : V) :
    (paletteCopySubgraph M S).degreeInto U v = (paletteCoreRow (ends M) role S v).card := by
  let f : V ↪ Sym2 V := ⟨fun u => s(v,u), by
    intro u w huv
    rcases Sym2.eq_iff.mp huv with h | h
    · exact h.2
    · exact h.2.trans h.1⟩
  calc
    _ = ∑ e ∈ U.map f, (S.filter (fun d => d.1 = e)).card := by
      rw [sum_map]
      rfl
    _ = _ := by
      rw [sum_card_fiberwise_eq_card_filter S (U.map f) Sigma.fst]
      unfold paletteCoreRow
      congr 1
      ext d
      simp only [mem_filter, mem_map, hU]
      refine and_congr_right (fun _ => ?_)
      constructor
      · rintro ⟨u, hu, he⟩
        have h := Sym2.eq_iff.mp ((endpoints_eq d.1).trans he.symm)
        rcases h with h | h
        · exact Or.inl ⟨h.1, h.2 ▸ hu⟩
        · exact Or.inr ⟨h.2, h.1 ▸ hu⟩
      · rintro (⟨hv, hu⟩ | ⟨hv, hu⟩)
        · refine ⟨_, hu, ?_⟩
          exact (endpoints_eq d.1).symm ▸ congrArg (fun x => s(x,(ends M d).2)) hv.symm
        · refine ⟨_, hu, ?_⟩
          change s(v,(ends M d).1) = d.1
          rw [← endpoints_eq d.1, Sym2.eq_swap]
          change s((ends M d).1,v) = s((ends M d).1,(ends M d).2)
          rw [hv]

/-- Removing the selected blocks loses at most their total degree
budget from an exceptional vertex's core row. -/
theorem paletteCopySubgraph_degreeInto_complement_lower
    {I : Type*} [Fintype I] (M : MultiGraph V) (S : I → Finset (Copies M))
    (hDisj : Pairwise (fun i j => Disjoint (S i) (S j))) (U : Finset V)
    (v : V) (size : I → ℕ) (hSize : ∀ i, (paletteCopySubgraph M (S i)).degree v ≤ size i) :
    M.degreeInto U v ≤
      (paletteCopySubgraph M (univ \ univ.biUnion S)).degreeInto U v + ∑ i, size i := by
  let R := paletteCopySubgraph M (univ \ univ.biUnion S)
  have hPartition (u : V) : R.mult s(v,u) +
      ∑ i, (paletteCopySubgraph M (S i)).mult s(v,u) = M.mult s(v,u) := by
    simp only [R, paletteCopySubgraph]
    rw [card_filter_add_sum_card_filter_of_disjoint S hDisj, edge_fibre_card]
  have hSum : R.degreeInto U v + ∑ i, (paletteCopySubgraph M (S i)).degreeInto U v =
      M.degreeInto U v := by
    unfold MultiGraph.degreeInto
    rw [sum_comm (s := (univ : Finset I)), ← sum_add_distrib]
    exact sum_congr rfl fun u _ => hPartition u
  rw [← hSum]
  exact Nat.add_le_add_left (sum_le_sum fun i _ =>
    (Nat.le_add_right _ _ |>.trans_eq ((paletteCopySubgraph M (S i)).degreeInto_add_compl U v)).trans
      (hSize i)) _

end OverfullWork.ChenShan
