module

public import OverfullWork.ChenShanPaletteBlockSelection
public import OverfullWork.ChenShanExceptionalRepresentatives
public import OverfullWork.GeneralCopies
public import OverfullWork.MultigraphCuts
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset MultiGraph.GeneralCopies
open scoped Classical

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq U]

/-- The induced side of Rext in the coordinates of the block sampler.
Vertices outside that side have zero multiplicity. -/
noncomputable def rextInternalSide (M : MultiGraph U) (core : W ↪ U) (S : Finset W) :
    MultiGraph W :=
  (⟨fun e => M.mult (Sym2.map core e), fun _ he => M.loopless _ he.map⟩ : MultiGraph W).restrict S

/-- Index the capacity data by the true internal edge copies. Each
exceptional row records multiplicities into the designated core side. -/
noncomputable def rextPaletteCapacityInput (M : MultiGraph U) (core : W ↪ U)
    (S : Finset W) (Z : Finset U) :
    PaletteBlockCapacityInput W U (Copies (rextInternalSide M core S)) where
  left e := (ends (rextInternalSide M core S) e).1
  right e := (ends (rextInternalSide M core S) e).2
  exceptional := Z
  weight z w := if w ∈ S then M.mult s(z,core w) else 0

omit [Fintype U] [DecidableEq U] in
private theorem rextSideDegree (M : MultiGraph U) (core : W ↪ U) (S : Finset W) (w : W) :
    (rextInternalSide M core S).degree w =
      if w ∈ S then M.degreeInto (S.map core) (core w) else 0 := by
  rw [rextInternalSide, MultiGraph.degree_restrict]
  congr 1
  simp only [MultiGraph.degreeInto, sum_map, Sym2.map_mk]

omit [Fintype U] [DecidableEq U] in
private theorem rextInternalSide_incidence_eq (M : MultiGraph U) (core : W ↪ U)
    (S : Finset W) (w : W) :
    internalEdgeIncidences
      (fun e => (ends (rextInternalSide M core S) e).1)
      (fun e => (ends (rextInternalSide M core S) e).2) w =
    ((rextInternalSide M core S).degree w : ℝ) := by
  rw [← MultiGraph.GeneralCopies.degree_eq]
  unfold internalEdgeIncidences ShannonColouring.degree
  rw [card_eq_sum_ones, sum_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro e _
  have hne := MultiGraph.GeneralCopies.loopless (rextInternalSide M core S) e
  unfold eventIndicator
  by_cases h₁ : (ends (rextInternalSide M core S) e).1 = w
  · have h₂ : (ends (rextInternalSide M core S) e).2 ≠ w :=
      fun h => hne (h₁.trans h.symm)
    simp [h₁,h₂]
  · by_cases h₂ : (ends (rextInternalSide M core S) e).2 = w <;> simp [h₁,h₂]

omit [Fintype U] [DecidableEq U] in
/-- The row sums coincide with the degree into the specified side. -/
theorem rextPaletteCapacityInput_weight_sum (M : MultiGraph U) (core : W ↪ U)
    (S : Finset W) (Z : Finset U) (z : U) :
    (∑ w, (rextPaletteCapacityInput M core S Z).weight z w) =
      (M.degreeInto (S.map core) z:ℝ) := by
  simp only [rextPaletteCapacityInput, MultiGraph.degreeInto, Nat.cast_sum, sum_map]
  rw [← sum_filter]
  congr 1
  exact eq_of_subset_of_card_le (by intro w hw; exact (mem_filter.mp hw).2)
    (card_le_card fun w hw => mem_filter.mpr ⟨mem_univ _,hw⟩)

omit [Fintype U] in
/-- The degree budget in the capacity test follows from the actual
degree in Rext into the chosen side and its opposite exceptional rows. -/
theorem rextPaletteCapacityInput_degree_bound (M : MultiGraph U) (core : W ↪ U)
    (S : Finset W) (Z : Finset U) (a : ℝ) (ha : 0 ≤ a)
    (hDisj : Disjoint (S.map core) Z)
    (hDegree : ∀ w ∈ S, (M.degreeInto (S.map core ∪ Z) (core w):ℝ) ≤ a) :
    ∀ w, internalEdgeIncidences (rextPaletteCapacityInput M core S Z).left
      (rextPaletteCapacityInput M core S Z).right w +
      (∑ z ∈ Z, (rextPaletteCapacityInput M core S Z).weight z w) ≤ a := by
  intro w
  simp only [rextPaletteCapacityInput, rextInternalSide_incidence_eq, rextSideDegree]
  by_cases hw : w ∈ S
  · simp only [ite_eq_left hw]
    have h := hDegree w hw
    simp only [MultiGraph.degreeInto, sum_union hDisj, Nat.cast_add, Nat.cast_sum] at h ⊢
    simpa only [Sym2.eq_swap] using h
  · simpa only [ite_eq_right hw, Nat.cast_zero, sum_const_zero, zero_add] using ha

omit [Fintype U] in
/-- The internal-copy and exceptional-incidence tests come directly
from the residual multigraph, including the palette floor bounds. -/
theorem rextPaletteCapacityInput_admissible (M : MultiGraph U) (core : W ↪ U)
    (S : Finset W) (Z : Finset U) (p fraction a : ℝ) (c : U → ℝ)
    (ha : 0 ≤ a) (hDisj : Disjoint (S.map core) Z)
    (hDegree : ∀ w ∈ S, (M.degreeInto (S.map core ∪ Z) (core w):ℝ) ≤ a)
    (hOpposite : ∀ z ∈ Z, (M.degreeInto (S.map core) z:ℝ) ≤ c z/2)
    (hRound : ∀ z ∈ Z, 64 ≤ fraction*c z)
    (hSmall : ∀ z ∈ Z, a ≤ p*c z/4096) :
    (rextPaletteCapacityInput M core S Z).Admissible p fraction a c := by
  refine ⟨MultiGraph.GeneralCopies.loopless (rextInternalSide M core S),?_,
    rextPaletteCapacityInput_degree_bound M core S Z a ha hDisj hDegree,?_,hRound,hSmall⟩
  · intro z hz w
    by_cases hw : w ∈ S
    · have hmem : z ∈ S.map core ∪ Z := mem_union_right _ hz
      have h := single_le_sum (f := fun y => M.mult s(core w,y))
        (fun _ _ => Nat.zero_le _) hmem
      have h' : (M.mult s(core w,z):ℝ) ≤ (M.degreeInto (S.map core ∪ Z) (core w):ℝ) := by
        exact_mod_cast h
      simp only [rextPaletteCapacityInput, ite_eq_left hw]
      exact ⟨Nat.cast_nonneg _, (by rw [Sym2.eq_swap]; exact h'.trans (hDegree w hw))⟩
    · simpa only [rextPaletteCapacityInput, ite_eq_right hw] using And.intro le_rfl ha
  · intro z hz
    rw [rextPaletteCapacityInput_weight_sum]
    exact hOpposite z hz


/-- Internal edge copies counted in part coordinates are exactly the
edges induced by the corresponding side in Rext. -/
theorem rextInternalSide_edgeCount (M : MultiGraph U) (core : W ↪ U) (S : Finset W) :
    (rextInternalSide M core S).edgeCount = M.edgesWithin (S.map core) := by
  have hS := (rextInternalSide M core S).sum_degrees_eq_twice_edgeCount
  have hU := (M.restrict (S.map core)).sum_degrees_eq_twice_edgeCount
  have h₁ : (∑ w, (rextInternalSide M core S).degree w) =
      ∑ u ∈ S.map core, M.degreeInto (S.map core) u := by
    rw [sum_map]
    simp_rw [rextSideDegree]
    rw [← sum_filter]
    congr 1
    exact eq_of_subset_of_card_le (by intro w hw; exact (mem_filter.mp hw).2)
      (card_le_card fun w hw => mem_filter.mpr ⟨mem_univ _,hw⟩)
  have h₂ : (∑ u, (M.restrict (S.map core)).degree u) =
      ∑ u ∈ S.map core, M.degreeInto (S.map core) u := by
    simp_rw [MultiGraph.degree_restrict]
    rw [← sum_filter]
    congr 1
    exact eq_of_subset_of_card_le (by intro u hu; exact (mem_filter.mp hu).2)
      (card_le_card fun u hu => mem_filter.mpr ⟨mem_univ _,hu⟩)
  rw [h₁] at hS
  rw [h₂] at hU
  unfold MultiGraph.edgesWithin
  omega

/-- The mass of a capacity test is the size of the corresponding
edge set E₊ or E₋, including all parallel copies. -/
theorem rextPaletteCapacityInput_edgeCount (M : MultiGraph U) (core : W ↪ U)
    (S : Finset W) (Z : Finset U) :
    (rextPaletteCapacityInput M core S Z).edgeCount =
      (M.edgesWithin (S.map core):ℝ) + ∑ z ∈ Z, (M.degreeInto (S.map core) z:ℝ) := by
  have hC : Fintype.card (Copies (rextInternalSide M core S)) =
      (rextInternalSide M core S).edgeCount := by
    simp only [Copies, Fintype.card_sigma, Fintype.card_fin, MultiGraph.edgeCount]
  have hRows := sum_congr (s₁ := Z) rfl
    (fun z _ => rextPaletteCapacityInput_weight_sum M core S Z z)
  change (Fintype.card (Copies (rextInternalSide M core S)):ℝ) +
    (∑ z ∈ Z, ∑ w, (rextPaletteCapacityInput M core S Z).weight z w) = _
  rw [hC, rextInternalSide_edgeCount, hRows]

omit [Fintype W] [Fintype U] [DecidableEq U] in
/-- The weighted degree of a sampled block is a degree in Rext. -/
theorem rext_weight_sum_in_block [DecidableEq W] (M : MultiGraph U) (core : W ↪ U)
    (S X : Finset W) (z : U) :
    (∑ w ∈ X, if w ∈ S then (M.mult s(z,core w):ℝ) else 0) =
      (M.degreeInto ((X ∩ S).map core) z:ℝ) := by
  rw [← sum_filter]
  simp only [MultiGraph.degreeInto, sum_map, Nat.cast_sum]
  congr 1


private theorem copies_in_subset_count (N : MultiGraph W) (X : Finset W) :
    (∑ e : Copies N, eventIndicator ((ends N e).1 ∈ X ∧ (ends N e).2 ∈ X)) =
      (N.edgesWithin X:ℝ) := by
  unfold MultiGraph.edgesWithin MultiGraph.edgeCount
  rw [Fintype.sum_sigma, Nat.cast_sum]
  apply sum_congr rfl
  intro e _
  have hSub : e.toFinset ⊆ X ↔ (endpoints e).1 ∈ X ∧ (endpoints e).2 ∈ X := by
    conv_lhs => rw [← endpoints_eq e]
    simp only [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff]
  simp only [ends, MultiGraph.restrict]
  by_cases h : e.toFinset ⊆ X
  · simp [h, hSub.mp h, eventIndicator, nsmul_eq_mul]
  · simp [h, mt hSub.mpr h, eventIndicator]

omit [Fintype W] [Fintype U] [DecidableEq U] in
private theorem rextInternalSide_restrict (M : MultiGraph U) (core : W ↪ U)
    (S X : Finset W) :
    (rextInternalSide M core S).restrict X = rextInternalSide M core (X ∩ S) := by
  apply MultiGraph.ext_mult
  intro e
  have hi : e.toFinset ⊆ X ∩ S ↔ e.toFinset ⊆ X ∧ e.toFinset ⊆ S := by
    refine ⟨fun h => ⟨fun _ hw => (mem_inter.mp (h hw)).1, fun _ hw => (mem_inter.mp (h hw)).2⟩,?_⟩
    exact fun ⟨hX,hS⟩ _ hw => mem_inter.mpr ⟨hX hw,hS hw⟩
  simp only [rextInternalSide, MultiGraph.restrict]
  by_cases hX : e.toFinset ⊆ X <;> by_cases hS : e.toFinset ⊆ S <;> simp [hi,hX,hS]

/-- Written on the actual vertices of Rext, the statistic is exactly
(5.5), with internal edges and opposite-side incidences counted with
their multiplicities. -/
theorem rextPaletteCapacityInput_statistic (M : MultiGraph U) (core : W ↪ U)
    (S X : Finset W) (Z : Finset U) (p fraction : ℝ) (c : U → ℝ) :
    (rextPaletteCapacityInput M core S Z).statistic p fraction c X =
      (64*fraction/p^2)*(M.edgesWithin ((X ∩ S).map core):ℝ) +
      ∑ z ∈ Z, min ((64*fraction/p)*(M.degreeInto ((X ∩ S).map core) z:ℝ))
        (⌊(15/16:ℝ)*fraction*c z⌋₊ : ℝ) := by
  simp only [PaletteBlockCapacityInput.statistic, subsetBlockCapacity,
    rextPaletteCapacityInput, rext_weight_sum_in_block, copies_in_subset_count,
    MultiGraph.edgesWithin, rextInternalSide_restrict, rextInternalSide_edgeCount]



/-- By the lower incidence bound in (5.3), the floor in (5.5) fits
within the number of colors available at each exceptional vertex.
When the scale factors are at most one, the statistic is a lower
bound for the number of eligible edge copies with those vertex caps. -/
theorem rextPaletteCapacityInput_le_eligible_edges (M : MultiGraph U) (core : W ↪ U)
    (S X : Finset W) (Z : Finset U) (p fraction : ℝ) (c : U → ℝ) (r : U → ℕ)
    (hp : 0 < p) (hpOne : p ≤ 1) (hf : 0 ≤ fraction) (hScale : 64*fraction ≤ p^2)
    (hc : ∀ z ∈ Z, 0 ≤ c z)
    (hIncidence : ∀ z ∈ Z, (15/16:ℝ)*fraction*c z ≤ r z) :
    (rextPaletteCapacityInput M core S Z).statistic p fraction c X ≤
      (M.edgesWithin ((X ∩ S).map core):ℝ) +
        ∑ z ∈ Z, ((min (M.degreeInto ((X ∩ S).map core) z) (r z) : ℕ):ℝ) := by
  rw [rextPaletteCapacityInput_statistic]
  have h₂ : 64*fraction/p^2 ≤ 1 := (div_le_one (by positivity)).mpr hScale
  have h₁ : 64*fraction/p ≤ 1 := by
    apply (div_le_one hp).mpr
    have h := mul_le_mul_of_nonneg_left hpOne hp.le
    nlinarith only [hScale,h]
  refine add_le_add (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg _)) (sum_le_sum ?_)
  intro z hz
  rw [Nat.cast_min]
  apply min_le_min
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right h₁
      (Nat.cast_nonneg (α := ℝ) (M.degreeInto ((X ∩ S).map core) z))
  · exact (Nat.floor_le (mul_nonneg (by positivity) (hc z hz))).trans (hIncidence z hz)

section Preferred

variable {I : Type*} [Fintype I] {V : I → Type*} [∀ i, Fintype (V i)]

/-- The distinct representative endpoints of one ordinary vertex,
split into the parts used for block sampling. -/
noncomputable def rextPreferredEnds (core : (Σ i, V i) ↪ U) (T : Finset U) (i : I) :
    Finset (V i) :=
  univ.filter (fun v => core ⟨i,v⟩ ∈ T)

omit [Fintype U] in
theorem rextPreferredEnds_card (core : (Σ i, V i) ↪ U) (T : Finset U)
    (hT : T ⊆ univ.map core) :
    (∑ i, (rextPreferredEnds core T i).card) = T.card := by
  let R := (univ : Finset (Σ i, V i)).filter (fun w => core w ∈ T)
  have hMap : R.map core = T := by
    ext w
    constructor
    · intro h
      obtain ⟨v,hv,rfl⟩ := mem_map.mp h
      exact (mem_filter.mp hv).2
    · intro hw
      obtain ⟨v,_,rfl⟩ := mem_map.mp (hT hw)
      exact mem_map.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,hw⟩,rfl⟩
  calc
    _ = R.card := by
      simp only [R, rextPreferredEnds, card_eq_sum_ones, sum_filter]
      rw [Fintype.sum_sigma]
    _ = T.card := (card_map core).symm.trans (congrArg Finset.card hMap)

omit [Fintype U] in
/-- The sample counts precisely the representatives whose core
endpoints lie in the selected block of Rext. -/
theorem rextPreferredEnds_sampled (core : (Σ i, V i) ↪ U) (T : Finset U)
    (s : I → ℕ) (X : BlockParts (V := V) s) :
    ordinaryBlockPreferred s (rextPreferredEnds core T) X =
      ((T ∩ (blockPartsSelected s X).map core).card:ℝ) := by
  let Y := blockPartsSelected s X
  let R := Y.filter (fun w => core w ∈ T)
  have hMap : R.map core = T ∩ Y.map core := by
    ext w
    constructor
    · intro h
      obtain ⟨v,hv,rfl⟩ := mem_map.mp h
      obtain ⟨hY,hT⟩ := mem_filter.mp hv
      exact mem_inter.mpr ⟨hT,mem_map.mpr ⟨v,hY,rfl⟩⟩
    · intro hw
      obtain ⟨hT,hY⟩ := mem_inter.mp hw
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hY
      exact mem_map.mpr ⟨v,mem_filter.mpr ⟨hv,hT⟩,rfl⟩
  rw [← hMap, card_map]
  have hCard : (R.card:ℝ) = ∑ w ∈ Y, eventIndicator (core w ∈ T) := by
    rw [show R.card = ∑ _w ∈ R, (1:ℕ) from card_eq_sum_ones R, Nat.cast_sum]
    simp only [R, sum_filter, Nat.cast_one]
    exact sum_congr rfl (fun w _ => by
      by_cases hw : core w ∈ T <;> simp [eventIndicator,hw])
  rw [hCard, sum_blockPartsSelected]
  unfold ordinaryBlockPreferred
  apply sum_congr rfl
  intro i _
  let L := (X i).val.filter (fun v => core ⟨i,v⟩ ∈ T)
  have hL : rextPreferredEnds core T i ∩ (X i).val = L := by
    ext v
    simp only [rextPreferredEnds, mem_inter, mem_filter, mem_univ, true_and, L, and_comm]
  rw [hL, card_eq_sum_ones, Nat.cast_sum]
  simp only [L, sum_filter, Nat.cast_one]
  exact sum_congr rfl (fun v _ => by
    by_cases hv : core ⟨i,v⟩ ∈ T <;> simp [eventIndicator,hv])

noncomputable def rextPreferredWeight (M : MultiGraph U) (core : (Σ i, V i) ↪ U)
    (S : Finset (Σ i, V i)) (z : U) (i : I) (v : V i) : ℝ :=
  if (⟨i,v⟩ : Σ i, V i) ∈ S then M.mult s(z,core ⟨i,v⟩) else 0

omit [Fintype U] [DecidableEq U] in
/-- Preferred incidences at special vertices give their actual
multigraph degree into the sampled part of the preferred side. -/
theorem rextPreferredWeight_sampled (M : MultiGraph U) (core : (Σ i, V i) ↪ U)
    (S : Finset (Σ i, V i)) (z : U) (s : I → ℕ) (X : BlockParts (V := V) s) :
    specialBlockPreferred s (rextPreferredWeight M core S z) X =
      (M.degreeInto (((blockPartsSelected s X) ∩ S).map core) z:ℝ) := by
  rw [← rext_weight_sum_in_block M core S (blockPartsSelected s X) z, sum_blockPartsSelected]
  rfl

/-- Extract the representatives from the preferred-side lemma and
transport their total number to the block coordinates. -/
theorem exists_rext_ordinary_preferred_inputs
    (M : MultiGraph U) (core : (Σ i, V i) ↪ U)
    (A B : Finset U) (hAB : Disjoint A B) (hCore : A ∪ B ⊆ univ.map core)
    (z : U) (k a : ℕ) (β : ℝ) (hβ : 0 < β) (hβ₁ : β ≤ 1)
    (hDegree : M.degree z ≤ k) :
    let c := M.degreeInto (A ∪ B) z
    β*(k:ℝ) ≤ (c:ℝ) → (a:ℝ) ≤ β*k/10 →
    (c - (M.neighboursInto (A ∪ B) z).card ≤ a ∨
      β*(k:ℝ) ≤ min ((M.neighboursInto A z).card : ℝ) ((M.neighboursInto B z).card : ℝ)) →
    ∃ S : Finset U, (S = A ∨ S = B) ∧ c ≤ 2*M.degreeInto S z ∧
      β*(c:ℝ)/4 ≤ ∑ i, ((rextPreferredEnds core (M.neighboursInto S z) i).card:ℝ) ∧
      ∃ f : ↥(M.neighboursInto S z) ↪ (Σ y : U, Fin (M.mult s(z,y))),
        ∀ y, (f y).1 = y.val := by
  intro c hDensity hSlack hOrd
  obtain ⟨S,hSide,hHalf,hCount,f,hf⟩ := exists_preferred_side_representatives M A B hAB z
    k a β hβ hβ₁ hDegree hDensity hSlack hOrd
  have hSub : M.neighboursInto S z ⊆ univ.map core := by
    intro v hv
    apply hCore
    have hm := (mem_filter.mp hv).1
    rcases hSide with rfl | rfl
    · exact mem_union_left _ hm
    · exact mem_union_right _ hm
  have h := rextPreferredEnds_card core (M.neighboursInto S z) hSub
  have hReal : (∑ i, ((rextPreferredEnds core (M.neighboursInto S z) i).card:ℝ)) =
      ((M.neighboursInto S z).card:ℝ) := by exact_mod_cast h
  exact ⟨S,hSide,hHalf,hReal.symm ▸ hCount,f,hf⟩


omit [Fintype U] [DecidableEq U] in
/-- The preferred incidence row sums to the Rext degree into its
preferred side before sampling. -/
theorem rextPreferredWeight_sum (M : MultiGraph U) (core : (Σ i, V i) ↪ U)
    (S : Finset (Σ i, V i)) (z : U) :
    (∑ i, ∑ v, rextPreferredWeight M core S z i v) =
      (M.degreeInto (S.map core) z:ℝ) := by
  have h := rext_weight_sum_in_block M core S univ z
  rw [univ_inter, Fintype.sum_sigma] at h
  simpa only [rextPreferredWeight] using h

omit [Fintype U] in
/-- Both halves of the preferred-side split in §5.1.1. Once a vertex
chooses the side of larger degree, the other side contributes at most
half the total degree. -/
theorem rext_preferred_and_opposite_degrees (M : MultiGraph U) {S T : Finset U}
    (hDisj : Disjoint S T) (z : U) (hPref : M.degreeInto T z ≤ M.degreeInto S z) :
    (M.degreeInto (S ∪ T) z:ℝ)/2 ≤ M.degreeInto S z ∧
      (M.degreeInto T z:ℝ) ≤ (M.degreeInto (S ∪ T) z:ℝ)/2 := by
  have hEq : M.degreeInto (S ∪ T) z = M.degreeInto S z + M.degreeInto T z := by
    simp only [MultiGraph.degreeInto, sum_union hDisj]
  have hR : (M.degreeInto T z:ℝ) ≤ M.degreeInto S z := by exact_mod_cast hPref
  rw [hEq, Nat.cast_add]
  constructor <;> linarith only [hR]

end Preferred

end OverfullWork.ChenShan
