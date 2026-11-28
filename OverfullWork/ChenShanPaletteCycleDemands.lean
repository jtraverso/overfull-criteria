module

public import OverfullWork.ChenShanPaletteAssembly514
public import OverfullWork.ChenShanClusterCycleDemands
public import OverfullWork.ChenShanAugmentationBudget
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The core vertices already covered by a recolored matching. -/
noncomputable def paletteCoveredCore {M : MultiGraph V} {k : ℕ}
    (D : M.EdgeColoring k) (A B : Finset V) (j : Fin k) : Finset V :=
  (A ∪ B).filter (fun v => (D.colourGraph j).degree v = 1)

/-- Turn the §5.1.4 recoloring guarantees into the support, balance
and cardinality properties of the occupied sets in §5.1.5. -/
theorem paletteCoveredCore_properties {M : MultiGraph V} {k mass : ℕ}
    (D : M.EdgeColoring k) (A B interior : Finset V) (j : Fin k)
    (hAB : Disjoint A B) (hBounds : PaletteMatchingBounds D A B mass)
    (hInterior : ∀ v ∈ A ∪ B, v ∉ interior → (D.colourGraph j).degree v = 0) :
    let blocked := paletteCoveredCore D A B j
    blocked ⊆ (A ∪ B) ∩ interior ∧
      (A ∩ blocked).card = (B ∩ blocked).card ∧
      (blocked.card:ℝ) ≤ 2*(mass:ℝ)/k + 4 := by
  intro blocked
  have hFilter (T : Finset V) (hT : T ⊆ A ∪ B) :
      T ∩ blocked = T.filter (fun v => (D.colourGraph j).degree v = 1) := by
    ext v
    simp only [blocked, paletteCoveredCore, mem_inter, mem_filter]
    exact ⟨fun ⟨h, _, d⟩ => ⟨h,d⟩, fun ⟨h,d⟩ => ⟨h,hT h,d⟩⟩
  have hLeft := hFilter A subset_union_left
  have hRight := hFilter B subset_union_right
  have hBalance := hBounds.balanced j
  rw [sideCount_eq_card_covered, sideCount_eq_card_covered, ← hLeft, ← hRight] at hBalance
  have hCard : blocked.card = (A ∩ blocked).card + (B ∩ blocked).card := by
    have hUnion : (A ∩ blocked) ∪ (B ∩ blocked) = blocked := by
      rw [← union_inter_distrib_right]
      exact inter_eq_right.mpr (filter_subset _ _)
    rw [← card_union_of_disjoint (hAB.mono inter_subset_left inter_subset_left), hUnion]
  refine ⟨?_, by exact_mod_cast hBalance, ?_⟩
  · intro v hv
    have h := mem_filter.mp hv
    refine mem_inter.mpr ⟨h.1, ?_⟩
    by_contra hn
    have hZero := hInterior v h.1 hn
    have hOne := h.2
    omega
  · have hBound := hBounds.core_bound j
    rw [sideCount_eq_card_covered, sideCount_eq_card_covered, ← hLeft, ← hRight] at hBound
    rw [hCard, Nat.cast_add]
    exact_mod_cast hBound

omit [Fintype V] in
private theorem sum_cluster_covered_eq {I : Type*} [Fintype I]
    (C : I → Finset V) (S blocked : Finset V)
    (hDisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hSub : ∀ i, C i ⊆ S)
    (hCover : ∀ v ∈ S, v ∈ blocked → ∃ i, v ∈ C i) :
    (∑ i, (C i ∩ blocked).card) = (S ∩ blocked).card := by
  have hUnion : univ.biUnion (fun i => C i ∩ blocked) = S ∩ blocked := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hv
      exact mem_inter.mpr ⟨hSub i (mem_inter.mp hi).1, (mem_inter.mp hi).2⟩
    · intro hv
      obtain ⟨hS, hB⟩ := mem_inter.mp hv
      obtain ⟨i, hi⟩ := hCover v hS hB
      exact mem_biUnion.mpr ⟨i, mem_univ _, mem_inter.mpr ⟨hi, hB⟩⟩
  rw [← hUnion, card_biUnion]
  exact fun _ _ _ _ hij => (hDisj hij).mono inter_subset_left inter_subset_left

/-- On the first augmentation cycle Aᵢ meets Bᵢ and its predecessor.
On the second cycle Aᵢ₊₁ meets Bᵢ and its successor. -/
def paletteAugmentationNext (ℓ : ℕ) (u : Fin 2) : Equiv.Perm (Fin ℓ) :=
  if u = 0 then (finRotate ℓ)⁻¹ else finRotate ℓ

theorem paletteAugmentationNext_sameCycle {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (u : Fin 2) (i j : Fin ℓ) :
    (paletteAugmentationNext ℓ u).SameCycle i j := by
  have hMove (a : Fin ℓ) : finRotate ℓ a ≠ a := by
    apply Equiv.Perm.mem_support.mp
    rw [support_finRotate_of_le hℓ]
    exact mem_univ a
  have h := (isCycle_finRotate_of_le hℓ).sameCycle (hMove i) (hMove j)
  by_cases hu : u = 0
  · simpa [paletteAugmentationNext, hu] using h.inv
  · simpa [paletteAugmentationNext, hu] using h

/-- Obtain the integer demands of §5.1.5 directly from a palette
coloring. The two cycle geometries are indexed by the two colors
in each pair. A boundary cluster may occur in a cycle even though
its initially covered set is empty. -/
theorem exists_palette_pair_augmentation_demands
    {M : MultiGraph V} {k mass s ℓ : ℕ}
    (D : M.EdgeColoring k) (A B interior : Finset V)
    (hSize : s*2 = k) (hℓ : 2 ≤ ℓ)
    (L R : Fin 2 → Fin ℓ → Finset V) (b z : ℕ)
    (hAB : Disjoint A B) (hBounds : PaletteMatchingBounds D A B mass)
    (hInterior : ∀ v ∈ A ∪ B, v ∉ interior → ∀ j, (D.colourGraph j).degree v = 0)
    (hL : ∀ u, Pairwise (fun i j => Disjoint (L u i) (L u j)))
    (hR : ∀ u, Pairwise (fun i j => Disjoint (R u i) (R u j)))
    (hSubL : ∀ u i, L u i ⊆ A) (hSubR : ∀ u i, R u i ⊆ B)
    (hCoverL : ∀ u v, v ∈ A → v ∈ interior → ∃ i, v ∈ L u i)
    (hCoverR : ∀ u v, v ∈ B → v ∈ interior → ∃ i, v ∈ R u i)
    (hZ : 2*(mass:ℝ)/k + 4 < (z:ℝ)+1) (hBudget : ℓ*z ≤ b) :
    let label : Fin s × Fin 2 ≃ Fin k := finProdFinEquiv.trans (finCongr hSize)
    let blocked (p : Fin s × Fin 2) := paletteCoveredCore D A B (label p)
    ∃ H : (Fin s × Fin 2) → Fin ℓ → Fin ℓ → ℕ,
      (∀ p, blocked p ⊆ (A ∪ B) ∩ interior) ∧
      (∀ p i j, j ≠ i → j ≠ paletteAugmentationNext ℓ p.2 i → H p i j = 0) ∧
      (∀ p i, (L p.2 i ∩ blocked p).card + ∑ j, H p i j = b) ∧
      (∀ p j, (R p.2 j ∩ blocked p).card + ∑ i, H p i j = b) := by
  classical
  intro label blocked
  have hProperties (p : Fin s × Fin 2) := paletteCoveredCore_properties D A B interior (label p)
    hAB hBounds (fun v hv hOut => hInterior v hv hOut (label p))
  have hCovered (p : Fin s × Fin 2) : (blocked p).card ≤ z := by
    have h := (hProperties p).2.2.trans_lt hZ
    have h' : (blocked p).card < z+1 := by exact_mod_cast h
    omega
  have hMatrices (p : Fin s × Fin 2) :
      ∃ H : Fin ℓ → Fin ℓ → ℕ,
        (∀ i j, j ≠ i → j ≠ paletteAugmentationNext ℓ p.2 i → H i j = 0) ∧
        (∀ i, (L p.2 i ∩ blocked p).card + ∑ j, H i j = b) ∧
        (∀ j, (R p.2 j ∩ blocked p).card + ∑ i, H i j = b) := by
    have hSumL := sum_cluster_covered_eq (L p.2) A (blocked p) (hL p.2) (hSubL p.2)
      (fun v hv h => hCoverL p.2 v hv (mem_inter.mp ((hProperties p).1 h)).2)
    have hSumR := sum_cluster_covered_eq (R p.2) B (blocked p) (hR p.2) (hSubR p.2)
      (fun v hv h => hCoverR p.2 v hv (mem_inter.mp ((hProperties p).1 h)).2)
    have hz : z ≤ b := (show z ≤ ℓ*z from by
      simpa using Nat.mul_le_mul_right z (show 1 ≤ ℓ by omega)).trans hBudget
    exact exists_clusterCycle_augmentation_loads (paletteAugmentationNext ℓ p.2)
      (paletteAugmentationNext_sameCycle hℓ p.2)
      (fun i => (L p.2 i ∩ blocked p).card) (fun j => (R p.2 j ∩ blocked p).card) b z
      hz (by simpa using hBudget) (fun _ => (card_le_card inter_subset_right).trans (hCovered p))
      (fun _ => (card_le_card inter_subset_right).trans (hCovered p))
      (hSumL.trans ((hProperties p).2.1.trans hSumR.symm))
  choose H hSupport hRows hCols using hMatrices
  exact ⟨H, fun p => (hProperties p).1, hSupport, hRows, hCols⟩

/-- The two cycles for one canonical interval A₀ B₀ ... Bₗ₋₁ Aₗ.
Both contain all interior vertices of the appropriate side.
The first uses A₀ and the second uses Aₗ. -/
theorem exists_palette_interval_augmentation_demands
    {M : MultiGraph V} {k mass s ℓ : ℕ}
    (D : M.EdgeColoring k) (A B interior : Finset V) (C : ℕ → Finset V)
    (hSize : s*2 = k) (hℓ : 2 ≤ ℓ) (b z : ℕ)
    (hAB : Disjoint A B) (hBounds : PaletteMatchingBounds D A B mass)
    (hInterior : ∀ v ∈ A ∪ B, v ∉ interior → ∀ j, (D.colourGraph j).degree v = 0)
    (hDisj : ∀ i j, i ≤ 2*ℓ → j ≤ 2*ℓ → i ≠ j → Disjoint (C i) (C j))
    (hEven : ∀ i ≤ ℓ, C (2*i) ⊆ A) (hOdd : ∀ i < ℓ, C (2*i+1) ⊆ B)
    (hCover : ∀ v ∈ interior, ∃ i, 0 < i ∧ i < 2*ℓ ∧ v ∈ C i)
    (hZ : 2*(mass:ℝ)/k + 4 < (z:ℝ)+1) (hBudget : ℓ*z ≤ b) :
    let label : Fin s × Fin 2 ≃ Fin k := finProdFinEquiv.trans (finCongr hSize)
    let blocked (p : Fin s × Fin 2) := paletteCoveredCore D A B (label p)
    let L (u : Fin 2) (i : Fin ℓ) := C (2*i.val + if u = 0 then 0 else 2)
    let R (_ : Fin 2) (i : Fin ℓ) := C (2*i.val+1)
    ∃ H : (Fin s × Fin 2) → Fin ℓ → Fin ℓ → ℕ,
      (∀ p, blocked p ⊆ (A ∪ B) ∩ interior) ∧
      (∀ p i j, j ≠ i → j ≠ paletteAugmentationNext ℓ p.2 i → H p i j = 0) ∧
      (∀ p i, (L p.2 i ∩ blocked p).card + ∑ j, H p i j = b) ∧
      (∀ p j, (R p.2 j ∩ blocked p).card + ∑ i, H p i j = b) := by
  intro label blocked L R
  let shift (u : Fin 2) := if u = 0 then 0 else 2
  have hShift (u : Fin 2) : shift u ≤ 2 := by by_cases h : u = 0 <;> simp [shift, h]
  have hL (u : Fin 2) : Pairwise (fun i j => Disjoint (L u i) (L u j)) := by
    intro i j hNe
    change Disjoint (C (2*i.val+shift u)) (C (2*j.val+shift u))
    have hi := i.isLt
    have hj := j.isLt
    have hs := hShift u
    exact hDisj _ _ (by omega) (by omega) (fun h => hNe (Fin.ext (by omega)))
  have hR (u : Fin 2) : Pairwise (fun i j => Disjoint (R u i) (R u j)) := by
    intro i j hNe
    have hi := i.isLt
    have hj := j.isLt
    exact hDisj _ _ (by omega) (by omega) (fun h => hNe (Fin.ext (by omega)))
  have hLA (u : Fin 2) (i : Fin ℓ) : L u i ⊆ A := by
    have hi := i.isLt
    by_cases hu : u = 0
    · simpa [L, hu] using hEven i.val hi.le
    · have h := hEven (i.val+1) hi
      simpa [L, hu, Nat.mul_succ] using h
  have hRB (u : Fin 2) (i : Fin ℓ) : R u i ⊆ B := hOdd i.val i.isLt
  have hCL (u : Fin 2) (v : V) (hv : v ∈ A) (hInt : v ∈ interior) : ∃ i, v ∈ L u i := by
    obtain ⟨i, hi0, hi, hiv⟩ := hCover v hInt
    have hParity : i % 2 = 0 := by
      by_contra hn
      have hEq : i = 2*(i/2)+1 := by omega
      rw [hEq] at hiv
      exact disjoint_left.mp hAB hv (hOdd (i/2) (by omega) hiv)
    by_cases hu : u = 0
    · refine ⟨⟨i/2, by omega⟩, ?_⟩
      have hEq : 2*(i/2) = i := by omega
      simpa [L, hu, hEq] using hiv
    · refine ⟨⟨i/2-1, by omega⟩, ?_⟩
      have hEq : 2*(i/2-1)+2 = i := by omega
      simpa [L, hu, hEq] using hiv
  have hCR (u : Fin 2) (v : V) (hv : v ∈ B) (hInt : v ∈ interior) : ∃ i, v ∈ R u i := by
    obtain ⟨i, _, hi, hiv⟩ := hCover v hInt
    have hParity : i % 2 = 1 := by
      by_contra hn
      have hEq : i = 2*(i/2) := by omega
      rw [hEq] at hiv
      exact disjoint_left.mp hAB (hEven (i/2) (by omega) hiv) hv
    refine ⟨⟨i/2, by omega⟩, ?_⟩
    have hEq : 2*(i/2)+1 = i := by omega
    simpa [R, hEq] using hiv
  exact exists_palette_pair_augmentation_demands D A B interior hSize hℓ L R b z
    hAB hBounds hInterior hL hR hLA hRB hCL hCR hZ hBudget

/-- Round the class bound (5.9) down for the integer Hall demands
and choose the target b using the two quantitative margins of (5.12). -/
theorem exists_integral_palette_augmentation_budget
    (ℓ s n mass k : ℕ) (d₀ : ℝ) :
    let bound : ℝ := 2*(mass:ℝ)/k+4
    (ℓ:ℝ)*bound+2 ≤ d₀*n/100 →
    (s:ℝ)*((ℓ:ℝ)*bound+2) ≤ d₀^3*(n:ℝ)^2/40000 →
    ∃ z b : ℕ, bound < (z:ℝ)+1 ∧ ℓ*z ≤ b ∧
      (ℓ:ℝ)*bound+1 ≤ (b:ℝ) ∧ (b:ℝ) < d₀*n/100 ∧
      (s:ℝ)*(b:ℝ) ≤ d₀^3*(n:ℝ)^2/40000 := by
  intro bound hLocal hGlobal
  have hNonneg : 0 ≤ bound := by dsimp [bound]; positivity
  obtain ⟨b, hLower, hUpper, hProduct⟩ :=
    exists_augmentation_target_of_scaled_margins ℓ s n bound d₀ hNonneg hLocal hGlobal
  refine ⟨⌊bound⌋₊, b, Nat.lt_floor_add_one _, ?_, hLower, hUpper, hProduct⟩
  have hFloor : (⌊bound⌋₊ : ℝ) ≤ bound := Nat.floor_le hNonneg
  have hBound : (ℓ:ℝ)*(⌊bound⌋₊:ℝ) ≤ (b:ℝ) := by
    calc
      _ ≤ (ℓ:ℝ)*bound := mul_le_mul_of_nonneg_left hFloor (Nat.cast_nonneg _)
      _ ≤ _ := by linarith only [hLower]
  exact_mod_cast hBound

end OverfullWork.ChenShan
