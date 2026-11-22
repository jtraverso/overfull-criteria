module

public import OverfullWork.DirectedArcSelection

@[expose] public section


/-! Directed regular-pair counting with the source and target directions
kept explicit. This supplies the regular-pair lifting step used in
GGKLO Lemma 14.3 and the counting pattern of CMS (5.2)--(5.3).
No directed regularity partition or robust graph is postulated. -/
namespace OverfullWork.DirectedRegularPairs
open Finset Real DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 18000000

noncomputable def density (D : Digraph V) (A B : Finset V) : ℝ :=
  (incidences D A B:ℝ)/((A.card:ℝ)*(B.card:ℝ))

def IsUniform (D : Digraph V) (ε : ℝ) (U W : Finset V) : Prop :=
  ∀ A ⊆ U,∀ B ⊆ W,(U.card:ℝ)*ε ≤ (A.card:ℝ) → (W.card:ℝ)*ε ≤ (B.card:ℝ) →
    |density D A B-density D U W| < ε

theorem uniform_on_subcells (D : Digraph V) {U W A B : Finset V} {ε ε' : ℝ}
    (hUniform : IsUniform D ε U W) (hA : A ⊆ U) (hB : B ⊆ W)
    (hALarge : (U.card:ℝ)*ε ≤ (A.card:ℝ)) (hBLarge : (W.card:ℝ)*ε ≤ (B.card:ℝ))
    (hAScale : (U.card:ℝ)*ε ≤ (A.card:ℝ)*ε')
    (hBScale : (W.card:ℝ)*ε ≤ (B.card:ℝ)*ε') (hTol : 2*ε ≤ ε') :
    IsUniform D ε' A B := by
  intro A' hA' B' hB' hSizeA hSizeB
  have h₁ := hUniform A' (hA'.trans hA) B' (hB'.trans hB)
    (hAScale.trans hSizeA) (hBScale.trans hSizeB)
  have h₂ := hUniform A hA B hB hALarge hBLarge
  calc
    _ = |(density D A' B'-density D U W)-(density D A B-density D U W)| := by congr 1;ring
    _ ≤ |density D A' B'-density D U W|+|density D A B-density D U W| := abs_sub _ _
    _ < ε+ε := add_lt_add h₁ h₂
    _ ≤ ε' := by linarith only [hTol]

theorem density_on_subcells (D : Digraph V) {U W A B : Finset V} {ε d : ℝ}
    (hUniform : IsUniform D ε U W) (hDensity : d ≤ density D U W)
    (hA : A ⊆ U) (hB : B ⊆ W)
    (hALarge : (U.card:ℝ)*ε ≤ (A.card:ℝ)) (hBLarge : (W.card:ℝ)*ε ≤ (B.card:ℝ)) :
    d-ε < density D A B := by
  have hh := (abs_lt.mp (hUniform A hA B hB hALarge hBLarge)).1
  linarith only [hh,hDensity]

theorem uniform_incidences_lower (D : Digraph V) {U W A B : Finset V} {ε d : ℝ}
    (hUniform : IsUniform D ε U W) (hDensity : d ≤ density D U W)
    (hA : A ⊆ U) (hB : B ⊆ W)
    (hALarge : (U.card:ℝ)*ε ≤ (A.card:ℝ)) (hBLarge : (W.card:ℝ)*ε ≤ (B.card:ℝ))
    (hAPos : A.Nonempty) (hBPos : B.Nonempty) :
    (d-ε)*(A.card:ℝ)*(B.card:ℝ) < (incidences D A B:ℝ) := by
  have hh := density_on_subcells D hUniform hDensity hA hB hALarge hBLarge
  have hDen : (0:ℝ) < (A.card:ℝ)*(B.card:ℝ) := by
    have h₁ : (0:ℝ) < A.card := by exact_mod_cast hAPos.card_pos
    have h₂ : (0:ℝ) < B.card := by exact_mod_cast hBPos.card_pos
    positivity
  unfold density at hh
  have hPay := (lt_div_iff₀ hDen).mp hh
  nlinarith only [hPay]

theorem incidences_family_le {I : Type*} (D : Digraph V) (J : Finset I)
    (A : I → Finset V) (S B : Finset V)
    (hDis : (↑J:Set I).PairwiseDisjoint A) (hSub : ∀ i ∈ J,A i ⊆ S) :
    (∑ i ∈ J,incidences D (A i) B) ≤ incidences D S B := by
  unfold incidences
  rw [sum_comm]
  apply sum_le_sum
  intro v _
  let C : I → Finset V := fun i => (A i).filter fun u => D.Adj u v
  have hDisC : (↑J:Set I).PairwiseDisjoint C := by
    intro i hi j hj hij
    exact (hDis hi hj hij).mono (filter_subset _ _) (filter_subset _ _)
  have hSubC : J.biUnion C ⊆ S.filter (fun u => D.Adj u v) := by
    intro u hu
    obtain ⟨i,hi,hui⟩ := mem_biUnion.mp hu
    exact mem_filter.mpr ⟨hSub i hi (mem_filter.mp hui).1,(mem_filter.mp hui).2⟩
  have hCount := card_le_card hSubC
  rw [card_biUnion hDisC] at hCount
  exact hCount

theorem incidences_le_of_neighbour_bound (D : Digraph V) (S B : Finset V) (r : ℕ)
    (h : ∀ v ∈ B,inNeighbours D S v ≤ r) : incidences D S B ≤ r*B.card := by
  unfold incidences
  calc
    _ ≤ ∑ _v ∈ B,r := sum_le_sum h
    _ = _ := by simp [Nat.mul_comm]

theorem few_low_neighbours_family {I : Type*} (D : Digraph V) (J : Finset I)
    (hJ : J.Nonempty) (U A : I → Finset V) (W S : Finset V) (ε d : ℝ)
    (hε : 0 < ε) (hW : W.Nonempty) (hU : ∀ i ∈ J,(U i).Nonempty)
    (hUniform : ∀ i ∈ J,IsUniform D ε (U i) W)
    (hDensity : ∀ i ∈ J,d ≤ density D (U i) W)
    (hAU : ∀ i ∈ J,A i ⊆ U i) (hAS : ∀ i ∈ J,A i ⊆ S)
    (hSize : ∀ i ∈ J,((U i).card:ℝ)*ε ≤ ((A i).card:ℝ))
    (hDis : (↑J:Set I).PairwiseDisjoint A) (r : ℕ)
    (hr : (r:ℝ) ≤ (d-ε)*(∑ i ∈ J,((A i).card:ℝ))) :
    ((W.filter fun v => inNeighbours D S v < r).card:ℝ) < (W.card:ℝ)*ε := by
  let B := W.filter fun v => inNeighbours D S v < r
  by_contra hn
  have hB : (W.card:ℝ)*ε ≤ (B.card:ℝ) := by change ¬((B.card:ℝ) < _) at hn;linarith only [hn]
  have hBPos : B.Nonempty := by
    have hWPos : (0:ℝ) < W.card := by exact_mod_cast hW.card_pos
    have hh := (mul_pos hWPos hε).trans_le hB
    exact card_pos.mp (by exact_mod_cast hh)
  have hPoint : ∀ i ∈ J,(d-ε)*((A i).card:ℝ)*(B.card:ℝ) < (incidences D (A i) B:ℝ) := by
    intro i hi
    have hAPos : (A i).Nonempty := by
      have hUPos : (0:ℝ) < (U i).card := by exact_mod_cast (hU i hi).card_pos
      have hh := (mul_pos hUPos hε).trans_le (hSize i hi)
      exact card_pos.mp (by exact_mod_cast hh)
    exact uniform_incidences_lower D (hUniform i hi) (hDensity i hi)
      (hAU i hi) (filter_subset _ _) (hSize i hi) hB hAPos hBPos
  have hSum := sum_lt_sum_of_nonempty hJ hPoint
  rw [←sum_mul,←mul_sum] at hSum
  have hFamily : (∑ i ∈ J,(incidences D (A i) B:ℝ)) ≤ (incidences D S B:ℝ) := by
    exact_mod_cast incidences_family_le D J A S B hDis hAS
  have hUpper : (incidences D S B:ℝ) ≤ (r:ℝ)*(B.card:ℝ) := by
    exact_mod_cast incidences_le_of_neighbour_bound D S B r
      (fun v hv => (mem_filter.mp hv).2.le)
  have hProduct := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg B.card : (0:ℝ) ≤ B.card)
  linarith only [hSum,hFamily,hUpper,hProduct]

end OverfullWork.DirectedRegularPairs
