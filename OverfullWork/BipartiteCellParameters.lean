module

public import OverfullWork.TwoSidedInitialCells
public import OverfullWork.RegularPairNeighbourhood

@[expose] public section


/-! Quantitative size and slicing data for equal subcells of a bipartite
parent equipartition. The two directions retain distinct host fibres. -/
namespace OverfullWork.BipartiteRegularitySource
open Finset Finpartition DirectedClusterQuotient DirectedBipartiteEncoding
open scoped Classical
set_option maxHeartbeats 18000000

theorem rounded_chunk_scale (n p : ℕ) (γ : ℝ) (hp : 0 < p)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hLarge : 4*(p:ℝ) ≤ γ*(n:ℝ)) :
    let m := ⌊γ*(n:ℝ)/(p:ℝ)⌋₊
    0 < m ∧ γ*(n:ℝ)/2 ≤ (m:ℝ)*(p:ℝ) ∧
      (m:ℝ)*(p:ℝ) ≤ γ*(n:ℝ) ∧
      γ*(2*(n:ℝ)+(p:ℝ))/6 ≤ (m:ℝ)*(p:ℝ) := by
  dsimp only
  let m := ⌊γ*(n:ℝ)/(p:ℝ)⌋₊
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hLo : γ*(n:ℝ) < ((m:ℝ)+1)*(p:ℝ) :=
    (div_lt_iff₀ hpR).mp (Nat.lt_floor_add_one (γ*(n:ℝ)/(p:ℝ)))
  have hHi : (m:ℝ)*(p:ℝ) ≤ γ*(n:ℝ) :=
    (le_div_iff₀ hpR).mp (Nat.floor_le (by positivity))
  have hm : 0 < m := by
    by_contra hn
    have hz : m=0 := by omega
    simp only [hz,Nat.cast_zero,zero_add,one_mul] at hLo
    linarith only [hLarge,hLo,hpR]
  have hN := mul_le_mul_of_nonneg_right hγ1 (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hPN : (p:ℝ) ≤ (n:ℝ) := by linarith only [hLarge,hN,hpR]
  have hγP := mul_le_mul_of_nonneg_left hPN hγ.le
  refine ⟨hm,?_,hHi,?_⟩ <;> nlinarith only [hLo,hLarge,hγP]

variable {V : Type*} [Fintype V]

theorem parent_chunk_scale (P : Finpartition (univ : Finset (V ⊕ V)))
    (hEqui : P.IsEquipartition) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hp : 0 < P.parts.card) (hLarge : 4*(P.parts.card:ℝ) ≤ γ*(Fintype.card V:ℝ))
    (U : P.parts) :
    (U.val.card:ℝ)*γ/6 ≤ (⌊γ*(Fintype.card V:ℝ)/(P.parts.card:ℝ)⌋₊:ℝ) := by
  have hUp := hEqui.card_part_le_average_add_one U.property
  simp only [card_univ,Fintype.card_sum] at hUp
  have hMul := Nat.mul_le_mul_right P.parts.card hUp
  have hDiv := Nat.mul_div_le (Fintype.card V+Fintype.card V) P.parts.card
  have hBound : U.val.card*P.parts.card ≤ 2*Fintype.card V+P.parts.card := by nlinarith only [hMul,hDiv]
  have hBoundR : (U.val.card:ℝ)*(P.parts.card:ℝ) ≤ 2*(Fintype.card V:ℝ)+(P.parts.card:ℝ) := by exact_mod_cast hBound
  have hScaled := mul_le_mul_of_nonneg_left hBoundR (show (0:ℝ) ≤ γ/6 by positivity)
  have hM := (rounded_chunk_scale (Fintype.card V) P.parts.card γ hp hγ hγ1 hLarge).2.2.2
  have hpR : (0:ℝ) < P.parts.card := by exact_mod_cast hp
  apply (mul_le_mul_iff_right₀ hpR).mp
  nlinarith only [hScaled,hM]

theorem directed_pair_from_parent (D : Digraph V)
    (U W : Finset (V ⊕ V)) (A B : Finset V) (ε d γ : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 ≤ ε) (hεγ : ε ≤ γ/6)
    (hUniform : (graph D).IsUniform ε U W) (hDensity : d ≤ ((graph D).edgeDensity U W:ℝ))
    (hA : left A ⊆ U) (hB : right B ⊆ W)
    (hASize : (U.card:ℝ)*γ/6 ≤ (A.card:ℝ))
    (hBSize : (W.card:ℝ)*γ/6 ≤ (B.card:ℝ)) :
    DirectedRegularPairs.IsUniform D (12*ε/γ) A B ∧
      d-ε ≤ DirectedRegularPairs.density D A B := by
  have hScale : ∀ a b : ℝ,0 ≤ a → a*γ/6 ≤ b → a*ε ≤ b ∧ a*ε ≤ b*(12*ε/γ) := by
    intro a b ha hab
    constructor
    · have hh := mul_le_mul_of_nonneg_left hεγ ha
      nlinarith only [hh,hab]
    · rw [show b*(12*ε/γ)=(b*(12*ε))/γ by ring]
      apply (le_div_iff₀ hγ).mpr
      have hh := mul_le_mul_of_nonneg_right hab (show (0:ℝ) ≤ 12*ε by positivity)
      have hPos : 0 ≤ a*ε*γ := by positivity
      nlinarith only [hh,hPos]
  obtain ⟨ha,haScale⟩ := hScale _ _ (Nat.cast_nonneg _) hASize
  obtain ⟨hb,hbScale⟩ := hScale _ _ (Nat.cast_nonneg _) hBSize
  have hCap : 2*ε ≤ 12*ε/γ := by
    apply (le_div_iff₀ hγ).mpr
    have hh := mul_le_mul_of_nonneg_left hγ1 (show (0:ℝ) ≤ 2*ε by positivity)
    linarith only [hh,hε]
  have hEncoded := RegularPairNeighbourhood.uniform_on_subcells (graph D) hUniform hA hB
    (by simpa only [left_card] using ha) (by simpa only [right_card] using hb)
    (by simpa only [left_card] using haScale) (by simpa only [right_card] using hbScale) hCap
  have hDensity' := (abs_lt.mp (hUniform hA hB
    (by simpa only [left_card] using ha) (by simpa only [right_card] using hb))).1
  rw [density_eq] at hDensity'
  exact ⟨directed_uniform_of_encoded D A B _ hEncoded,by linarith only [hDensity',hDensity]⟩

end OverfullWork.BipartiteRegularitySource
