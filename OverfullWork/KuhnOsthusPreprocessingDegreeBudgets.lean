module

public import OverfullWork.KuhnOsthusPreprocessingConstruction

@[expose] public section


/-! The degree-demand parameters in the last step of Lemma 8.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling
open scoped Classical

/-- Choose the lower demand bound for Lemma 5.2 after spending the
semidegrees of the path extender and the exceptional factors. -/
theorem preprocessing_degree_demand_parameters (n b k r : ℕ) (μ : ℝ)
    (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hGap : (4:ℝ)*((k+r:ℕ):ℝ) ≤ μ*(b:ℝ))
    (hSize : (2:ℝ)*(b:ℝ) ≤ μ^2*(n:ℝ)) :
    ∃ L : ℕ, k+r ≤ b-L ∧ L ≤ b ∧ b ≤ 2*L ∧
      2*(b-L)*n ≤ L*⌈μ*(n:ℝ)⌉₊ ∧ 2*b*n ≤ ⌈μ*(n:ℝ)⌉₊^2 := by
  let L := b-(k+r)
  have hRoom : 2*(k+r) ≤ b := by
    have hSmall := mul_le_of_le_one_left (Nat.cast_nonneg b : (0:ℝ) ≤ b) hμ₁
    have hNonneg : (0:ℝ) ≤ ((k+r:ℕ):ℝ) := Nat.cast_nonneg _
    exact_mod_cast (show (2:ℝ)*((k+r:ℕ):ℝ) ≤ (b:ℝ) by linarith only [hSmall,hGap,hNonneg])
  have hL : L ≤ b := Nat.sub_le _ _
  have hTwo : b ≤ 2*L := by dsimp only [L]; omega
  have hUsed : b-L = k+r := by dsimp only [L]; omega
  let c := ⌈μ*(n:ℝ)⌉₊
  have hc : μ*(n:ℝ) ≤ (c:ℝ) := Nat.le_ceil _
  have hHalf : (b:ℝ) ≤ (2:ℝ)*(L:ℝ) := by exact_mod_cast hTwo
  have hSpend : (2:ℝ)*((k+r:ℕ):ℝ) ≤ μ*(L:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hHalf hμ
    nlinarith only [h,hGap]
  have hGap' : 2*(b-L)*n ≤ L*c := by
    rw [hUsed]
    have h := mul_le_mul_of_nonneg_right hSpend (Nat.cast_nonneg n)
    have hh := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg L)
    exact_mod_cast (show (2:ℝ)*((k+r:ℕ):ℝ)*(n:ℝ) ≤ (L:ℝ)*(c:ℝ) by nlinarith only [h,hh])
  have hSquare : 2*b*n ≤ c^2 := by
    have h := mul_le_mul_of_nonneg_right hSize (Nat.cast_nonneg n)
    have hh := mul_self_le_mul_self (mul_nonneg hμ (Nat.cast_nonneg n)) hc
    exact_mod_cast (show (2:ℝ)*(b:ℝ)*(n:ℝ) ≤ (c:ℝ)^2 by nlinarith only [h,hh])
  exact ⟨L,hUsed.ge,hL,hTwo,hGap',hSquare⟩

/-- Doubling the expansion window is sufficient on the ordinary
vertices when the exceptional set contains at most half of the host. -/
theorem preprocessing_ordinary_width {V : Type*} [Fintype V] (Z : Finset V) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ₁ : 2*τ ≤ 1) (hZ : 2*Z.card ≤ Fintype.card V) :
    τ*(Fintype.card V:ℝ) ≤ (2*τ)*(Zᶜ.card:ℝ) ∧
    (1-2*τ)*(Zᶜ.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ) := by
  have hSize : Zᶜ.card + Z.card = Fintype.card V := card_compl_add_card Z
  have hHalf : Fintype.card V ≤ 2*Zᶜ.card := by omega
  have hCard : Zᶜ.card ≤ Fintype.card V := by omega
  have hHalf' : (Fintype.card V:ℝ) ≤ (2:ℝ)*Zᶜ.card := by exact_mod_cast hHalf
  have hCard' : (Zᶜ.card:ℝ) ≤ Fintype.card V := by exact_mod_cast hCard
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left hHalf' hτ]
  · exact (mul_le_mul_of_nonneg_left hCard' (sub_nonneg.mpr hτ₁)).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hτ] : (1-2*τ:ℝ) ≤ 1-τ) (Nat.cast_nonneg _))

/-- The integer side constraints for the final degree correction
follow from the semidegree and density margins of Lemma 8.6. -/
theorem kuhn_osthus_preprocessing_graph_of_degree_margins
    {V : Type*} [Fintype V] {Z : Finset V} {label : V → Fin 50} {r l : ℕ}
    (G : Digraph V) (C : Fin r → OriginalExceptionalFactor label Z l) (R : Digraph ↥Zᶜ)
    (t k : ℕ) (ν τ μ α : ℝ)
    (hC : ∀ i, (C i).digraph ≤ G)
    (hDisC : Pairwise (fun i j => Disjoint (C i).digraph (C j).digraph))
    (hOrdC : ∀ v ∉ Z, inDegree (⨆ i, (C i).digraph) v ≤ r ∧ outDegree (⨆ i, (C i).digraph) v ≤ r)
    (hR : R ≤ induced (G \ (⨆ i, (C i).digraph)) Zᶜ)
    (hDegree : ∀ v, inDegree R v ≤ k ∧ outDegree R v ≤ k)
    (hG : IsRealRobust G ν τ) (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1) (hτ : 0 ≤ τ) (hτ₁ : 2*τ ≤ 1)
    (hZ : 2*Z.card ≤ Fintype.card V) (hSlots : 1 ≤ 50*l)
    (hBudget : μ*(Fintype.card V:ℝ)+(Z.card:ℝ)+(k+r*(50*l):ℕ) ≤ ν*(Fintype.card V:ℝ))
    (hGap : (4:ℝ)*((k+r:ℕ):ℝ) ≤ μ*((r*(50*l)+t:ℕ):ℝ))
    (hSize : (2:ℝ)*((r*(50*l)+t:ℕ):ℝ) ≤ μ^2*(Zᶜ.card:ℝ))
    (hRoom : (4*τ)*(Fintype.card V:ℝ)+2+((r*(50*l)+t+(k+r*(50*l))+Z.card:ℕ):ℝ) ≤
      α*(Fintype.card V:ℝ))
    (hIn : ∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree G v:ℝ))
    (hOut : ∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree G v:ℝ)) :
    ∃ P B : Digraph V, P ≤ G ∧ B ≤ P ∧ induced B Zᶜ = R ∧
      (∀ i, (C i).digraph ≤ P ∧ Disjoint (C i).digraph B) ∧
      ∀ v, let a := if v ∈ Z then r*(50*l+1) else r*(50*l+1)+t
        inDegree P v+r = a ∧ outDegree P v+r = a := by
  let b := r*(50*l)+t
  let w := ⌈(2*τ)*(Zᶜ.card:ℝ)⌉₊
  obtain ⟨L,hDemand,hL,hTwo,hDGap,hSquare⟩ :=
    preprocessing_degree_demand_parameters Zᶜ.card b k r μ hμ hμ₁ hGap hSize
  obtain ⟨hWidthLo,hWidthHi⟩ := preprocessing_ordinary_width Z τ hτ hτ₁ hZ
  have hZLe : (Zᶜ.card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ Zᶜ
  have hBudget' : μ*(Zᶜ.card:ℝ)+(Z.card:ℝ)+(k+r*(50*l):ℕ) ≤ ν*(Fintype.card V:ℝ) := by
    linarith only [hBudget,mul_le_mul_of_nonneg_left hZLe hμ]
  have hW : (w:ℝ) ≤ (2*τ)*(Zᶜ.card:ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hTotal : (2:ℝ)*(w:ℝ)+((b+(k+r*(50*l))+Z.card:ℕ):ℝ) ≤ α*(Fintype.card V:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hZLe (show (0:ℝ) ≤ 2*τ by positivity)
    nlinarith only [h,hW,hRoom]
  refine kuhn_osthus_preprocessing_graph_of_reserves G C R t k L ν τ μ (2*τ)
    hC hDisC hOrdC hR hDegree hG hμ hWidthLo hWidthHi hBudget' hSlots hDemand hL hTwo hDGap hSquare ?_ ?_
  · intro v
    change 2*w+b+(k+r*(50*l))+Z.card ≤ inDegree G v
    have h : 2*w+(b+(k+r*(50*l))+Z.card) ≤ inDegree G v := by exact_mod_cast hTotal.trans (hIn v)
    simpa only [Nat.add_assoc] using h
  · intro v
    change 2*w+b+(k+r*(50*l))+Z.card ≤ outDegree G v
    have h : 2*w+(b+(k+r*(50*l))+Z.card) ≤ outDegree G v := by exact_mod_cast hTotal.trans (hOut v)
    simpa only [Nat.add_assoc] using h

end OverfullWork.DirectedRobustExpansion
