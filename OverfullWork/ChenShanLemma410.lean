module

public import OverfullWork.ChenShanTrianglePacking
public import OverfullWork.ChenShanTrianglePackingBounds
public import OverfullWork.ChenShanDenseTripartiteDegree

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real Filter
open scoped Classical

universe uA uB uW

/-- Chen–Shan, Lemma 4.10. Under the density and balance hypotheses of
Lemma 4.8, an edge-disjoint triangle packing leaves a locally balanced
graph of maximum degree at most ζm. -/
theorem exists_triangle_packing_with_small_balanced_leave (η ζ : ℝ)
    (hη : 0 < η) (hηhalf : η < 1/2) (hζ : 0 < ζ) :
    ∃ ε₀ : ℝ, ∃ m₀ : ℕ, 0 < ε₀ ∧ ∀ (m : ℕ), m₀ ≤ m →
    ∀ (A : Type uA) (B : Type uB) (W : Type uW) [Fintype A] [Fintype B] [Fintype W]
      (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop) (ε : ℝ),
      0 ≤ ε → ε ≤ ε₀ → DenseTripartite E L R m η ε →
      ∃ T ⊆ supportedTriangles E L R,
        (↑(triangleHypergraph T) : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
        ArcBalanced (packingLeave (tripartiteArcs E L R) (triangleHypergraph T)) ∧
        ∀ v, (incidentDegree (packingLeave (tripartiteArcs E L R) (triangleHypergraph T)) v : ℝ)
          ≤ ζ * m := by
  obtain ⟨mSample,hSample⟩ := exists_triangle_sample_threshold.{uA,uB,uW}
  obtain ⟨Δ₀,hPack⟩ := exists_triangle_packing_from_sample.{uA,uB,uW}
  obtain ⟨D,hD⟩ := eventually_atTop.mp (eventually_triangle_packing_bounds Δ₀ ζ hζ)
  obtain ⟨mBounds,hmBounds⟩ := exists_nat_gt (6 * max (1 : ℝ) D)
  refine ⟨min η (1/(32*(2+10/η))),max mSample (max mBounds 1),
    lt_min hη (by positivity),?_⟩
  intro m hm A B W _ _ _ E L R ε hε₀ hε hDense
  have hmSample : mSample ≤ m := (le_max_left _ _).trans hm
  have hmB : mBounds ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm0 : 0 < m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hεη : ε ≤ η := hε.trans (min_le_left _ _)
  have ⟨hkLower,hkUpper⟩ := hDense.color_count_bounds hm0 hη hηhalf hεη
  have hkNat : m ≤ 2 * Fintype.card W := by
    exact_mod_cast (show (m : ℝ) ≤ 2 * (Fintype.card W : ℝ) by linarith only [hkLower])
  have hFrac := bounded_fractional_triangle_decomposition_of_dense hDense hη hηhalf hε₀ hε
  obtain ⟨T,hT,hDegree⟩ := hSample m hmSample A B W E L R hDense.sizeA hDense.sizeB
    hkNat hDense.balanced hFrac
  let d := (Fintype.card W : ℝ) / 3
  let u := d ^ (2/3 : ℝ)
  let Δ := d + u
  have hmd : (m : ℝ) ≤ 6*d := by dsimp only [d]; linarith only [hkLower]
  have hdm : d ≤ m := by dsimp only [d]; linarith only [hkUpper,Nat.cast_nonneg (α := ℝ) m]
  have hmdBounds : (mBounds : ℝ) ≤ m := by exact_mod_cast hmB
  have hThreshold : D ≤ d :=
    (le_max_right _ _).trans (by linarith only [hmd,hmBounds,hmdBounds])
  obtain ⟨hd,hΔ,hExp,hHeavy,hdiff,hLoss⟩ := hD d hThreshold
  have hTCount : (T.card : ℝ) ≤ 2 * (m : ℝ)^3 := by
    have hCard : T.card ≤ m * (m * Fintype.card W) := by
      simpa only [card_univ,Fintype.card_prod,hDense.sizeA,hDense.sizeB] using
        (card_le_card (subset_univ T))
    have hCard' : (T.card : ℝ) ≤ (m : ℝ) * (m * (Fintype.card W : ℝ)) := by exact_mod_cast hCard
    calc
      _ ≤ _ := hCard'
      _ ≤ (m : ℝ) * (m * (2 * m)) := by gcongr
      _ = _ := by ring
  have hTExp : (T.card : ℝ) ≤ exp (Δ ^ ((1/900 : ℝ)^2)) := by
    refine hTCount.trans (le_trans ?_ hExp)
    calc
      2 * (m : ℝ)^3 ≤ 2 * (6*d)^3 := by gcongr
      _ = 432 * d^3 := by ring
  have hJCount : (Fintype.card (A ⊕ B ⊕ W) : ℝ) ≤ 4 * m := by
    simp only [Fintype.card_sum,Nat.cast_add,hDense.sizeA,hDense.sizeB]
    linarith only [hkUpper]
  have hJExp : (Fintype.card (A ⊕ B ⊕ W) : ℝ) ≤ exp (Δ ^ ((1/900 : ℝ)^2)) := by
    have hdCube : d ≤ d^3 := by
      calc
        d = d * 1^2 := by ring
        _ ≤ d * d^2 := by gcongr
        _ = _ := by ring
    exact hJCount.trans ((show 4 * (m : ℝ) ≤ 432*d^3 by linarith only [hmd,hdCube,hd]).trans hExp)
  have hDegrees := hDense.incidentDegree_bounds hη.le
    (hεη.trans hηhalf.le) hkUpper
  have hHeavy' (v : A ⊕ B ⊕ W) :
      2 * Δ ^ (3/2 : ℝ) ≤ (d-u) * incidentDegree (tripartiteArcs E L R) v :=
    hHeavy.trans (mul_le_mul_of_nonneg_left (hdm.trans (hDegrees v).1) hdiff)
  obtain ⟨M,hM,hMatching,hBalance,hResidual⟩ := hPack A B W E L R T d hd hΔ hT
    hDense.balanced hDegree hTExp hJExp hHeavy'
  refine ⟨M,hM.trans hT,?_,hBalance,?_⟩
  · intro S hS U hU hNe
    exact hMatching S hS U hU hNe
  intro v
  have hLossNN : 0 ≤ Δ ^ (-(1/900) : ℝ) + 2*d ^ (-(1/3) : ℝ) := by
    have hd0 : 0 ≤ d := zero_le_one.trans hd
    have hD0 : 0 ≤ Δ := add_nonneg hd0 (rpow_nonneg hd0 _)
    positivity
  refine (hResidual v).trans ?_
  calc
    _ ≤ (Δ ^ (-(1/900) : ℝ) + 2*d ^ (-(1/3) : ℝ)) * (4 * m) :=
      mul_le_mul_of_nonneg_left (hDegrees v).2 hLossNN
    _ = (4 * (Δ ^ (-(1/900) : ℝ) + 2*d ^ (-(1/3) : ℝ))) * m := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hLoss (Nat.cast_nonneg _)

end OverfullWork.ChenShan
