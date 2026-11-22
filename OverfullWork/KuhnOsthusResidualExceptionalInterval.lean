module

public import OverfullWork.KuhnOsthusPhysicalExceptionalInterval

@[expose] public section


/-! Apply the two deletion budgets in Lemma 7.5 to one interval:
the exceptional budget controls endpoint availability, and the
ordinary budget controls the chord and successor pairs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

/-- The reduced pair gives all chord rectangles after restricting to
a style and deleting the prefix arcs. -/
theorem residual_style_chord_rectangles (G H : Digraph V) (hHG : H ≤ G)
    (U W A B : Finset V) (hA : A ⊆ U) (hB : B ⊆ W)
    (hAnon : A.Nonempty) (hBnon : B.Nonempty)
    (d ε η a : ℝ) (k e : ℕ) (hη : 0 < η) (hη1 : η ≤ 1) (ha : 0 ≤ a)
    (hScaleA : (U.card:ℝ)*ε ≤ (A.card:ℝ)*η)
    (hScaleB : (W.card:ℝ)*ε ≤ (B.card:ℝ)*η)
    (hTol : 2*(ε+a) ≤ η) (hBudget : (k:ℝ) ≤ a*((A.card:ℝ)*η))
    (hGap : η < d-ε-a) (hCutA : (A.card:ℝ)*η ≤ (e:ℝ)+1)
    (hCutB : (B.card:ℝ)*η ≤ (e:ℝ)+1)
    (hLoss : ∀ y ∈ W, inDegree H y ≤ k)
    (hReg : IsUniform G ε U W) (hDensity : d ≤ density G U W) :
    ∀ X ⊆ A, ∀ Y ⊆ B, e < X.card → e < Y.card → 0 < incidences (G \ H) X Y := by
  obtain ⟨hReg',hClose⟩ := uniform_on_pair_remainder G H hHG U W A B hA hB hAnon hBnon
    ε η a k hη hη1 hScaleA hScaleB hTol hBudget ha hLoss hReg
  apply chord_rectangles_of_uniform_residual_pair (G \ H) A B e η (d-ε-a) hReg' _ hGap hCutA hCutB
  linarith only [(abs_lt.mp hClose).1,hDensity]

/-- The lower density bound on a successor pair is independent of its
individual density parameter. Each actual parameter survives the trim. -/
theorem IsLowerSuperregularPair.on_residual_style_cells
    (G H : Digraph V) (hHG : H ≤ G)
    (U W A B : Finset V) (hA : A ⊆ U) (hB : B ⊆ W)
    (hAnon : A.Nonempty) (hBal : A.card = B.card)
    (K k : ℕ) (d ε η a : ℝ) (hK : 0 < K) (hε : 0 ≤ ε)
    (hη : 0 < η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hFloor : 2*ε ≤ d)
    (hSizeA : U.card = K*A.card) (hSizeB : W.card = K*B.card)
    (hRefA : UniformProfileCell (inProfile G) U A K ε)
    (hRefB : UniformProfileCell (outProfile G) W B K ε)
    (hTol : 2*(max 2 (K:ℝ)*ε+a) ≤ η)
    (hBudget : (k:ℝ) ≤ a*((A.card:ℝ)*η))
    (hLossOut : ∀ x ∈ U, outDegree H x ≤ k)
    (hLossIn : ∀ y ∈ W, inDegree H y ≤ k)
    (hG : IsLowerSuperregularPair G ε d U W) :
    IsLowerSuperregularPair (G \ H) η d A B := by
  obtain ⟨c,hc,hc1,hPair⟩ := hG
  have hc₀ : 0 ≤ c := by linarith only [hc,hFloor,hε]
  have hFloor' : 2*ε ≤ c := hFloor.trans hc
  exact ⟨c,hc,hc1,IsSuperregularPair.on_residual_style_cells G H hHG U W A B hA hB
    hAnon hBal K k c ε η a hK hc₀ hc1 hε hη hη1 ha hFloor' hSizeA hSizeB hRefA hRefB
    hTol hBudget hLossOut hLossIn hPair⟩

/-- Construct the complete exceptional system inside a residual graph
using neighbourhood and pair estimates in the original graph. -/
theorem exists_original_interval_after_prefix_deletion
    (d δ ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) (hTol : 2*δ ≤ ε) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {n : ℕ}
      (G H : Digraph W) (R : Digraph (Fin (n+1))) (Z Uₜ T : Finset W)
      (U C : Fin (n+1) → Finset W)
      (K m e endpointCap endpointBudget routeCap ordinaryLoss exceptionalLoss : ℕ)
      (ε₀ a η : ℝ),
      let A := univ.biUnion C ∪ T
      let E := (windingEndpointPositions (0 : Fin (n+1))).biUnion C
      let s := finRotate (n+1)
      let loss := endpointCap+(routeCap+2)+2*endpointCap
      H ≤ G →
      (∀ x ∉ Z, inDegree H x ≤ ordinaryLoss ∧ outDegree H x ≤ ordinaryLoss) →
      (∀ x ∈ Z, inDegree H x ≤ exceptionalLoss ∧ outDegree H x ≤ exceptionalLoss) →
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) →
      (∀ i, Disjoint (C i) T) → Disjoint A Z →
      (∀ i, (C i).card = m) → T.card = m →
      (∀ i, (U i).card = K*m) → Uₜ.card = K*m →
      (∀ i, C i ⊆ U i) → T ⊆ Uₜ →
      (∀ i, Disjoint (U i) Z) → Disjoint Uₜ Z →
      (∀ i, UniformProfileCell (inProfile G) (U i) (C i) K ε₀) →
      (∀ i, UniformProfileCell (outProfile G) (U i) (C i) K ε₀) →
      UniformProfileCell (outProfile G) Uₜ T K ε₀ →
      2*Z.card < endpointCap*(endpointBudget+1) →
      (∀ z ∈ Z, 2*Z.card+endpointBudget*m+exceptionalLoss < inNeighbours G E z) →
      (∀ z ∈ Z, 2*Z.card+endpointBudget*m+exceptionalLoss < outTo G E z) →
      2*(routeCap+2+2*endpointCap)+e < m-endpointCap →
      (∀ i, ¬R.Adj i i) →
      (∃ radius growth cutoff budget : ℕ, IsRobustAt R radius cutoff ∧ 0 < growth ∧
        2*(budget+1)+growth ≤ radius ∧
        (∀ i, cutoff+2*(budget+1) ≤ outDegree R i) ∧ (∀ i, cutoff ≤ inDegree R i) ∧
        Z.card*(2*((n+1)/growth+3)) < routeCap*(budget+1)) →
      loss < m → N ≤ m-loss →
      ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) →
      (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε →
      0 < K → 0 ≤ ε₀ → 0 ≤ a → 0 < η → η ≤ 1 →
      (K:ℝ)*ε₀ ≤ η → 2*(ε₀+a) ≤ η →
      (ordinaryLoss:ℝ) ≤ a*((m:ℝ)*η) →
      η < d-ε₀-a → (m:ℝ)*η ≤ (e:ℝ)+1 →
      0 < δ → δ ≤ 1 → 2*ε₀ ≤ d →
      2*(max 2 (K:ℝ)*ε₀+a) ≤ δ → (ordinaryLoss:ℝ) ≤ a*((m:ℝ)*δ) →
      (∀ i j, R.Adj i j → IsUniform G ε₀ (U i) (U j) ∧ d ≤ density G (U i) (U j)) →
      (∀ i, IsLowerSuperregularPair G ε₀ d (U i) (if s i = 0 then Uₜ else U (s i))) →
      Nonempty (OriginalInterval (G \ H) Z A (C 0) T) := by
  obtain ⟨N,hN⟩ := exists_original_interval_of_physical_pairs.{u}
    d δ ε ν τ γ hν hWidth hε hε1 hτγ hγ hd hCost hDegrees hTol
  refine ⟨N,?_⟩
  intro W _ n G H R Z Uₜ T U C K m e endpointCap endpointBudget routeCap ordinaryLoss exceptionalLoss
    ε₀ a η A E s loss hHG hOrd hExc hDis hTerm hAZ hSize hT hU hUT hUC hSubT hUZ hUTZ
    hRefIn hRefOut hRefT hBdg hIn hOut hRoom hLoop hRoutes hm hMin hHall hPay
    hK hε₀ ha hη hη1 hScale hCTol hCBudget hGap hCut hδ hδ1 hFloor hSTol hSBudget hReg hSup
  have hM : 0 < m := by omega
  have hNon (i : Fin (n+1)) : (C i).Nonempty := card_pos.mp (hM.trans_eq (hSize i).symm)
  have hScale' (i : Fin (n+1)) : ((U i).card:ℝ)*ε₀ ≤ ((C i).card:ℝ)*η := by
    rw [hU,hSize,Nat.cast_mul]
    have h := mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg m)
    nlinarith only [h]
  have hLoss (z : Z) : inDegree (G \ (G \ H)) z ≤ exceptionalLoss ∧
      outDegree (G \ (G \ H)) z ≤ exceptionalLoss := by
    have he : G \ (G \ H) = H := by
      ext x y
      simp only [Digraph.sdiff_adj]
      have h : H.Adj x y → G.Adj x y := fun h => hHG h
      tauto
    rw [he]
    exact hExc z z.prop
  have hIn' (z : W) (hz : z ∈ Z) :
      2*Z.card+endpointBudget*m < inNeighbours (G \ H) E z := by
    have h := (exceptional_style_neighbourhood_after_deletion G (G \ H) E z exceptionalLoss
      (fun _ _ h => h.1) (hLoss ⟨z,hz⟩).1 (hLoss ⟨z,hz⟩).2).1
    have hh := hIn z hz
    omega
  have hOut' (z : W) (hz : z ∈ Z) :
      2*Z.card+endpointBudget*m < outTo (G \ H) E z := by
    have h := (exceptional_style_neighbourhood_after_deletion G (G \ H) E z exceptionalLoss
      (fun _ _ h => h.1) (hLoss ⟨z,hz⟩).1 (hLoss ⟨z,hz⟩).2).2
    have hh := hOut z hz
    omega
  have hRect (i j : Fin (n+1)) (hij : R.Adj i j) := residual_style_chord_rectangles G H hHG
    (U i) (U j) (C i) (C j) (hUC i) (hUC j) (hNon i) (hNon j)
    d ε₀ η a ordinaryLoss e hη hη1 ha (hScale' i) (hScale' j) hCTol (by rwa [hSize i])
    hGap (by rwa [hSize i]) (by rwa [hSize j])
    (fun y hy => (hOrd y (fun hz => disjoint_left.mp (hUZ j) hy hz)).1) (hReg i j hij).1 (hReg i j hij).2
  have hSucc (i : Fin (n+1)) : IsLowerSuperregularPair (G \ H) δ d
      (C i) (if s i = 0 then T else C (s i)) := by
    have hl := hSup i
    have hSrc (x : W) (hx : x ∈ U i) : outDegree H x ≤ ordinaryLoss :=
      (hOrd x (fun hz => disjoint_left.mp (hUZ i) hx hz)).2
    by_cases h : s i = 0
    · rw [if_pos h] at hl ⊢
      exact IsLowerSuperregularPair.on_residual_style_cells G H hHG (U i) Uₜ (C i) T
        (hUC i) hSubT (hNon i) ((hSize i).trans hT.symm)
        K ordinaryLoss d ε₀ δ a hK hε₀ hδ hδ1 ha hFloor
        (by rw [hSize i]; exact hU i) (by rwa [hT]) (hRefIn i) hRefT hSTol (by rwa [hSize i]) hSrc
        (fun y hy => (hOrd y (fun hz => disjoint_left.mp hUTZ hy hz)).1) hl
    · rw [if_neg h] at hl ⊢
      exact IsLowerSuperregularPair.on_residual_style_cells G H hHG (U i) (U (s i)) (C i) (C (s i))
        (hUC i) (hUC (s i)) (hNon i) ((hSize i).trans (hSize (s i)).symm)
        K ordinaryLoss d ε₀ δ a hK hε₀ hδ hδ1 ha hFloor
        (by rw [hSize i]; exact hU i) (by rw [hSize (s i)]; exact hU (s i)) (hRefIn i) (hRefOut (s i)) hSTol (by rwa [hSize i]) hSrc
        (fun y hy => (hOrd y (fun hz => disjoint_left.mp (hUZ (s i)) hy hz)).1) hl
  exact hN (G \ H) R Z T C m e endpointCap endpointBudget routeCap hDis hTerm hAZ
    hSize hT hBdg hIn' hOut' hRoom hLoop hRoutes hRect hm hMin hHall hPay hSucc

end OverfullWork.DirectedRobustExpansion
