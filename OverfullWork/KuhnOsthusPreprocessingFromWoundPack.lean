module

public import OverfullWork.KuhnOsthusExceptionalFactorSequence
public import OverfullWork.KuhnOsthusWoundPreprocessingInput

@[expose] public section


/-! Apply Lemma 8.6 directly to the first call to Lemma 7.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 850000 in
/-- The first winding pack supplies the cells and factors of
Lemma 8.6. The ordinary extender and the preprocessing graph
are both built after these factors have been selected. -/
theorem kuhn_osthus_preprocessing_reserve_from_wound_pack
    (d d₀ ε ξ δ ζ η θ aStyle : ℝ) (l j : ℕ) (hl : 2 ≤ l) (hj : 0 < j)
    (hd : 0 < d) (hd1 : d ≤ 1) (hd₀ : 0 < d₀) (hSmall : d₀ ≤ d/4)
    (hε : 0 < ε) (hξ : 0 < ξ) (hξε : ξ ≤ ε) (hξ₁ : ξ ≤ 1) (hRel : 4*ξ ≤ ε*d)
    (hξd : ξ ≤ d/4) (hζ : ζ ≤ 1/2) (hη : 0 < η)
    (hCut : 4*η ≤ ε^3*(d₀/((l*j:ℕ):ℝ))) (hMax : 2*η ≤ d₀/((l*j:ℕ):ℝ))
    (hCodeg : η ≤ (d₀/((l*j:ℕ):ℝ))^2) (hMin : 4*η ≤ d₀)
    (hδ : 0 ≤ δ) (hθ₁ : θ ≤ 1) (hStyle : aStyle ≤ (1-θ)/50) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {m r : ℕ}
      (G : Digraph V) (Z : Finset V) (R : Digraph (Fin (l*j))) (X : Fin (l*j) → Finset V)
      (t k L : ℕ) (ε₀ ν τ μ σ : ℝ),
      N ≤ 50*m → 0 < m →
      (∀ i, (X i).card = 50*m) → (∀ i i', i ≠ i' → Disjoint (X i) (X i')) →
      (∀ i, Disjoint (X i) Z) → (∀ x ∉ Z, ∃ i, x ∈ X i) →
      (∀ i i', R.Adj i i' → IsUniform G ε₀ (X i) (X i') ∧ d ≤ density G (X i) (X i')) →
      (∀ i, IsLowerSuperregularPair G ε₀ d (X i) (X (finRotate (l*j) i))) →
      0 ≤ ε₀ → ε₀ ≤ ξ → 2*(ε₀+δ) ≤ ξ → θ ≤ d-ε₀ →
      (r:ℝ) ≤ δ*((50*m)*ξ) → (r:ℝ) ≤ (ξ-ε₀)*(50*m) →
      aStyle*d*(50*m)+(r:ℝ) ≤ (1-θ)*((d-ε₀)*(50*m)/50) →
      (8*d₀/d)*(50*m) ≤ (k:ℝ) → IsRealRobust G ν τ → 0 ≤ μ →
      τ*(Fintype.card V:ℝ) ≤ σ*(Zᶜ.card:ℝ) →
      (1-σ)*(Zᶜ.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ) →
      μ*(Zᶜ.card:ℝ)+(Z.card:ℝ)+(k+r*(50*l):ℕ) ≤ ν*(Fintype.card V:ℝ) →
      k+r ≤ r*(50*l)+t-L → L ≤ r*(50*l)+t → r*(50*l)+t ≤ 2*L →
      2*(r*(50*l)+t-L)*Zᶜ.card ≤ L*⌈μ*(Zᶜ.card:ℝ)⌉₊ →
      2*(r*(50*l)+t)*Zᶜ.card ≤ ⌈μ*(Zᶜ.card:ℝ)⌉₊^2 →
      (∀ v, 2*⌈σ*(Zᶜ.card:ℝ)⌉₊+(r*(50*l)+t)+(k+r*(50*l))+Z.card ≤ inDegree G v) →
      (∀ v, 2*⌈σ*(Zᶜ.card:ℝ)⌉₊+(r*(50*l)+t)+(k+r*(50*l))+Z.card ≤ outDegree G v) →
      ∀ E : WoundFactorPacking G Z X hj 50 m r θ,
        ∃ (label : V → Fin 50) (cluster : ↥Zᶜ → Fin (l*j)) (H S : Digraph ↥Zᶜ) (PG B : Digraph V),
          (∀ i x, x ∈ E.cell i → label x = i.1) ∧
          (∀ i x, cluster x = i ↔ x.val ∈ X i) ∧
          Disjoint H S ∧ H ⊔ S ≤ induced (G \ (⨆ i, ⨆ a, (E.factors i a).digraph)) Zᶜ ∧
          ExtenderPairBounds R H S cluster (fun x => label x.val) m d₀ (d₀/((l*j:ℕ):ℝ)) ε
            ((aStyle*d₀-η)*(50*m)) ((d₀/(d/2))^2*(50*m)) ∧
          (∀ x, (inDegree (H ⊔ S) x:ℝ) + outDegree (H ⊔ S) x ≤ (8*d₀/d)*(50*m)) ∧
          PG ≤ G ∧ B ≤ PG ∧ induced B Zᶜ = H ⊔ S ∧
          (⨆ i, ⨆ a, (E.factors i a).digraph) ≤ PG ∧
          Disjoint (⨆ i, ⨆ a, (E.factors i a).digraph) B ∧
          ∀ x, let D := if x ∈ Z then 50*l*r else 50*l*r+t
            inDegree PG x = D ∧ outDegree PG x = D := by
  have hq : 0 < l*j := Nat.mul_pos (by omega) hj
  obtain ⟨N,hN⟩ := kuhn_osthus_lemma_8_6_of_exceptional_factors.{u}
    d d₀ ε ξ δ ζ η θ aStyle (l*j) hq hd hd1 hd₀ hSmall
    hε hξ hξε hξ₁ hRel hξd hζ hη hCut hMax hCodeg hMin hδ hθ₁ hStyle
  refine ⟨N,?_⟩
  intro V _ m r G Z R X t k L ε₀ ν τ μ σ hNm hm hSize hDis hOrd hCover hReg hSup
    hε₀ hScale hTol hθ hBudget hPay hMargin hK hG hμ hWidthLow hWidthHigh hBudgetG
    hRoom hL hTwo hGap hSquare hIn hOut E
  have hCellOrd (i : Fin 50 × Fin (l*j)) : Disjoint (E.cell i) Z :=
    (hOrd i.2).mono_left (E.size i).2
  have hCellCover (x : V) (hx : x ∉ Z) : ∃ i, x ∈ E.cell i := by
    obtain ⟨i,hi⟩ := hCover x hx
    rw [←E.cover i] at hi
    obtain ⟨a,_,ha⟩ := mem_biUnion.mp hi
    exact ⟨(a,i),ha⟩
  obtain ⟨label,F,hLabel,hF,hLe,hApart,hLoss⟩ :=
    winding_preprocessing_inputs G Z E.cell m hl hj (fun i => (E.size i).1)
      E.disjoint hCellOrd hCellCover E.factors E.apart
  obtain ⟨cluster,H,S,PG,B,hCoord,hSep,hSub,hPairs,hSum,hPG,hB,hInd,hKeep,hDegree⟩ :=
    hN G R X E.cell F m t k L ε₀ ν τ μ σ hNm hm hLe hApart
      (fun x hx => ⟨(hLoss x hx).1.le,(hLoss x hx).2.le⟩)
      hSize hDis hOrd hCover E.size E.cover hLabel E.profiles hReg hSup
      hε₀ hScale hTol hθ hBudget hPay hMargin hK hG hμ hWidthLow hWidthHigh hBudgetG
      (by omega) hRoom hL hTwo hGap hSquare hIn hOut
  simp only [hF] at hSub hKeep
  have hSlots : r*(50*l+1) = 50*l*r+r := by ring
  refine ⟨label,cluster,H,S,PG,B,hLabel,hCoord,hSep,hSub,hPairs,hSum,hPG,hB,hInd,
    iSup_le (fun i => (hKeep i).1),?_,?_⟩
  · apply disjoint_iff_inf_le.mpr
    rintro x y ⟨ha,hb⟩
    obtain ⟨i,hi⟩ := Digraph.iSup_adj.mp ha
    exact disjoint_iff_inf_le.mp (hKeep i).2 ⟨hi,hb⟩
  · intro x
    obtain ⟨hi,ho⟩ := hDegree x
    rw [hSlots] at hi ho
    by_cases hx : x ∈ Z
    · rw [if_pos hx] at hi ho ⊢
      omega
    · rw [if_neg hx] at hi ho ⊢
      omega

end OverfullWork.DirectedRobustExpansion
