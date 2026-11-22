module

public import OverfullWork.KuhnOsthusPreprocessingExtender
public import OverfullWork.KuhnOsthusPreprocessingConstruction

@[expose] public section


/-! Complete the preprocessing graph by the degree demands of
Kühn–Osthus Lemma 8.6 after choosing its two sparse reserves. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 700000 in
/-- A physical partition, its 50-refinement and the original factors
on that refinement determine a preprocessing graph. The regularity and
degree-demand margins of Lemmas 7.1, 8.2 and 5.2 are explicit. -/
theorem kuhn_osthus_lemma_8_6_of_exceptional_factors
    (d d₀ ε ξ δ ζ η θ aStyle : ℝ) (q : ℕ) (hq : 0 < q)
    (hd : 0 < d) (hd1 : d ≤ 1) (hd₀ : 0 < d₀) (hSmall : d₀ ≤ d/4)
    (hε : 0 < ε) (hξ : 0 < ξ) (hξε : ξ ≤ ε) (hξ₁ : ξ ≤ 1) (hRel : 4*ξ ≤ ε*d)
    (hξd : ξ ≤ d/4) (hζ : ζ ≤ 1/2) (hη : 0 < η)
    (hCut : 4*η ≤ ε^3*(d₀/(q:ℕ))) (hMax : 2*η ≤ d₀/(q:ℕ))
    (hCodeg : η ≤ (d₀/(q:ℕ))^2) (hMin : 4*η ≤ d₀)
    (hδ : 0 ≤ δ) (hθ₁ : θ ≤ 1) (hStyle : aStyle ≤ (1-θ)/50) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {Z : Finset V} {r l : ℕ} {label : V → Fin 50}
      (G : Digraph V) (R : Digraph (Fin q))
      (X : Fin q → Finset V) (C : Fin 50 × Fin q → Finset V)
      (F : Fin r → OriginalExceptionalFactor label Z l)
      (m t k L : ℕ) (ε₀ ν τ μ σ : ℝ),
      let s := finRotate q
      let E := ⨆ i, (F i).digraph
      N ≤ 50*m → 0 < m →
      (∀ i, (F i).digraph ≤ G) → (Pairwise (fun i j => Disjoint (F i).digraph (F j).digraph)) →
      (∀ x ∉ Z, inDegree E x ≤ r ∧ outDegree E x ≤ r) →
      (∀ i, (X i).card = 50*m) → (∀ i j, i ≠ j → Disjoint (X i) (X j)) →
      (∀ i, Disjoint (X i) Z) → (∀ x ∉ Z, ∃ i, x ∈ X i) →
      (∀ j, (C j).card = m ∧ C j ⊆ X j.2) →
      (∀ i, (univ : Finset (Fin 50)).biUnion (fun j => C (j,i)) = X i) →
      (∀ j x, x ∈ C j → label x = j.1) →
      (∀ j, UniformProfileCell (inProfile G) (X j.2) (C j) 50 θ ∧
        UniformProfileCell (outProfile G) (X j.2) (C j) 50 θ) →
      (∀ i j, R.Adj i j → IsUniform G ε₀ (X i) (X j) ∧ d ≤ density G (X i) (X j)) →
      (∀ i, IsLowerSuperregularPair G ε₀ d (X i) (X (s i))) →
      0 ≤ ε₀ → ε₀ ≤ ξ → 2*(ε₀+δ) ≤ ξ → θ ≤ d-ε₀ →
      (r:ℝ) ≤ δ*((50*m)*ξ) → (r:ℝ) ≤ (ξ-ε₀)*(50*m) →
      aStyle*d*(50*m)+(r:ℝ) ≤ (1-θ)*((d-ε₀)*(50*m)/50) →
      (8*d₀/d)*(50*m) ≤ (k:ℝ) → IsRealRobust G ν τ → 0 ≤ μ →
      τ*(Fintype.card V:ℝ) ≤ σ*(Zᶜ.card:ℝ) →
      (1-σ)*(Zᶜ.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ) →
      μ*(Zᶜ.card:ℝ)+(Z.card:ℝ)+(k+r*(50*l):ℕ) ≤ ν*(Fintype.card V:ℝ) →
      1 ≤ 50*l → k+r ≤ r*(50*l)+t-L → L ≤ r*(50*l)+t → r*(50*l)+t ≤ 2*L →
      2*(r*(50*l)+t-L)*Zᶜ.card ≤ L*⌈μ*(Zᶜ.card:ℝ)⌉₊ →
      2*(r*(50*l)+t)*Zᶜ.card ≤ ⌈μ*(Zᶜ.card:ℝ)⌉₊^2 →
      (∀ v, 2*⌈σ*(Zᶜ.card:ℝ)⌉₊+(r*(50*l)+t)+(k+r*(50*l))+Z.card ≤ inDegree G v) →
      (∀ v, 2*⌈σ*(Zᶜ.card:ℝ)⌉₊+(r*(50*l)+t)+(k+r*(50*l))+Z.card ≤ outDegree G v) →
      ∃ (cluster : ↥Zᶜ → Fin q) (H S : Digraph ↥Zᶜ) (P B : Digraph V),
        (∀ i x, cluster x = i ↔ x.val ∈ X i) ∧
        Disjoint H S ∧ H ⊔ S ≤ induced (G \ E) Zᶜ ∧
        ExtenderPairBounds R H S cluster (fun x => label x.val) m d₀ (d₀/(q:ℕ)) ε
          ((aStyle*d₀-η)*(50*m)) ((d₀/(d/2))^2*(50*m)) ∧
        (∀ x, (inDegree (H ⊔ S) x:ℝ) + outDegree (H ⊔ S) x ≤ (8*d₀/d)*(50*m)) ∧
        P ≤ G ∧ B ≤ P ∧ induced B Zᶜ = H ⊔ S ∧
        (∀ i, (F i).digraph ≤ P ∧ Disjoint (F i).digraph B) ∧
        ∀ v, let a := if v ∈ Z then r*(50*l+1) else r*(50*l+1)+t
          inDegree P v+r = a ∧ outDegree P v+r = a := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  obtain ⟨N,hN⟩ := exists_preprocessing_extender_after_exceptional_deletion.{u}
    d d₀ ε ξ δ ζ η θ aStyle q hd hd1 hd₀ hSmall hε hξ hξε hξ₁ hRel hξd hζ hη hCut hMax
    hCodeg hMin hδ hθ₁ hStyle
  refine ⟨N,?_⟩
  intro V _ Z r l label G R X C F m t k L ε₀ ν τ μ σ s E hn hm hF hDisF hLoss hSize hDis hOrd hCover
    hCell hCellCover hLabel hProfiles hRegular hSuccessor hε₀ hScale hTol hθ hBudget hPay hMargin
    hK hG hμ hWidthLow hWidthHigh hBudgetG hSlots hRoom hL hTwo hGap hSquare hIn hOut
  obtain ⟨cluster,H,S,hCoord,hDisjoint,hSub,hPairs,hDegSum⟩ := hN G E Z R X C label m r ε₀
    hn hm (iSup_le hF) hLoss hSize hDis hOrd hCover hCell hCellCover hLabel hProfiles hRegular
    hSuccessor hε₀ hScale hTol hθ hBudget hPay hMargin
  have hDegree (v : ↥Zᶜ) : inDegree (H ⊔ S) v ≤ k ∧ outDegree (H ⊔ S) v ≤ k := by
    have hv : inDegree (H ⊔ S) v + outDegree (H ⊔ S) v ≤ k := by
      exact_mod_cast (show ((inDegree (H ⊔ S) v:ℕ):ℝ) + outDegree (H ⊔ S) v ≤ (k:ℝ) from
        (hDegSum v).trans hK)
    exact ⟨by omega,by omega⟩
  obtain ⟨P,B,hP,hB,hInd,hKeep,hReg⟩ := kuhn_osthus_preprocessing_graph_of_reserves
    G F (H ⊔ S) t k L ν τ μ σ hF hDisF hLoss hSub hDegree hG hμ hWidthLow hWidthHigh
    hBudgetG hSlots hRoom hL hTwo hGap hSquare hIn hOut
  exact ⟨cluster,H,S,P,B,hCoord,hDisjoint,hSub,hPairs,hDegSum,hP,hB,hInd,hKeep,hReg⟩

end OverfullWork.DirectedRobustExpansion
