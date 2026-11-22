module

public import OverfullWork.KuhnOsthusPreprocessingExtenderHost
public import OverfullWork.KuhnOsthusPreprocessingLayout
public import OverfullWork.KuhnOsthusRegularCyclePair
public import OverfullWork.KuhnOsthusExtenderCoordinates
public import OverfullWork.DirectedPairEnergy

@[expose] public section


/-! Sample the path-system extender in the ordinary host left by the
original exceptional factors, as in Kühn–Osthus Lemma 8.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 650000 in
/-- The reduced regular pairs and superregular successor pairs in the
physical partition supply both sparse reserves of Lemma 8.2 after the
exceptional deletion. The style labels are those of the original cells. -/
theorem exists_preprocessing_extender_after_exceptional_deletion
    (d d₀ ε ξ δ ζ η θ aStyle : ℝ) (q : ℕ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hd₀ : 0 < d₀) (hSmall : d₀ ≤ d/4)
    (hε : 0 < ε) (hξ : 0 < ξ) (hξε : ξ ≤ ε) (hξ₁ : ξ ≤ 1) (hRel : 4*ξ ≤ ε*d)
    (hξd : ξ ≤ d/4) (hζ : ζ ≤ 1/2) (hη : 0 < η)
    (hCut : 4*η ≤ ε^3*(d₀/((q+1):ℕ))) (hMax : 2*η ≤ d₀/((q+1):ℕ))
    (hCodeg : η ≤ (d₀/((q+1):ℕ))^2) (hMin : 4*η ≤ d₀)
    (hδ : 0 ≤ δ) (hθ₁ : θ ≤ 1) (hStyle : aStyle ≤ (1-θ)/50) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V]
      (G E : Digraph V) (Z : Finset V) (R : Digraph (Fin (q+1)))
      (X : Fin (q+1) → Finset V) (C : Fin 50 × Fin (q+1) → Finset V)
      (label : V → Fin 50) (m r : ℕ) (ε₀ : ℝ),
      let s := finRotate (q+1)
      N ≤ 50*m → 0 < m → E ≤ G →
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
      ∃ (cluster : ↥Zᶜ → Fin (q+1)) (H S : Digraph ↥Zᶜ),
        (∀ i x, cluster x = i ↔ x.val ∈ X i) ∧
        Disjoint H S ∧ H ⊔ S ≤ induced (G \ E) Zᶜ ∧
        ExtenderPairBounds R H S cluster (fun x => label x.val) m d₀ (d₀/((q+1):ℕ)) ε
          ((aStyle*d₀-η)*(50*m)) ((d₀/(d/2))^2*(50*m)) ∧
        ∀ x, (inDegree (H ⊔ S) x:ℝ) + outDegree (H ⊔ S) x ≤ (8*d₀/d)*(50*m) := by
  obtain ⟨N,hN⟩ := exists_physical_extender_with_style_degrees.{0,u}
    d d₀ ξ ε ζ η aStyle q hd hd1 hd₀ hSmall hε hξε hRel hξd hζ hη hCut hMax hCodeg hMin
  refine ⟨N,?_⟩
  intro V _ G E Z R X C label m r ε₀ s hNmin hm hE hLoss hSize hDis hOrd hCover
    hCell hCellCover hLabel hProfiles hRegular hSuccessor hε₀ hScale hTol hθ hBudget hPay hMargin
  obtain ⟨a,cluster,hCoord,hMap,hStyleMap,hStyleSize⟩ :=
    exists_ordinary_cluster_style_coordinates Z X C label m hSize hDis hOrd hCover hCell hCellCover hLabel
  let b i := (a i).trans (Function.Embedding.subtype (· ∈ Zᶜ))
  let A i j := univ.filter (fun w => label (a i w).val = j)
  let P i j := pullDirectedPair (b i) (b j) G
  have hMapB (i : Fin (q+1)) : univ.map (b i) = X i := hMap i
  have hStyleMapB (i : Fin (q+1)) (j : Fin 50) : (A i j).map (b i) = C (j,i) := hStyleMap i j
  choose cNext hNextLow hNextHigh hNext using hSuccessor
  let c i j := if s i = j then cNext i else if R.Adj i j then density G (X i) (X j) else d
  have hCNext (i : Fin (q+1)) : c i (s i) = cNext i := if_pos rfl
  have hDen (i j : Fin (q+1)) : d ≤ c i j ∧ c i j ≤ 1 := by
    by_cases he : s i = j
    · simp only [c,if_pos he]
      exact ⟨hNextLow i,hNextHigh i⟩
    · by_cases hr : R.Adj i j
      · simp only [c,if_neg he,if_pos hr]
        exact ⟨(hRegular i j hr).2,DirectedPairEnergy.density_le_one _ _ _⟩
      · simp only [c,if_neg he,if_neg hr]
        exact ⟨le_rfl,hd1⟩
  have hSuper (i : Fin (q+1)) : IsCentredSuperregular (P i (s i)) ε₀ (c i (s i)) := by
    apply (centred_superregular_iff_pair_univ _ _ _).mpr
    apply superregular_pullDirectedPair
    rw [hMapB,hMapB,hCNext]
    exact hNext i
  have hReg (i j : Fin (q+1)) (hEdge : s i = j ∨ R.Adj i j) : IsCentredRegular (P i j) ε₀ (c i j) := by
    by_cases he : s i = j
    · subst j
      exact (hSuper i).1
    · have hr := hEdge.resolve_left he
      constructor
      · apply uniform_pullDirectedPair
        rw [hMapB,hMapB]
        exact (hRegular i j hr).1
      · rw [density_pullDirectedPair,hMapB,hMapB]
        simpa only [c,if_neg he,if_pos hr,sub_self,abs_zero] using hε₀
  have hPos : 0 < Fintype.card (Fin (50*m)) := by simp only [Fintype.card_fin]; omega
  have hHost := preprocessing_extender_host_after_exceptional_deletion G E Z a s R A c r ε₀ ξ δ θ d aStyle
    hE hPos hξ hξ₁ hδ hScale hTol (by simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using hBudget)
    (by simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using hPay) hLoss hθ hθ₁ hStyle
    (by simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using hMargin)
    (fun i => (hDen i (s i)).1) hReg (fun i v => by
      obtain ⟨hi,ho⟩ := (hSuper i).2 v
      exact ⟨by linarith only [(abs_le.mp hi).1],by linarith only [(abs_le.mp ho).1]⟩)
    (fun i j => by
      change UniformProfileCell (inProfile G) (univ.map (b i)) ((A i j).map (b i)) 50 θ ∧
        UniformProfileCell (outProfile G) (univ.map (b i)) ((A i j).map (b i)) 50 θ
      rw [hMapB,hStyleMapB]
      exact hProfiles (j,i))
  obtain ⟨H,S,hDisjoint,hSub,hPairs,hDegree⟩ := hN (induced (G \ E) Zᶜ) R a cluster
    (fun x => label x.val) c m (by simpa only [Fintype.card_fin] using hNmin) (Fintype.card_fin _)
    hCoord hStyleSize hDen hHost.1 hHost.2.1 hHost.2.2
  refine ⟨cluster,H,S,?_,hDisjoint,hSub,hPairs,hDegree⟩
  intro i x
  rw [hCoord,←hMap i]
  simpa only [mem_map,mem_univ,true_and,Subtype.ext_iff] using
    (show (∃ w, (a i w).val = x.val) ↔ (∃ w, b i w = x.val) from Iff.rfl)

end OverfullWork.DirectedRobustExpansion
