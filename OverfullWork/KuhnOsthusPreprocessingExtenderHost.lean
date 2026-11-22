module

public import OverfullWork.KuhnOsthusPreprocessingHostPairs
public import OverfullWork.KuhnOsthusWrappedPairCoordinates

@[expose] public section


/-! The common host for Lemma 8.2 after removing the exceptional factors
in Lemma 8.6. The exceptional vertices are outside the sampled pairs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
variable {V W I : Type*} [Fintype V] [Fintype W]

/-- Each physical style cell restricts the very same neighbourhood
counts when pulled back to the normalized cluster coordinates. -/
theorem UniformProfileCell.pull_embedding {J : Type*}
    (e : W ↪ V) (A : Finset W) (p : J → V → Prop) (k : ℕ) (ε : ℝ)
    (h : UniformProfileCell (fun j => univ.filter (p j)) (univ.map e) (A.map e) k ε) :
    UniformProfileCell (fun j => univ.filter (fun w => p j (e w))) univ A k ε := by
  intro j hj
  rw [profile_pull_embedding e A (p j),profile_pull_embedding e univ (p j)]
  rw [profile_pull_embedding e univ (p j)] at hj
  exact h j (by simpa only [card_map] using hj)

/-- Remove the actual union of exceptional arcs. The reduced arcs and
the successor arcs retain their density centres, and only ordinary
semidegrees of the deletion are charged to the style cells. -/
theorem preprocessing_extender_host_after_exceptional_deletion
    (G L : Digraph V) (Z : Finset V) (a : I → W ↪ ↥Zᶜ)
    (s : I → I) (R : Digraph I) (A : I → Fin 50 → Finset W)
    (c : I → I → ℝ) (r : ℕ) (ε η δ θ d aStyle : ℝ)
    (hL : L ≤ G) (hW : 0 < Fintype.card W)
    (hη : 0 < η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ) (hScale : ε ≤ η) (hTol : 2*(ε+δ) ≤ η)
    (hBudget : (r:ℝ) ≤ δ*((Fintype.card W:ℝ)*η))
    (hPay : (r:ℝ) ≤ (η-ε)*(Fintype.card W:ℝ))
    (hLoss : ∀ x ∉ Z, inDegree L x ≤ r ∧ outDegree L x ≤ r)
    (hθ : θ ≤ d-ε) (hθ₁ : θ ≤ 1) (hStyle : aStyle ≤ (1-θ)/50)
    (hMargin : aStyle*d*(Fintype.card W:ℝ)+(r:ℝ) ≤ (1-θ)*((d-ε)*(Fintype.card W:ℝ)/50)) :
    let b i := (a i).trans (Function.Embedding.subtype (· ∈ Zᶜ))
    let P i j := pullDirectedPair (b i) (b j) G
    let Q i j := pullDirectedPair (a i) (a j) (induced (G \ L) Zᶜ)
    (∀ i, d ≤ c i (s i)) →
    (∀ i j, s i = j ∨ R.Adj i j → IsCentredRegular (P i j) ε (c i j)) →
    (∀ i v, (c i (s i)-ε)*(Fintype.card W:ℝ) ≤ inDegree (P i (s i)) v ∧
      (c i (s i)-ε)*(Fintype.card W:ℝ) ≤ outDegree (P i (s i)) v) →
    (∀ i j, UniformProfileCell (inProfile G) (univ.map (b i)) ((A i j).map (b i)) 50 θ ∧
      UniformProfileCell (outProfile G) (univ.map (b i)) ((A i j).map (b i)) 50 θ) →
    (∀ i j, s i = j ∨ R.Adj i j → IsCentredRegular (Q i j) η (c i j)) ∧
    (∀ i v, (c i (s i)-η)*(Fintype.card W:ℝ) ≤ inDegree (Q i (s i)) v ∧
      (c i (s i)-η)*(Fintype.card W:ℝ) ≤ outDegree (Q i (s i)) v) ∧
    ∀ i v j, aStyle*c i (s i)*(Fintype.card W:ℝ) ≤ inNeighbours (Q i (s i)) (A i j) v ∧
      aStyle*c i (s i)*(Fintype.card W:ℝ) ≤ outTo (Q i (s i)) (A (s i) j) v := by
  intro b P Q hDen hReg hDeg hProfiles
  have hOrd (i : I) (x : W) : (b i x) ∉ Z := mem_compl.mp (a i x).property
  have hNext (i : I) := preprocessing_successor_pairs_after_deletion G L (b i) (b (s i))
    (A i) (A (s i)) (c i (s i)) ε η δ θ aStyle r hL hW hη hη₁ hδ hScale hTol hBudget hPay
    (fun x => ⟨(hLoss _ (hOrd (s i) x)).1, (hLoss _ (hOrd i x)).2⟩)
    (hθ.trans (sub_le_sub_right (hDen i) ε)) hθ₁ (by
      have hShift := mul_le_mul_of_nonneg_right hStyle
        (mul_nonneg (sub_nonneg.mpr (hDen i)) (Nat.cast_nonneg (Fintype.card W)))
      linarith only [hShift,hMargin]) (hReg i (s i) (.inl rfl)) (hDeg i)
    (fun v j => UniformProfileCell.pull_embedding (b i) (A i j)
      (fun _ : Unit => fun x => G.Adj x (b (s i) v)) 50 θ
      (fun _ => (hProfiles i j).1 (b (s i) v)))
    (fun v j => UniformProfileCell.pull_embedding (b (s i)) (A (s i) j)
      (fun _ : Unit => G.Adj (b i v)) 50 θ (fun _ => (hProfiles (s i) j).2 (b i v)))
  refine ⟨?_,fun i => (hNext i).2.1,fun i => (hNext i).2.2⟩
  intro i j hEdge
  let J := pullDirectedPair (b i) (b j) L
  have hJ : J ≤ P i j := fun _ _ h => hL h
  have hIncoming (v : W) : inDegree J v ≤ r := by
    change pairSemidegree false (pullDirectedPair (b i) (b j) L) v ≤ r
    rw [pullDirectedPair_semidegree]
    exact (card_le_card (filter_subset_filter _ (subset_univ _))).trans (hLoss _ (hOrd j v)).1
  change IsCentredRegular (P i j \ J) η (c i j)
  exact IsCentredRegular.after_preprocessing_deletion (hReg i j hEdge) r hJ hW hη hη₁ hδ
    hScale hTol hBudget hIncoming

end OverfullWork.DirectedRobustExpansion
