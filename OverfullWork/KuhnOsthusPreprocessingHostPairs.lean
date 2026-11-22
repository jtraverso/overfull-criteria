module

public import OverfullWork.KuhnOsthusExceptionalPairStability
public import OverfullWork.KuhnOsthusResidualExtender
public import OverfullWork.RegularPairArcPartition
public import OverfullWork.OsthusStadenTrimmedCopies

@[expose] public section


/-! The normalized host pairs for the extender after the exceptional
factors have been removed, as in Kühn–Osthus Lemmas 7.1 and 8.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {V W : Type*} [Fintype V] [Fintype W]

/-- The dense host pair retains its nominal centre when the
regularity tolerance pays for the bounded deletion. -/
theorem IsCentredRegular.after_preprocessing_deletion
    {D H : Digraph W} {ε η δ d : ℝ} (hD : IsCentredRegular D ε d) (k : ℕ)
    (hH : H ≤ D) (hW : 0 < Fintype.card W) (hη : 0 < η) (hη₁ : η ≤ 1)
    (hδ : 0 ≤ δ) (hScale : ε ≤ η) (hTol : 2*(ε+δ) ≤ η)
    (hBudget : (k:ℝ) ≤ δ*((Fintype.card W:ℝ)*η)) (hLoss : ∀ y, inDegree H y ≤ k) :
    IsCentredRegular (D \ H) η d := by
  have hNon : (univ : Finset W).Nonempty := card_pos.mp (by simpa only [card_univ] using hW)
  have hSize : ((univ : Finset W).card:ℝ)*ε ≤ ((univ : Finset W).card:ℝ)*η :=
    mul_le_mul_of_nonneg_left hScale (by positivity)
  obtain ⟨hUniform,hClose⟩ := uniform_on_pair_remainder D H hH univ univ univ univ
    Subset.rfl Subset.rfl hNon hNon ε η δ k hη hη₁ hSize hSize hTol
    (by simpa only [card_univ] using hBudget) hδ (fun y _ => hLoss y) hD.1
  refine ⟨hUniform,(abs_sub_le _ (density D univ univ) _).trans ?_⟩
  linarith only [hClose,hD.2,hTol,hδ]

private theorem cut_semidegree_le (D : Digraph V) (a b : W ↪ V) (out : Bool) (x : W) :
    pairSemidegree out (pullDirectedPair a b D) x ≤
      pairSemidegree out D (if out then a x else b x) := by
  rw [pullDirectedPair_semidegree]
  cases out <;> exact card_le_card (filter_subset_filter _ (subset_univ _))

/-- Read a residual host pair in the same coordinates as the original
pair. A bound on the global deletion at its vertices pays for
regularity, both minimum semidegrees and all fixed style degrees. -/
theorem preprocessing_successor_pairs_after_deletion
    (G L : Digraph V) (a b : W ↪ V) (A B : Fin 50 → Finset W)
    (d ε η δ θ aStyle : ℝ) (k : ℕ)
    (hL : L ≤ G) (hW : 0 < Fintype.card W)
    (hη : 0 < η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ) (hScale : ε ≤ η) (hTol : 2*(ε+δ) ≤ η)
    (hBudget : (k:ℝ) ≤ δ*((Fintype.card W:ℝ)*η))
    (hPay : (k:ℝ) ≤ (η-ε)*(Fintype.card W:ℝ))
    (hLoss : ∀ x, inDegree L (b x) ≤ k ∧ outDegree L (a x) ≤ k)
    (hθ : θ ≤ d-ε) (hθ₁ : θ ≤ 1)
    (hMargin : aStyle*d*(Fintype.card W:ℝ)+(k:ℝ) ≤ (1-θ)*((d-ε)*(Fintype.card W:ℝ)/50))
    (hReg : IsCentredRegular (pullDirectedPair a b G) ε d)
    (hDeg : ∀ v, (d-ε)*(Fintype.card W:ℝ) ≤ inDegree (pullDirectedPair a b G) v ∧
      (d-ε)*(Fintype.card W:ℝ) ≤ outDegree (pullDirectedPair a b G) v)
    (hIn : ∀ v j, UniformProfileCell (fun _ : Unit =>
      univ.filter (fun x => G.Adj (a x) (b v))) univ (A j) 50 θ)
    (hOut : ∀ v j, UniformProfileCell (fun _ : Unit =>
      univ.filter (fun x => G.Adj (a v) (b x))) univ (B j) 50 θ) :
    let D := pullDirectedPair a b (G \ L)
    IsCentredRegular D η d ∧
      (∀ v, (d-η)*(Fintype.card W:ℝ) ≤ inDegree D v ∧
        (d-η)*(Fintype.card W:ℝ) ≤ outDegree D v) ∧
      ∀ v j, aStyle*d*(Fintype.card W:ℝ) ≤ inNeighbours D (A j) v ∧
        aStyle*d*(Fintype.card W:ℝ) ≤ outTo D (B j) v := by
  let Q := pullDirectedPair a b G
  let J := pullDirectedPair a b L
  intro D
  have hD : D = Q \ J := by ext x y; rfl
  rw [hD]
  have hJ : J ≤ Q := fun _ _ h => hL h
  have hDegJ (v : W) : inDegree J v ≤ k ∧ outDegree J v ≤ k :=
    ⟨(cut_semidegree_le L a b false v).trans (hLoss v).1,
      (cut_semidegree_le L a b true v).trans (hLoss v).2⟩
  refine ⟨IsCentredRegular.after_preprocessing_deletion hReg k hJ hW hη hη₁ hδ hScale hTol
    hBudget (fun y => (hDegJ y).1),?_,?_⟩
  · intro v
    obtain ⟨hi,ho⟩ := residual_semidegrees Q J hJ v
    have hi' : (inDegree (Q \ J) v:ℝ)+inDegree J v = inDegree Q v := by exact_mod_cast hi
    have ho' : (outDegree (Q \ J) v:ℝ)+outDegree J v = outDegree Q v := by exact_mod_cast ho
    have hbi : (inDegree J v:ℝ) ≤ k := by exact_mod_cast (hDegJ v).1
    have hbo : (outDegree J v:ℝ) ≤ k := by exact_mod_cast (hDegJ v).2
    exact ⟨by linarith only [hi',hbi,(hDeg v).1,hPay],
      by linarith only [ho',hbo,(hDeg v).2,hPay]⟩
  · intro v j
    apply successor_style_degree_after_host_deletion Q J (A j) (B j) v (d-ε) θ _ k
      hθ hθ₁ (hDeg v).1 (hDeg v).2 (hIn v j) (hOut v j)
      (fun x => (hDegJ x).1) (fun x => (hDegJ x).2) hMargin

end OverfullWork.DirectedRobustExpansion
