module

public import OverfullWork.KuhnOsthusSparsePairExpansion
public import OverfullWork.KuhnOsthusRobustPairMerge

@[expose] public section


/-! Compose Lemma 4.11 with the local replacement in Lemma 6.4. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u

/-- With the paper's codegree and relative-density hypotheses on the
identified pair, a local replacement coalesces every orbit meeting it. -/
theorem exists_cut_merge_of_sparse_superregular_pair
    (d ε μ ζ ν τ γ : ℝ) (hd : 0 < d) (hε : 0 < ε) (hε1 : ε < 1)
    (hμ : 0 < μ) (hζ : 0 < ζ) (hν : 0 < ν) (hτ : 2*ν ≤ τ)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hGamma : γ ≤ ζ*d)
    (hScale : 160*ε ≤ (ζ*μ)^2)
    (hDiscard : 8*ν ≤ τ*(ζ*d)^2) (hνDensity : ν < (1-ε)*d*ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (σ : Equiv.Perm V) (S : Finset V) (D : Digraph S),
      N ≤ S.card → (16:ℝ)*S.card ≤ (ζ*d*S.card)^2 →
      (∀ v, ζ*d*(S.card:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, ζ*d*(S.card:ℝ) ≤ (outDegree D v:ℝ)) →
      (∀ x y, x ≠ y → (commonInNeighbours D x y:ℝ) ≤ (d/μ)^2*S.card) →
      (∀ x y, x ≠ y → (commonInNeighbours (reverseArcs D) x y:ℝ) ≤ (d/μ)^2*S.card) →
      (∀ A B : Finset S, ε*(S.card:ℝ) ≤ (A.card:ℝ) → ε*(S.card:ℝ) ≤ (B.card:ℝ) →
        (1-ε)*d*(A.card:ℝ)*(B.card:ℝ) ≤ (incidences D A B:ℝ)) →
      ∃ M : Equiv.Perm (↑S), (∀ x, D.Adj x (M x)) ∧
        (∀ x y, σ.SameCycle x y → (replacedSuccessor σ S M).SameCycle x y) ∧
        ∀ x y, touchesCut σ S x → touchesCut σ S y →
          (replacedSuccessor σ S M).SameCycle x y := by
  have hντ : ν ≤ τ := by linarith
  obtain ⟨N,hN⟩ := exists_cut_merge_of_robust_reserve.{u} ν τ γ hν hντ hτγ hγ
  refine ⟨max 1 N,?_⟩
  intro V _ σ S D hn hDiagonal hIn hOut hcI hcO hReg
  apply hN σ S D ((le_max_right _ _).trans hn)
  · have hS : 0 < S.card := (le_max_left _ _).trans hn
    apply kuhn_osthus_sparse_pair_expansion D d ε μ ζ ν τ
      (by simpa only [Fintype.card_coe] using hS) hd hε hε1 hμ hζ hν hτ hScale
      (by simpa only [Fintype.card_coe] using hDiagonal) hDiscard hνDensity
    · simpa only [Fintype.card_coe] using hIn
    · simpa only [Fintype.card_coe] using hOut
    · simpa only [Fintype.card_coe] using hcI
    · simpa only [Fintype.card_coe] using hcO
    · simpa only [Fintype.card_coe] using hReg
  · intro v
    exact (mul_le_mul_of_nonneg_right hGamma (Nat.cast_nonneg _)).trans (hIn v)
  · intro v
    exact (mul_le_mul_of_nonneg_right hGamma (Nat.cast_nonneg _)).trans (hOut v)

end OverfullWork.DirectedRobustExpansion
