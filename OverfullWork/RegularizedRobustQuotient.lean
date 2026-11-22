module

public import OverfullWork.QuantitativePureRegularization
public import OverfullWork.ExceptionalProtectedQuotient

@[expose] public section


/-! At least half the original clusters survive quantitative trimming.
Compose the actual equalization, rounding and loss budgets with the
normalized quotient transfer. Initial partition data remain inputs. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRobustExpansion DirectedDegreeTrimming
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

theorem retained_at_least_half (f : V → Option I) (X : Finset V) (M q : ℕ) (θ : ℝ)
    (hM : 0 < M) (hSize : ∀ i,(cluster f i).card=M)
    (hθ : 0 < θ) (hθQuarter : θ ≤ 1/4)
    (hE : ((exceptional f).card:ℝ) ≤ θ*(Fintype.card V:ℝ))
    (hX : (X.card:ℝ) ≤ θ^2*(Fintype.card V:ℝ))
    (hQ : θ*(M:ℝ) ≤ (q:ℝ)+1) :
    Fintype.card I ≤ 2*(retained f X q).card := by
  have hB := overloaded_budget f X q
  have hb : ((overloaded f X q).card:ℝ)*((q:ℝ)+1) ≤ (X.card:ℝ) := by exact_mod_cast hB
  have hMul := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg (overloaded f X q).card : (0:ℝ) ≤ _)
  have hHeavy : (M:ℝ)*((overloaded f X q).card:ℝ) ≤ θ*(Fintype.card V:ℝ) := by
    apply (mul_le_mul_iff_right₀ hθ).mp
    nlinarith only [hb,hMul,hX]
  have hOrder : (Fintype.card V:ℝ)=((exceptional f).card:ℝ)+(M:ℝ)*(Fintype.card I:ℝ) := by
    exact_mod_cast order_eq f M hSize
  have hθn := mul_le_mul_of_nonneg_right hθQuarter (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  have hOrderBound : (Fintype.card V:ℝ) ≤ 2*(M:ℝ)*(Fintype.card I:ℝ) := by
    linarith only [hOrder,hE,hθn]
  have hScaled := mul_le_mul_of_nonneg_left hOrderBound hθ.le
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hBadCount : ((overloaded f X q).card:ℝ) ≤ 2*θ*(Fintype.card I:ℝ) := by
    apply (mul_le_mul_iff_right₀ hMR).mp
    nlinarith only [hHeavy,hScaled]
  have hθk := mul_le_mul_of_nonneg_right hθQuarter (Nat.cast_nonneg (Fintype.card I) : (0:ℝ) ≤ _)
  have hHalf : 2*(overloaded f X q).card ≤ Fintype.card I := by
    have hh : (2:ℝ)*((overloaded f X q).card:ℝ) ≤ (Fintype.card I:ℝ) := by
      linarith only [hBadCount,hθk]
    exact_mod_cast hh
  have hCount := retained_card_loss f X q
  omega

theorem cluster_margin_of_half (k k' : ℕ) (ν : ℝ) (hν : 0 ≤ ν)
    (hHalf : k ≤ 2*k') (hInitial : 8 ≤ ν*(k:ℝ)) : 4 ≤ ν*(k':ℝ) := by
  have hHalfR : (k:ℝ) ≤ 2*(k':ℝ) := by exact_mod_cast hHalf
  have hh := mul_le_mul_of_nonneg_left hHalfR hν
  linarith only [hh,hInitial]

theorem exists_regularized_robust_quotient_with_loss (D H : Digraph V) (hLe : H ≤ D)
    (f : V → Option I) (M : ℕ) (θ ν τ α : ℝ)
    (hM : 0 < M) (hSize : ∀ i,(cluster f i).card=M)
    (hθ : 0 < θ) (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/24) (hθα : θ ≤ α/12)
    (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hLarge : 1 ≤ θ*(Fintype.card V:ℝ))
    (hClusters : 8 ≤ ν*(Fintype.card I:ℝ)) (hOrder : 2 ≤ τ*(Fintype.card V:ℝ))
    (hE : ((exceptional f).card:ℝ) ≤ θ*(Fintype.card V:ℝ))
    (hTotal : (total (D\H):ℝ) ≤ θ^4*(Fintype.card V:ℝ)^2/2)
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) :
    let L := ⌈θ^2*(Fintype.card V:ℝ)⌉₊
    let q := ⌊θ*(M:ℝ)⌋₊
    ∃ g : V → Option (retained f (bad (D\H) L) q),
      (∀ i,(cluster g i).card=M-q) ∧ 0 < M-q ∧
      (∀ i,cluster g i ⊆ cluster f i.val) ∧
      ((exceptional g).card:ℝ) ≤ 4*θ*(Fintype.card V:ℝ) ∧
      IsRealRobust (quotient H g) (ν/2) (2*τ) ∧
      (∀ j,(α/2)*(Fintype.card (retained f (bad (D\H) L) q):ℝ) ≤ (inDegree (quotient H g) j:ℝ)) ∧
      (∀ j,(α/2)*(Fintype.card (retained f (bad (D\H) L) q):ℝ) ≤ (outDegree (quotient H g) j:ℝ)) ∧
      ∀ v, g v ≠ none → inDegree (D \ H) v ≤ L ∧ outDegree (D \ H) v ≤ L := by
  dsimp only
  let L := ⌈θ^2*(Fintype.card V:ℝ)⌉₊
  let q := ⌊θ*(M:ℝ)⌋₊
  have hn : 0 < Fintype.card V := by
    by_contra hh
    have hz : Fintype.card V=0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero] at hLarge
    norm_num at hLarge
  have hMk : M*Fintype.card I ≤ Fintype.card V := by
    have hh := order_eq f M hSize;omega
  obtain ⟨hHalf,hQ,hEqual,hThreshold,hL⟩ := floor_ceil_regularization_choices
    (Fintype.card V) M (Fintype.card I) θ hθ (by linarith only [hθSmall]) hLarge hMk
  obtain ⟨g,hNew,hm,hSub,hFinal,hLoss⟩ := exists_small_exception_equalization D H f M q L θ
    hM hHalf hSize hn hθ (by linarith only [hθSmall]) hE hTotal hThreshold hQ hEqual
  have hBad := bad_fraction_of_total D H L θ hn hθ hTotal hThreshold
  have hRet := retained_at_least_half f (bad (D\H) L) M q θ hM hSize hθ
    (by linarith only [hθSmall]) hE hBad hQ
  have hScale : 4 ≤ ν*(Fintype.card (retained f (bad (D\H) L) q):ℝ) := by
    rw [Fintype.card_coe]
    exact cluster_margin_of_half _ _ ν hν.le hRet hClusters
  obtain ⟨hExc,hSmall,hDegree⟩ := paper_margins_of_small_exception (exceptional g).card L
    (Fintype.card V) θ ν α hFinal hL hθSmall hθν hθα
  obtain ⟨hR,hI,hO⟩ := real_quotient_transfer_nonexceptional D H hLe g (M-q) L hm hNew
    ν τ α hν hτ hα hRobust hIn hOut (fun v hv => (hLoss v hv).1)
    (fun v hv => (hLoss v hv).2) hScale hOrder hExc hSmall hDegree
  exact ⟨g,hNew,hm,hSub,hFinal,hR,hI,hO,hLoss⟩

/-- Recover the quotient while keeping only its expansion, degrees and partition. -/
theorem exists_regularized_robust_quotient (D H : Digraph V) (hLe : H ≤ D)
    (f : V → Option I) (M : ℕ) (θ ν τ α : ℝ)
    (hM : 0 < M) (hSize : ∀ i,(cluster f i).card=M)
    (hθ : 0 < θ) (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/24) (hθα : θ ≤ α/12)
    (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hLarge : 1 ≤ θ*(Fintype.card V:ℝ))
    (hClusters : 8 ≤ ν*(Fintype.card I:ℝ)) (hOrder : 2 ≤ τ*(Fintype.card V:ℝ))
    (hE : ((exceptional f).card:ℝ) ≤ θ*(Fintype.card V:ℝ))
    (hTotal : (total (D\H):ℝ) ≤ θ^4*(Fintype.card V:ℝ)^2/2)
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) :
    let L := ⌈θ^2*(Fintype.card V:ℝ)⌉₊
    let q := ⌊θ*(M:ℝ)⌋₊
    ∃ g : V → Option (retained f (bad (D\H) L) q),
      (∀ i,(cluster g i).card=M-q) ∧ 0 < M-q ∧
      (∀ i,cluster g i ⊆ cluster f i.val) ∧
      ((exceptional g).card:ℝ) ≤ 4*θ*(Fintype.card V:ℝ) ∧
      IsRealRobust (quotient H g) (ν/2) (2*τ) ∧
      (∀ j,(α/2)*(Fintype.card (retained f (bad (D\H) L) q):ℝ) ≤ (inDegree (quotient H g) j:ℝ)) ∧
      (∀ j,(α/2)*(Fintype.card (retained f (bad (D\H) L) q):ℝ) ≤ (outDegree (quotient H g) j:ℝ)) := by
  obtain ⟨g,hNew,hm,hSub,hFinal,hR,hI,hO,_⟩ :=
    exists_regularized_robust_quotient_with_loss D H hLe f M θ ν τ α hM hSize
      hθ hθSmall hθν hθα hν hτ hα hLarge hClusters hOrder hE hTotal hRobust hIn hOut
  exact ⟨g,hNew,hm,hSub,hFinal,hR,hI,hO⟩

end OverfullWork.DirectedClusterQuotient
