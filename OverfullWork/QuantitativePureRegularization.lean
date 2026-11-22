module

public import OverfullWork.ClusterEqualization
public import OverfullWork.PureGraphDeletionBudget

@[expose] public section


/-! Quantitative composition of vertex trimming, overloaded-cluster
discard and equalization. A fourth-power total loss gives a linear
exceptional margin. Initial directed regularity and rounding choices
remain explicit inputs. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRobustExpansion DirectedDegreeTrimming
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

theorem exceptional_fraction_budget (n e x M q k b C : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hE : (e:ℝ) ≤ θ*(n:ℝ)) (hX : (x:ℝ) ≤ θ^2*(n:ℝ))
    (hQ : θ*(M:ℝ) ≤ (q:ℝ)+1) (hEqual : (q:ℝ)*(k:ℝ) ≤ θ*(n:ℝ))
    (hBad : b*(q+1) ≤ x) (hCost : C ≤ e+x+M*b+q*k) : (C:ℝ) ≤ 4*θ*(n:ℝ) := by
  have hb : (b:ℝ)*((q:ℝ)+1) ≤ (x:ℝ) := by exact_mod_cast hBad
  have hMul := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg b : (0:ℝ) ≤ b)
  have hHeavy : (M:ℝ)*(b:ℝ) ≤ θ*(n:ℝ) := by
    apply (mul_le_mul_iff_right₀ hθ).mp
    nlinarith only [hb,hMul,hX]
  have hTheta := mul_le_mul_of_nonneg_left hθ1 hθ.le
  have hSquare := mul_le_mul_of_nonneg_right hTheta (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hCast : (C:ℝ) ≤ (e:ℝ)+(x:ℝ)+(M:ℝ)*(b:ℝ)+(q:ℝ)*(k:ℝ) := by exact_mod_cast hCost
  nlinarith only [hE,hX,hEqual,hHeavy,hSquare,hCast]

theorem bad_fraction_of_total (D H : Digraph V) (L : ℕ) (θ : ℝ)
    (hn : 0 < Fintype.card V) (hθ : 0 < θ)
    (hTotal : (total (D\H):ℝ) ≤ θ^4*(Fintype.card V:ℝ)^2/2)
    (hThreshold : θ^2*(Fintype.card V:ℝ) ≤ (L:ℝ)+1) :
    ((bad (D\H) L).card:ℝ) ≤ θ^2*(Fintype.card V:ℝ) := by
  have hBad : ((bad (D\H) L).card:ℝ)*((L:ℝ)+1) ≤ 2*(total (D\H):ℝ) := by
    exact_mod_cast bad_budget (D\H) L
  have hMult := mul_le_mul_of_nonneg_left hThreshold (Nat.cast_nonneg (bad (D\H) L).card : (0:ℝ) ≤ _)
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
  have hPos : 0 < θ^2*(Fintype.card V:ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hPos).mp
  nlinarith only [hBad,hMult,hTotal]

theorem exists_small_exception_equalization (D H : Digraph V) (f : V → Option I)
    (M q L : ℕ) (θ : ℝ) (hM : 0 < M) (hHalf : 2*q ≤ M)
    (hSize : ∀ i,(cluster f i).card=M) (hn : 0 < Fintype.card V)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hE : ((exceptional f).card:ℝ) ≤ θ*(Fintype.card V:ℝ))
    (hTotal : (total (D\H):ℝ) ≤ θ^4*(Fintype.card V:ℝ)^2/2)
    (hThreshold : θ^2*(Fintype.card V:ℝ) ≤ (L:ℝ)+1)
    (hQ : θ*(M:ℝ) ≤ (q:ℝ)+1)
    (hEqual : (q:ℝ)*(Fintype.card I:ℝ) ≤ θ*(Fintype.card V:ℝ)) :
    ∃ g : V → Option (retained f (bad (D\H) L) q),
      (∀ i,(cluster g i).card=M-q) ∧ 0 < M-q ∧
      (∀ i,cluster g i ⊆ cluster f i.val) ∧
      ((exceptional g).card:ℝ) ≤ 4*θ*(Fintype.card V:ℝ) ∧
      (∀ v,g v ≠ none → inDegree (D\H) v ≤ L ∧ outDegree (D\H) v ≤ L) := by
  let X := bad (D\H) L
  have hqm : q ≤ M := by omega
  have hTarget : M-q+q=M := Nat.sub_add_cancel hqm
  obtain ⟨g,hNew,hSub,hCost⟩ := exists_redistributed_equalization f X q (M-q) M
    (Nat.sub_le _ _) (fun i => by rw [hTarget,hSize]) (fun i => (hSize i).le)
  have hRet : (retained f X q).card ≤ Fintype.card I := card_le_univ _
  have hCost' : (exceptional g).card ≤ (exceptional f).card+X.card+
      M*(overloaded f X q).card+q*Fintype.card I := by
    have hDiff : M-(M-q)=q := by omega
    rw [hDiff] at hCost
    have hMul := Nat.mul_le_mul_left q hRet
    omega
  have hX := bad_fraction_of_total D H L θ hn hθ hTotal hThreshold
  have hFinal := exceptional_fraction_budget (Fintype.card V) (exceptional f).card X.card M q
    (Fintype.card I) (overloaded f X q).card (exceptional g).card θ hθ hθ1 hE hX hQ hEqual
    (overloaded_budget f X q) hCost'
  refine ⟨g,hNew,by omega,?_,hFinal,?_⟩
  · intro i
    exact (hSub i).trans (by rw [cluster_redistribute];exact sdiff_subset)
  · exact nonexceptional_property_of_fibre_subsets (redistribute f X q) g hSub _
      (redistributed_loss_bounds D H f L q)

theorem paper_margins_of_small_exception (e L n : ℕ) (θ ν α : ℝ)
    (hE : (e:ℝ) ≤ 4*θ*(n:ℝ)) (hL : (L:ℝ) ≤ 2*θ*(n:ℝ))
    (hQuarter : θ ≤ 1/16) (hNu : θ ≤ ν/24) (hAlpha : θ ≤ α/12) :
    (e:ℝ) ≤ (n:ℝ)/4 ∧ (e:ℝ)+(L:ℝ) ≤ ν*(n:ℝ)/4 ∧
      (e:ℝ)+(L:ℝ) ≤ α*(n:ℝ)/2 := by
  have h₁ := mul_le_mul_of_nonneg_right hQuarter (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have h₂ := mul_le_mul_of_nonneg_right hNu (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have h₃ := mul_le_mul_of_nonneg_right hAlpha (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  constructor
  · linarith only [hE,h₁]
  constructor <;> linarith only [hE,hL,h₂,h₃]

theorem floor_ceil_regularization_choices (n M k : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hHalf : θ ≤ 1/2) (hLarge : 1 ≤ θ*(n:ℝ))
    (hOrder : M*k ≤ n) :
    2*⌊θ*(M:ℝ)⌋₊ ≤ M ∧
    θ*(M:ℝ) ≤ (⌊θ*(M:ℝ)⌋₊:ℝ)+1 ∧
    (⌊θ*(M:ℝ)⌋₊:ℝ)*(k:ℝ) ≤ θ*(n:ℝ) ∧
    θ^2*(n:ℝ) ≤ (⌈θ^2*(n:ℝ)⌉₊:ℝ)+1 ∧
    (⌈θ^2*(n:ℝ)⌉₊:ℝ) ≤ 2*θ*(n:ℝ) := by
  have hFloor := Nat.floor_le (mul_nonneg hθ.le (Nat.cast_nonneg M : (0:ℝ) ≤ M))
  have hFloorUpper := Nat.lt_floor_add_one (θ*(M:ℝ))
  have hHalfM := mul_le_mul_of_nonneg_right hHalf (Nat.cast_nonneg M : (0:ℝ) ≤ M)
  have hTwo : 2*⌊θ*(M:ℝ)⌋₊ ≤ M := by
    have hh : (2:ℝ)*(⌊θ*(M:ℝ)⌋₊:ℝ) ≤ (M:ℝ) := by linarith only [hFloor,hHalfM]
    exact_mod_cast hh
  have hOrderR : (M:ℝ)*(k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hOrder
  have hQk := mul_le_mul_of_nonneg_right hFloor (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  have hNk := mul_le_mul_of_nonneg_left hOrderR hθ.le
  have hCeil := Nat.le_ceil (θ^2*(n:ℝ))
  have hCeilUpper := Nat.ceil_lt_add_one (show 0 ≤ θ^2*(n:ℝ) by positivity)
  have hTheta : θ^2 ≤ θ := by nlinarith only [hθ,hHalf]
  have hSquareN := mul_le_mul_of_nonneg_right hTheta (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  exact ⟨hTwo,hFloorUpper.le,by nlinarith only [hQk,hNk],by linarith only [hCeil],
    by linarith only [hCeilUpper,hSquareN,hLarge]⟩

theorem fourth_power_pure_budget (D : Digraph V) (f : V → Option I) (M : ℕ) (ε d θ : ℝ)
    (hθ : 0 ≤ θ) (hd : 0 ≤ d) (hSize : ∀ i,(cluster f i).card=M)
    (hE : ((exceptional f).card:ℝ) ≤ θ^4*(Fintype.card V:ℝ)/16)
    (hDefects : ((defectivePairs D f ε).card:ℝ) ≤ θ^4*(Fintype.card I:ℝ)^2/8)
    (hDensity : d ≤ θ^4/8) :
    (total (D\restrictPairs D f (regularReduced D f ε d)):ℝ) ≤ θ^4*(Fintype.card V:ℝ)^2/2 := by
  have hBase := regular_pure_deletion_budget D f ε d M hd (fun i => (hSize i).le)
  have hOrder : (M:ℝ)*(Fintype.card I:ℝ) ≤ (Fintype.card V:ℝ) := by
    have hh := order_eq f M hSize
    have hn : M*Fintype.card I ≤ Fintype.card V := by omega
    exact_mod_cast hn
  have hSquared := mul_self_le_mul_self (show (0:ℝ) ≤ (M:ℝ)*(Fintype.card I:ℝ) by positivity) hOrder
  have hSquare : (M:ℝ)^2*(Fintype.card I:ℝ)^2 ≤ (Fintype.card V:ℝ)^2 := by nlinarith only [hSquared]
  have hScale := mul_le_mul_of_nonneg_left hSquare (show (0:ℝ) ≤ θ^4/8 by positivity)
  have hExc := mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  have hDef := mul_le_mul_of_nonneg_right hDefects (sq_nonneg (M:ℝ))
  have hDens := mul_le_mul_of_nonneg_right hDensity
    (show (0:ℝ) ≤ (M:ℝ)^2*(Fintype.card I:ℝ)^2 by positivity)
  have hPos : 0 ≤ θ^4*(Fintype.card V:ℝ)^2 := by positivity
  nlinarith only [hBase,hScale,hExc,hDef,hDens,hPos]

end OverfullWork.DirectedClusterQuotient
