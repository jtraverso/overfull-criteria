module

public import OverfullWork.HeavyPairReassembly

@[expose] public section


/-! # Source parameters pay the full heavy-pair factorization reserves

The linear engine's large coefficient depends only on the density
margin. Its order reserve is paid by strengthening the original sparse
scale Q; it is not an additional hypothesis on a residual graph.
-/
namespace OverfullWork.HeavyPairPeeling
open Gate8J2I
set_option maxHeartbeats 8000000

theorem strong_scaled_density (ε : ℝ) (C n d : ℕ)
    (hCε : 64 ≤ ε*(C:ℝ))
    (hdense : ((1:ℝ)/2+ε)*(n:ℝ) ≤ (d:ℝ)) : (C+128)*n ≤ 2*C*d := by
  have h₁ := mul_le_mul_of_nonneg_left hdense (show 0 ≤ 2*(C:ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hCε (Nat.cast_nonneg n)
  exact_mod_cast (show ((C:ℝ)+128)*(n:ℝ) ≤ 2*(C:ℝ)*(d:ℝ) by nlinarith only [h₁,h₂])

theorem source_linear_reserves (C Q n m d q B Y : ℕ)
    (hC : 4000 ≤ C) (hQ : 2 ≤ Q) (hCQ : C ≤ Q)
    (hAQ : (10:ℕ)^24*C^6 ≤ Q) (hn : 64*Q ≤ n)
    (hCard : n+1 = 2*(m+1)+Y)
    (hB : B ≤ 6*(n/(4096*Q^2))+6) (hY : Y ≤ n/(4096*Q^2)+1)
    (hHeavy : q ≤ n/(64*Q)) (hdense : (C+128)*n ≤ 2*C*d) :
    linearHalfBound C (B+1) ≤ m ∧ (C+64)*m ≤ C*(d-2*q) := by
  let k := n/(4096*Q^2)
  have hcoef : 64*Q ≤ 4096*Q^2 := by nlinarith only [hQ]
  have hk : 64*Q*k ≤ n :=
    (Nat.mul_le_mul_right k hcoef).trans (Nat.mul_div_le n (4096*Q^2))
  have hK : k ≤ Q*k := by nlinarith only [hQ,Nat.zero_le k]
  change B ≤ 6*k+6 at hB
  change Y ≤ k+1 at hY
  have hQbudget : Q*(6*k+7) ≤ m := by
    nlinarith only [hk,hn,hY,hCard,hQ,hK]
  have hBmul : (10:ℕ)^24*C^6*(B+1) ≤ Q*(6*k+7) :=
    (Nat.mul_le_mul_left _ (show B+1 ≤ 6*k+7 by omega)).trans
      (Nat.mul_le_mul_right (6*k+7) hAQ)
  have hsize : linearHalfBound C (B+1) ≤ m := hBmul.trans hQbudget
  have hqmul : 64*Q*q ≤ n :=
    (Nat.mul_le_mul_left (64*Q) hHeavy).trans (Nat.mul_div_le n (64*Q))
  have hCq : 4*C*q ≤ n :=
    (Nat.mul_le_mul_right q (by nlinarith only [hCQ,hQ] : 4*C ≤ 64*Q)).trans hqmul
  have hWeak : n ≤ 2*d := by nlinarith only [hdense,hC]
  have h128 : 128*q ≤ n :=
    (Nat.mul_le_mul_right q (by omega : 128 ≤ 64*Q)).trans hqmul
  have hqd : 2*q ≤ d := by omega
  have hr : d-2*q+2*q = d := Nat.sub_add_cancel hqd
  have hm : 2*m ≤ n := by omega
  have hdenseCore : (C+64)*m ≤ C*(d-2*q) := by
    nlinarith only [hdense,hCq,hr,hm,Nat.zero_le n,Nat.zero_le C]
  exact ⟨hsize,hdenseCore⟩

end OverfullWork.HeavyPairPeeling
