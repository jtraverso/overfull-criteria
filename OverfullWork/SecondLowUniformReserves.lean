module

public import OverfullWork.SecondLowFiniteExclusion

@[expose] public section


/-! Uniform arithmetic for the two-centre endpoint.
All scale choices precede the graph and its actual terminal data. -/
namespace OverfullWork.SecondLowUniformReserves
open Gate8J2I
set_option maxHeartbeats 12000000

theorem finite_reserves (C Q n D B K : ℕ) (hC : 4000 ≤ C) (hCQ : C ≤ Q)
    (hLQ : (10:ℕ)^24*C^6 ≤ Q) (hn : 256*Q ≤ n)
    (hB : B ≤ 6*(n/(4096*Q^2))+6) (hK : K ≤ n/(4096*Q^2)+1)
    (hScaled : (C+128)*n ≤ 2*C*D) :
    2*linearHalfBound C (6*B+1)+K+1 ≤ n ∧
    n+30*B+12 ≤ 2*D ∧ (C+64)*n ≤ 2*C*(D-6*B) := by
  let k := n/(4096*Q^2)
  let L := (10:ℕ)^24*C^6
  have hQ : 2 ≤ Q := by omega
  have hL : 1 ≤ L := by
    have hh : 0 < L := by dsimp only [L];positivity
    omega
  have hFloor := Nat.mul_div_le n (4096*Q^2)
  change 4096*Q^2*k ≤ n at hFloor
  have hCoefC : 1024*C ≤ 4096*Q^2 := by nlinarith only [hCQ,hQ]
  have hCoefL : 1024*L ≤ 4096*Q^2 := by change L ≤ Q at hLQ;nlinarith only [hLQ,hQ]
  have hFloorC : 1024*C*k ≤ n := (Nat.mul_le_mul_right k hCoefC).trans hFloor
  have hFloorL : 1024*L*k ≤ n := (Nat.mul_le_mul_right k hCoefL).trans hFloor
  have hnC : 256*C ≤ n := (Nat.mul_le_mul_left 256 hCQ).trans hn
  have hnL : 256*L ≤ n := (Nat.mul_le_mul_left 256 hLQ).trans hn
  have hCB := Nat.mul_le_mul_left C hB
  have hLB := Nat.mul_le_mul_left L hB
  have hkL : k ≤ L*k := by simpa using Nat.mul_le_mul_right k hL
  change C*B ≤ C*(6*k+6) at hCB
  change L*B ≤ L*(6*k+6) at hLB
  change K ≤ k+1 at hK
  have hReserve : C*(30*B+12) ≤ n := by nlinarith only [hCB,hFloorC,hnC]
  have hSlack : n+30*B+12 ≤ 2*D := by
    apply Nat.le_of_mul_le_mul_left (c:=C) ?_ (by omega)
    nlinarith only [hScaled,hReserve]
  refine ⟨?_,hSlack,?_⟩
  · change 2*(L*(6*B+1))+K+1 ≤ n
    nlinarith only [hLB,hFloorL,hnL,hkL,hK,hL]
  · have hSub : D-6*B+6*B=D := Nat.sub_add_cancel (by omega)
    have hMult := congrArg (fun x => 2*C*x) hSub
    nlinarith only [hScaled,hReserve,hMult]

theorem uniform_reserves (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, 4000 ≤ C ∧ ∃ Q : ℕ, 8 ≤ Q ∧ ∃ N : ℕ,
      ∀ n D B K : ℕ, N ≤ n → ((1:ℝ)/2+ε)*(n:ℝ) ≤ (D:ℝ) →
      B ≤ 6*(n/(4096*Q^2))+6 → K ≤ n/(4096*Q^2)+1 →
      2*linearHalfBound C (6*B+1)+K+1 ≤ n ∧
      n+30*B+12 ≤ 2*D ∧ (C+64)*n ≤ 2*C*(D-6*B) := by
  obtain ⟨C,hC⟩ := exists_nat_gt (max (4000:ℝ) (64/ε))
  have hCN : 4000 ≤ C := by exact_mod_cast (le_max_left _ _).trans hC.le
  have hCε : 64 ≤ ε*(C:ℝ) := by
    have hh : 64/ε < C := (le_max_right _ _).trans_lt hC
    have ht := (div_lt_iff₀ hε).mp hh
    nlinarith only [ht]
  let Q := max C ((10:ℕ)^24*C^6)
  have hCQ : C ≤ Q := le_max_left _ _
  have hLQ : (10:ℕ)^24*C^6 ≤ Q := le_max_right _ _
  refine ⟨C,hCN,Q,by omega,256*Q,?_⟩
  intro n D B K hn hdense hB hK
  apply finite_reserves C Q n D B K hCN hCQ hLQ hn hB hK
  have hMul := mul_le_mul_of_nonneg_left hdense (show (0:ℝ) ≤ 2*(C:ℝ) by positivity)
  have hE := mul_le_mul_of_nonneg_right hCε (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n)
  exact_mod_cast (show ((C:ℝ)+128)*n ≤ 2*(C:ℝ)*D by nlinarith only [hMul,hE])

end OverfullWork.SecondLowUniformReserves
