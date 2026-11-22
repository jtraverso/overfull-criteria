module

public import OverfullWork.CanonicalCaseTwoCut

@[expose] public section


/-! # Pay support-cut and partition-repair reserves from source budgets -/
namespace OverfullWork.CaseTwoCutScales
set_option maxHeartbeats 10000000

theorem source_budget_le_q (P n m B Y : ℕ) (hP : 8 ≤ P)
    (hm : 2^50*P^4 ≤ m) (hCard : n+1 = 2*m+Y)
    (hY : Y ≤ n/(4096*P^2)+1) (hB : B ≤ 6*(n/(4096*P^2))+6) :
    B ≤ m/(1024*P) := by
  let k := n/(4096*P^2)
  let q := m/(1024*P)
  have hk : 4096*P^2*k ≤ n := Nat.mul_div_le n (4096*P^2)
  have hCoef : 24576*P+1 ≤ 4096*P^2 := by nlinarith only [hP]
  have hMul := Nat.mul_le_mul_right k hCoef
  change Y ≤ k+1 at hY
  change B ≤ 6*k+6 at hB
  have hkM : 12288*P*k ≤ m := by nlinarith only [hk,hMul,hY,hCard]
  have hkq : 12*k ≤ q := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 1024*P)).mpr
    nlinarith only [hkM]
  have hPow : P ≤ P^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < P by omega) (by decide : 1 ≤ 4)
  have hq : 12 ≤ q := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 1024*P)).mpr
    nlinarith only [hm,hPow]
  change B ≤ q
  by_cases hk0 : k = 0 <;> omega

theorem repair_reserves (P T m : ℕ) (hP : 2 ≤ P)
    (hm : (8*(3*T+1)+1)*(2^30*P^3) ≤ m) :
    2*(3*T+1) < m/(2^30*P^3) ∧ 3*T+1 ≤ m ∧
      2*(m/(1024*P)+(3*T+1)) ≤ m := by
  have hDen : 0 < 2^30*P^3 := by positivity
  have hr : 8*(3*T+1)+1 ≤ m/(2^30*P^3) :=
    (Nat.le_div_iff_mul_le hDen).mpr hm
  have hWeak : 8*(3*T+1)+1 ≤ m := hr.trans (Nat.div_le_self _ _)
  have hq : 4*(m/(1024*P)) ≤ m :=
    (Nat.mul_le_mul_right (m/(1024*P)) (show 4 ≤ 1024*P by omega)).trans
      (Nat.mul_div_le m (1024*P))
  omega

end OverfullWork.CaseTwoCutScales
