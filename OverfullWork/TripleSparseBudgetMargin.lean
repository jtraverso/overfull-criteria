module

public import OverfullWork.CriticalLargeCentreRemainder

@[expose] public section


namespace OverfullWork.SparseBudgetMargin
set_option maxHeartbeats 24000000

theorem triple_budget_of_coarse_margin (n D Qm Q B : ℕ)
    (hQm : 2 ≤ Qm) (hQ : 2*Qm ≤ Q) (hn : 4096*Qm^2 ≤ n)
    (hB : B ≤ 6*(n/(4096*Q^2))+6)
    (hMargin : n+2*(6*(n/(4096*Qm^2))+6)+(n/(4096*Qm^2)+1)+3 ≤ 2*D) :
    n+3*B ≤ 2*D := by
  let fine := n/(4096*Q^2)
  let coarse := n/(4096*Qm^2)
  have hCoeff : 4*(4096*Qm^2) ≤ 4096*Q^2 := by nlinarith
  have hFine : 4*fine ≤ coarse := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 4096*Qm^2)).mpr
    have hPay := (Nat.mul_le_mul_right fine hCoeff).trans (Nat.mul_div_le n (4096*Q^2))
    change 4*fine*(4096*Qm^2) ≤ n
    nlinarith only [hPay]
  have hCoarse : 1 ≤ coarse := (Nat.le_div_iff_mul_le (by positivity : 0 < 4096*Qm^2)).mpr (by simpa using hn)
  change B ≤ 6*fine+6 at hB
  change n+2*(6*coarse+6)+(coarse+1)+3 ≤ 2*D at hMargin
  omega

end OverfullWork.SparseBudgetMargin
