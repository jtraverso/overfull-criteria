module

public import OverfullWork.CanonicalCompletionOddCuts

@[expose] public section


/-! # Pay all cut-size inequalities from the existing sparse budgets -/
namespace OverfullWork.CanonicalOddCutScales
set_option maxHeartbeats 6000000

theorem source_bounds (Q n m Δ B Y : ℕ) (hQ : 2≤Q) (hm : 2^66*Q^6≤m)
    (hn : n≤3*m) (hΔ : m≤Δ) (hΔm : Δ≤3*m)
    (hB : B≤6*(n/(4096*Q^2))+6) (hY : Y≤n/(4096*Q^2)+1) :
    Δ≤(m/(2^30*Q^3))*(m/(2^30*Q^3)) ∧
      B+3*(2*(m/(1024*Q))+Y)≤Δ := by
  let L:=2^30*Q^3
  let r:=m/L
  have hL:0<L:=by dsimp [L];positivity
  have hmL:64*L^2≤m:=by convert hm using 1 <;>dsimp [L] <;>ring
  have hR:32*L≤r:=by
    apply (Nat.le_div_iff_mul_le hL).mpr
    nlinarith only [hmL]
  have hRem:m<L*(r+1):=Nat.lt_mul_div_succ m hL
  have hPos:1≤r:=by omega
  have hRev:m≤2*L*r:=by
    have hh:=Nat.mul_le_mul_left L (show r+1≤2*r by omega)
    nlinarith only [hRem,hh]
  have hSix:6*L≤r:=by omega
  have hSquare:=Nat.mul_le_mul_right r hSix
  have hLarge:Δ≤r*r:=by nlinarith only [hSquare,hRev,hΔm]
  let k:=n/(4096*Q^2)
  let t:=m/(1024*Q)
  have hPow:1≤Q^2:=Nat.one_le_pow 2 Q (by omega)
  have hCoef:4096≤4096*Q^2:=by nlinarith only [hPow]
  have hk:4096*k≤3*m:=
    ((Nat.mul_le_mul_right k hCoef).trans (Nat.mul_div_le n (4096*Q^2))).trans hn
  have hTCoef:1024≤1024*Q:=by omega
  have ht:1024*t≤m:=
    (Nat.mul_le_mul_right t hTCoef).trans (Nat.mul_div_le m (1024*Q))
  have hmSmall:16≤m:=by
    have hh:1≤Q^6:=Nat.one_le_pow 6 Q (by omega)
    nlinarith only [hh,hm]
  change B≤6*k+6 at hB
  change Y≤k+1 at hY
  have hSmall:B+3*(2*t+Y)≤Δ:=by omega
  exact ⟨hLarge,hSmall⟩

end OverfullWork.CanonicalOddCutScales
