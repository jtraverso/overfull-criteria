module

public import OverfullWork.RegularCompletionPartition

@[expose] public section


/-! # Discharge the direct bipartite-expansion scales

The constants are deliberately generous. No graph, partition or
expansion statement is an input to this arithmetic lemma.
-/
namespace OverfullWork.BipartiteScaleParameters
set_option maxHeartbeats 12000000

theorem bounds (Q m D B Y : ℕ) (hQ : 1≤Q) (hm : 2^50*Q^4≤m)
    (hD : D≤3*m) (hB : B≤m) (hY : Y≤m/(1024*Q))
    (hDense : m+16*(m/(1024*Q))+4≤D) :
    let q:=m/(1024*Q)
    let r:=m/(2^30*Q^3)
    let δ:=(m+1)/2+q
    let a:=1+(2*D+B)/(q+1)
    (2*(δ:ℝ)+(m:ℝ)/(1024*(Q:ℝ))+3*((q+Y:ℕ):ℝ)≤D) ∧
      δ≤m ∧ m+2*q≤2*δ ∧ 0<r ∧ r≤q ∧ r+a≤q ∧
      4*r*m+2*m*a≤q*q := by
  let q:=m/(1024*Q)
  let r:=m/(2^30*Q^3)
  let δ:=(m+1)/2+q
  let a:=1+(2*D+B)/(q+1)
  have hQpos:0<Q:=by omega
  have hDen:0<1024*Q:=by positivity
  have hRDen:0<2^30*Q^3:=by positivity
  have hPow:Q^3≤Q^4:=Nat.pow_le_pow_right hQpos (by decide)
  have hBig:2^36*Q^3≤m:=by nlinarith only [hm,hPow]
  have hqBig:2^26*Q^2≤q:=by
    apply (Nat.le_div_iff_mul_le hDen).mpr
    calc
      _ = 2^36*Q^3 :=by ring
      _ ≤ _ :=hBig
  have hqPos:1≤q:=by
    have hh:1≤Q^2:=Nat.one_le_pow 2 Q hQ
    nlinarith only [hqBig,hh]
  have hqUpper:1024*Q*q≤m:=Nat.mul_div_le m (1024*Q)
  have hqRem:m<(1024*Q)*(q+1):=Nat.lt_mul_div_succ m hDen
  have hReverse:m≤2048*Q*q:=by
    have hInc:q+1≤2*q:=by omega
    have hh:=Nat.mul_le_mul_left (1024*Q) hInc
    nlinarith only [hqRem,hh]
  have hrUpper:2^30*Q^3*r≤m:=Nat.mul_div_le m (2^30*Q^3)
  have hrPos:0<r:=by
    apply Nat.div_pos
    · nlinarith only [hBig]
    · exact hRDen
  have haBound:a≤8192*Q:=by
    have hT:2*D+B≤7*m:=by omega
    have hTbound:2*D+B<(7168*Q)*(q+1):=by nlinarith only [hT,hqRem]
    have hDiv:(2*D+B)/(q+1)<7168*Q:=
      (Nat.div_lt_iff_lt_mul (by omega : 0<q+1)).mpr hTbound
    dsimp only [a]
    omega
  have hrSmall:2*r≤q:=by
    have hCompare:(2048*Q)*(2^19*Q^2*r)≤(2048*Q)*q:=by
      nlinarith only [hrUpper,hReverse]
    have hc:2^19*Q^2*r≤q:=Nat.le_of_mul_le_mul_left hCompare (by positivity)
    have hCoef:2≤2^19*Q^2:=by
      have hh:1≤Q^2:=Nat.one_le_pow 2 Q hQ
      nlinarith only [hh]
    exact (Nat.mul_le_mul_right r hCoef).trans hc
  have haSmall:2*a≤q:=by
    have hCoef:2≤8192*Q:=by omega
    have hMul:=Nat.mul_le_mul_left (8192*Q) haBound
    have hq: (8192*Q)*(8192*Q)≤q:=by
      convert hqBig using 1 <;>ring
    nlinarith only [hCoef,hMul,hq]
  have hRscale:8*r*m≤q*q:=by
    have h₁:=Nat.mul_le_mul_right m hrUpper
    have h₂:=Nat.mul_le_mul hReverse hReverse
    have h₃:(2^22*Q^2)*(256*Q*r*m)≤(2^22*Q^2)*(q*q):=by
      nlinarith only [h₁,h₂]
    have hc:256*Q*r*m≤q*q:=Nat.le_of_mul_le_mul_left h₃ (by positivity)
    have hCoef:8≤256*Q:=by omega
    have hh:=Nat.mul_le_mul_right (r*m) hCoef
    nlinarith only [hc,hh]
  have hAscale:4*m*a≤q*q:=by
    have hq:(8192*Q)*(8192*Q)≤q:=by convert hqBig using 1 <;>ring
    have hqa:(8192*Q)*a≤q:=(Nat.mul_le_mul_left (8192*Q) haBound).trans hq
    have h₁:=Nat.mul_le_mul_right (4*a) hReverse
    have h₂:=Nat.mul_le_mul_right q hqa
    nlinarith only [h₁,h₂]
  have hScale:4*r*m+2*m*a≤q*q:=by nlinarith only [hRscale,hAscale]
  have hδ:δ≤m:=by
    have hFour:4*q≤m:=by
      have hc:4≤1024*Q:=by omega
      exact (Nat.mul_le_mul_right q hc).trans hqUpper
    dsimp only [δ]
    omega
  have hMargin:m+2*q≤2*δ:=by dsimp only [δ];omega
  have hRoom:2*(δ:ℝ)+(m:ℝ)/(1024*(Q:ℝ))+3*((q+Y:ℕ):ℝ)≤D:=by
    have hb:(m:ℝ)/(1024*(Q:ℝ))<(q:ℝ)+1:=by
      apply (div_lt_iff₀ (show 0<1024*(Q:ℝ) by positivity)).mpr
      have hh:m<(q+1)*(1024*Q):=by nlinarith only [hqRem]
      exact_mod_cast hh
    have hδupper:2*δ≤m+1+2*q:=by dsimp only [δ];omega
    have hd:(m:ℝ)+16*(q:ℝ)+4≤D:=by exact_mod_cast hDense
    have hy:(Y:ℝ)≤q:=by exact_mod_cast hY
    have hδupper':2*(δ:ℝ)≤(m:ℝ)+1+2*(q:ℝ):=by exact_mod_cast hδupper
    push_cast
    linarith
  have hrq:r≤q:=by omega
  have hrt:r+a≤q:=by omega
  exact ⟨hRoom,hδ,hMargin,hrPos,hrq,hrt,hScale⟩

end OverfullWork.BipartiteScaleParameters
