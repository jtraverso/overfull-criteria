module

public import OverfullWork.GeneralCompletionBudget

@[expose] public section


/-! # Uniform discharge of the five margins for arbitrary fixed budgets -/
namespace OverfullWork.BoundedMargins
set_option maxHeartbeats 4000000

theorem budget_of_density (μ b c m D t k : ℕ)
    (hc : 1000*(μ+b+1)≤c) (ht : 0<t)
    (hsmall : 1000*c*c*t≤m) (hdense : (c+64)*m≤c*D) (hk : k≤D/2+t) :
    Budget μ b c m D t k (ScaledMargins.degreeBound c m) := by
  have hc1000 : 1000≤c:=by omega
  have hcpos : 0<c:=by omega
  have hbc : 1000*b≤c:=by omega
  have hμc : 1000*μ≤c:=by omega
  have hble : b≤c:=by omega
  have hμle : μ≤c:=by omega
  have hctsmall : 1000*c*t≤m := by
    have hh:=Nat.mul_le_mul_right (1000*c*t) (show 1≤c by omega)
    nlinarith only [hh,hsmall]
  have hcsmall : 1000*c≤m := by
    have hh:=Nat.mul_le_mul_left (1000*c) (show 1≤t by omega)
    nlinarith only [hh,hctsmall]
  have hccsmall : 1000*c*c≤m := by
    have hh:=Nat.mul_le_mul_left (1000*c*c) (show 1≤t by omega)
    nlinarith only [hh,hsmall]
  have hcm : 1000*m≤c*m:=Nat.mul_le_mul_right m hc1000
  have hbm:=Nat.mul_le_mul_right m hbc
  have hμm:=Nat.mul_le_mul_right m hμc
  have hbct:=Nat.mul_le_mul_right (c*t) hble
  have hbc':=Nat.mul_le_mul_right c hble
  have hμc':=Nat.mul_le_mul_right c hμle
  have hk2 : 2*k≤D+2*t:=by omega
  have hck:=Nat.mul_le_mul_left c hk2
  have hhalf : m≤2*(m/2)+1:=by omega
  have hchalf:=Nat.mul_le_mul_left c hhalf
  have hhalf' : 2*(m/2)≤m:=by omega
  have hchalf':=Nat.mul_le_mul_left c hhalf'
  have hdiv:=Nat.mul_div_le m c
  have hdivR:=Nat.lt_mul_div_succ m hcpos
  have hdiv4:=Nat.mul_div_le (4*m) c
  have hbdiv4:=Nat.mul_le_mul_left b hdiv4
  have hdiv3:=Nat.mul_div_le m (3*c)
  have hμdiv3:=Nat.mul_le_mul_left μ hdiv3
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold ScaledMargins.badBound
    apply (Nat.mul_lt_mul_left hcpos).mp
    nlinarith only [hdense,hck,hbdiv4,hsmall,hctsmall,hccsmall,hcm,hbm,hbct,hbc',hc1000]
  · unfold ScaledMargins.degreeBound
    apply Nat.le_of_mul_le_mul_left (c:=2*c) ?_ (by omega)
    nlinarith only [hdense,hck,hdiv,hchalf',hsmall,hctsmall,hccsmall,hbc']
  · unfold ScaledMargins.badBound ScaledMargins.degreeBound
    apply (Nat.mul_lt_mul_left hcpos).mp
    nlinarith only [hdivR,hdiv4,hchalf,hctsmall,hcsmall]
  · apply Nat.le_of_mul_le_mul_left (c:=c) ?_ hcpos
    nlinarith only [hdense,hck,hdiv3,hsmall,hctsmall,hccsmall,hbc',hcsmall]
  · apply (Nat.mul_lt_mul_left hcpos).mp
    nlinarith only [hdense,hck,hμdiv3,hsmall,hctsmall,hccsmall,hcm,hμm,hμc',hc1000]

end OverfullWork.BoundedMargins
