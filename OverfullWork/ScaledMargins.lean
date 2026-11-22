module

public import OverfullWork.Gate8I

@[expose] public section


/-! # Arithmetic margins for a variable remainder cutoff -/
namespace OverfullWork.ScaledMargins

def badBound (c m t : ℕ) : ℕ:=4*t+2*(4*m/c+1)
def degreeBound (c m : ℕ) : ℕ:=m/2+16*(m/c)

structure Budget (c m D t k : ℕ) : Prop where
  first : 7*badBound c m t+7+k+c*t<D
  ordinary : degreeBound c m+k+c*t+7≤D
  overlap : m+2*badBound c m t<2*degreeBound c m
  residual_hall : m+2*(3*c*t)+4*(m/(3*c)+1)+16+2*k≤2*D
  residual_centre : 3*c*t+16*(m/(3*c)+1)+k<D

set_option maxHeartbeats 2000000

theorem budget_of_density (c m D t k : ℕ) (hc : 1000≤c) (ht : 0<t)
    (hsmall : 1000*c*c*t≤m) (hdense : (c+64)*m≤c*D) (hk : k≤D/2+t) :
    Budget c m D t k := by
  have hcpos : 0<c:=by omega
  have hctsmall : 1000*c*t≤m := by
    have hh:=Nat.mul_le_mul_right (1000*c*t) (show 1≤c by omega)
    nlinarith only [hh,hsmall]
  have hcsmall : 1000*c≤m := by
    have hh:=Nat.mul_le_mul_left (1000*c) (show 1≤t by omega)
    nlinarith only [hh,hctsmall]
  have hcm : 1000*m≤c*m:=Nat.mul_le_mul_right m hc
  have hk2 : 2*k≤D+2*t:=by omega
  have hck:=Nat.mul_le_mul_left c hk2
  have hhalf : m≤2*(m/2)+1:=by omega
  have hchalf:=Nat.mul_le_mul_left c hhalf
  have hhalf' : 2*(m/2)≤m:=by omega
  have hchalf':=Nat.mul_le_mul_left c hhalf'
  have hdiv:=Nat.mul_div_le m c
  have hdivR:=Nat.lt_mul_div_succ m hcpos
  have hdiv4:=Nat.mul_div_le (4*m) c
  have hdiv3:=Nat.mul_div_le m (3*c)
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold badBound
    apply (Nat.mul_lt_mul_left hcpos).mp
    nlinarith only [hdense,hck,hdiv4,hsmall,hctsmall,hcsmall,hcm,hc]
  · unfold degreeBound
    apply Nat.le_of_mul_le_mul_left (c:=2*c) ?_ (by omega)
    nlinarith only [hdense,hck,hdiv,hchalf',hsmall,hctsmall,hcsmall]
  · unfold badBound degreeBound
    apply (Nat.mul_lt_mul_left hcpos).mp
    nlinarith only [hdivR,hdiv4,hchalf,hctsmall,hcsmall]
  · apply Nat.le_of_mul_le_mul_left (c:=c) ?_ hcpos
    nlinarith only [hdense,hck,hdiv3,hsmall,hctsmall,hcsmall]
  · apply (Nat.mul_lt_mul_left hcpos).mp
    nlinarith only [hdense,hck,hdiv3,hsmall,hctsmall,hcsmall,hcm,hc]

end OverfullWork.ScaledMargins
