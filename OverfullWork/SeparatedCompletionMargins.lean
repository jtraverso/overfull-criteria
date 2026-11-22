module

public import OverfullWork.GeneralCompletionBudget

@[expose] public section


/-! # Density margin separated from the multiplicity cutoff -/
namespace OverfullWork.BoundedMargins
set_option maxHeartbeats 4000000

theorem budget_of_separated_density (C S μ b m D t k : ℕ)
    (hC : 4000≤C) (hS : 1≤S) (hμ : μ≤2*S) (hb : b≤S) (ht : 0<t)
    (hsmall : 1000*C*(C*S)*t≤m) (hdense : (C+64)*m≤C*D) (hk : k≤D/2+t) :
    Budget μ b (C*S) m D t k (ScaledMargins.degreeBound C m) := by
  let c:=C*S
  have hCpos : 0<C:=by omega
  have hCS:=Nat.mul_le_mul_right S hC
  have hc4000 : 4000≤c:=by dsimp [c];nlinarith only [hCS,hS]
  have hcpos : 0<c:=by omega
  have hSc : S≤c:=by dsimp [c];nlinarith only [hCS]
  have hCc : C≤c:=by simpa [c] using Nat.mul_le_mul_left C hS
  have hbc : 1000*b≤c:=by dsimp [c];nlinarith only [hCS,hb]
  have hμc : 1000*μ≤c:=by dsimp [c];nlinarith only [hCS,hμ]
  have hble : b≤c:=by omega
  have hμle : μ≤c:=by omega
  have hctsmall : 1000*c*t≤m := by
    have hh:=Nat.mul_le_mul_right (1000*c*t) (show 1≤C by omega)
    change 1000*C*c*t≤m at hsmall
    nlinarith only [hh,hsmall]
  have hcsmall : 1000*c≤m := by
    have hh:=Nat.mul_le_mul_left (1000*c) (show 1≤t by omega)
    nlinarith only [hh,hctsmall]
  have hsmallS : 1000*c*c*t≤S*m := by
    have hh:=Nat.mul_le_mul_left S hsmall
    dsimp [c] at *
    nlinarith only [hh]
  have hccS : 1000*c*c≤S*m := by
    have hh:=Nat.mul_le_mul_left (1000*c*c) (show 1≤t by omega)
    nlinarith only [hh,hsmallS]
  have hcmS : 4000*(S*m)≤c*m := by
    have hh:=Nat.mul_le_mul_right (S*m) hC
    dsimp [c]
    nlinarith only [hh]
  have hbm:=Nat.mul_le_mul_right m hbc
  have hμm:=Nat.mul_le_mul_right m hμc
  have hbct:=Nat.mul_le_mul_right (c*t) hble
  have hbc':=Nat.mul_le_mul_right c hble
  have hμc':=Nat.mul_le_mul_right c hμle
  have hk2 : 2*k≤D+2*t:=by omega
  have hck:=Nat.mul_le_mul_left c hk2
  have hCk:=Nat.mul_le_mul_left C hk2
  have hSm : m≤S*m:=by simpa using Nat.mul_le_mul_right m hS
  have hcdense : (c+64)*m≤c*D := by
    have hh:=Nat.mul_le_mul_right S hdense
    dsimp [c]
    nlinarith only [hh,hSm]
  have hhalf : m≤2*(m/2)+1:=by omega
  have hchalf:=Nat.mul_le_mul_left c hhalf
  have hhalf' : 2*(m/2)≤m:=by omega
  have hChalf':=Nat.mul_le_mul_left C hhalf'
  have hdiv:=Nat.mul_div_le m C
  have hdivR:=Nat.lt_mul_div_succ m hCpos
  have hdivRS:=Nat.mul_lt_mul_of_pos_left hdivR (show 0<S by omega)
  have hdiv4:=Nat.mul_div_le (4*m) c
  have hbdiv4:=Nat.mul_le_mul_left b hdiv4
  have hdiv3:=Nat.mul_div_le m (3*c)
  have hμdiv3:=Nat.mul_le_mul_left μ hdiv3
  have hCt : C*t≤C*c*t := by
    have hh:=Nat.mul_le_mul_left (C*t) (show 1≤c by omega)
    nlinarith only [hh]
  have hCSsmall : 1000*C*c≤m := by
    have hh:=Nat.mul_le_mul_left (1000*C*c) (show 1≤t by omega)
    change 1000*C*c*t≤m at hsmall
    nlinarith only [hh,hsmall]
  have hCb : C*b≤c:=by simpa only [c] using Nat.mul_le_mul_left C hb
  have hdiv3C : 3*C*(m/(3*c))≤m := by
    have hh:=Nat.mul_le_mul_right (3*C*(m/(3*c))) hS
    have he : S*(3*C*(m/(3*c)))=3*c*(m/(3*c)):=by dsimp [c];ring
    rw [he] at hh
    simpa using hh.trans hdiv3
  change Budget μ b c m D t k (ScaledMargins.degreeBound C m)
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold ScaledMargins.badBound
    apply (Nat.mul_lt_mul_left hcpos).mp
    nlinarith only [hcdense,hck,hbdiv4,hsmallS,hccS,hcmS,hbm,hbct,hbc',hc4000]
  · unfold ScaledMargins.degreeBound
    apply Nat.le_of_mul_le_mul_left (c:=2*C) ?_ (by omega)
    change 1000*C*c*t≤m at hsmall
    nlinarith only [hdense,hCk,hdiv,hChalf',hsmall,hCSsmall,hCt,hCb,hSc,hcsmall,hCc]
  · unfold ScaledMargins.badBound ScaledMargins.degreeBound
    apply (Nat.mul_lt_mul_left hcpos).mp
    have hfloor : S*m<c*(m/C+1) := by
      dsimp [c]
      nlinarith only [hdivRS]
    nlinarith only [hfloor,hdiv4,hchalf,hctsmall,hcsmall,hSm]
  · apply Nat.le_of_mul_le_mul_left (c:=C) ?_ hCpos
    change 1000*C*c*t≤m at hsmall
    nlinarith only [hdense,hCk,hdiv3C,hsmall,hCSsmall,hCt,hCb,hSc,hcsmall,hCc]
  · apply (Nat.mul_lt_mul_left hcpos).mp
    nlinarith only [hcdense,hck,hμdiv3,hsmallS,hccS,hcmS,hμm,hμc',hc4000]

end OverfullWork.BoundedMargins
