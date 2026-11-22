module

public import OverfullWork.CompensatedReduction

@[expose] public section


/-! # Numerical room for a weighted exceptional-centre completion

The density cutoff c stays independent of the maximum incident weight S.
The weighted Hall bound uses an actual occupied-weight estimate D/3+2S.
-/
namespace OverfullWork.Gate8J2C
set_option maxHeartbeats 4000000

theorem weighted_numerics_of_scaled (c m D t k b S : ℕ)
    (hc : 1000≤c) (ht : 0<t) (hb : b≤t) (hS : S≤t)
    (hnum : ScaledMargins.Budget c m D (2*t) k)
    (hsmall : 1000*c*c*(2*t)≤m) (hmD : m≤D) (hk : k≤D/2+t) :
    SimpleGraph.MultiGraph.PartialColouring.AdditiveFirstBudget b c m D t k
        (ScaledMargins.degreeBound c m) ∧
      k+4*t+2*S<D ∧
      m+2*(3*c*t)+4*(m/(3*c)+1)+2*b+2+2*k≤2*D ∧
      k+3*c*t+D/3+2*S<D := by
  have hcpos : 0<c:=by omega
  have hct : t≤c*t:=by simpa using Nat.mul_le_mul_right t (show 1≤c by omega)
  have he : c*(2*t)=2*(c*t):=by ring
  have hf:=hnum.first
  have ho:=hnum.ordinary
  have hv:=hnum.overlap
  have hr:=hnum.residual_hall
  have hp:=hnum.residual_centre
  simp only [ScaledMargins.badBound,Nat.mul_assoc,he] at hf ho hv hr hp
  have hsmallD : 2000*(c*t)≤D := by
    have hh:=Nat.mul_le_mul_right (2000*c*t) (show 1≤c by omega)
    nlinarith only [hh,hsmall,hmD]
  have hctpos : 0<c*t:=Nat.mul_pos hcpos ht
  have hslack : 36*(c*t)<D:=by omega
  have hk2 : 2*k≤D+2*t:=by omega
  have hthird : 3*(D/3)≤D:=Nat.mul_div_le D 3
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · unfold ScaledMargins.badBound
    omega
  · omega
  · unfold ScaledMargins.badBound
    omega
  · omega
  · simp only [Nat.mul_assoc]
    omega
  · nlinarith only [hk2,hthird,hslack,hS,hct]

end OverfullWork.Gate8J2C
