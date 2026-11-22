module

public import OverfullWork.QuantitativeSeedParameters
public import OverfullWork.SeparatedCompletionMargins

@[expose] public section


/-! # Short-seed moments without an extra binary-depth factor -/
namespace OverfullWork.Gate8J2B
open SimpleGraph
open scoped Classical
set_option maxHeartbeats 4000000

theorem moments_of_short_seed (j m D r : ℕ) (hm : 1≤m) (hrm : r≤m)
    (hdepth : j*r≤m) (hD : D≤2*m)
    (hsize : 30*(m:ℝ)^4*((2^j:ℕ):ℝ)^6<(r:ℝ)^6) :
    30*(m:ℝ)^4<(2*(r:ℝ)/(2^j:ℕ))^6 ∧
      15*(2*m:ℝ)*(D/2+r+j*r+1:ℕ)^3<(2*r:ℝ)^6 := by
  have hμ : (1:ℝ)≤((2^j:ℕ):ℝ):=by exact_mod_cast (Nat.one_le_pow j 2 (by omega))
  have hpowμ : (1:ℝ)≤((2^j:ℕ):ℝ)^6:=by
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hμ 6
  have hbase : 30*(m:ℝ)^4<(r:ℝ)^6 := by
    have hh:=mul_le_mul_of_nonneg_left hpowμ (show (0:ℝ)≤30*(m:ℝ)^4 by positivity)
    nlinarith only [hh,hsize]
  have hdouble : (r:ℝ)^6≤(2*(r:ℝ))^6:=pow_le_pow_left₀ (by positivity)
    (by nlinarith [Nat.cast_nonneg r (α:=ℝ)]) 6
  constructor
  · rw [div_pow]
    apply (lt_div_iff₀ (show (0:ℝ)<((2^j:ℕ):ℝ)^6 by positivity)).mpr
    exact hsize.trans_le hdouble
  · have hq : D/2+r+j*r+1≤4*m:=by omega
    have hqR : ((D/2+r+j*r+1:ℕ):ℝ)≤4*(m:ℝ):=by exact_mod_cast hq
    have hp:=pow_le_pow_left₀ (Nat.cast_nonneg _) hqR 3
    have hmul:=mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤15*(2*(m:ℝ)) by positivity)
    nlinarith only [hmul,hbase]

/-- The small-error bound now uses the product of the density parameter
and the cutoff, rather than the square of the cutoff. -/
theorem explicit_refined_seed_parameters (j C c m : ℕ) (hC : 1000≤C) (hc : 0<c)
    (hbig : 100000*C*c*(4*2^j+2)≤m)
    (hcube : 6*(4000*C*c*(4*2^j+2)*2^j)^3<m) :
    ∃ r : ℕ,1≤r ∧ r≤m ∧ j*r≤m ∧
      1000*C*c*((4*2^j+2)*(r+1))≤m ∧
      30*(m:ℝ)^4*((2^j:ℕ):ℝ)^6<(r:ℝ)^6 := by
  let A:=4*2^j+2
  let den:=4000*C*c*A
  let R : ℝ:=((2^j:ℕ):ℝ)
  let L:=den*2^j
  have hA : 1≤A:=by dsimp [A];omega
  have hden : 1<den:=by
    have hh:=Nat.mul_le_mul_left (4000*C*c) hA
    have hh':=Nat.mul_le_mul_left (4000*C) (show 1≤c by omega)
    have hcoef : 1<4000*C:=by omega
    dsimp [den]
    nlinarith only [hh,hh',hcoef]
  have hdenR : (0:ℝ)<(den:ℝ):=by exact_mod_cast (show 0<den by omega)
  have hR : 0<R:=by dsimp [R];positivity
  have hL : 0<L:=by dsimp [L];positivity
  have hmpos : 0<m:=by omega
  let r:=m/den+1
  have hr : 1≤r:=Nat.succ_le_succ (Nat.zero_le (m/den))
  have hrm : r≤m:=Nat.succ_le_of_lt (Nat.div_lt_self hmpos hden)
  have hq:=Nat.mul_div_le m den
  have hrbound : den*r≤m+den:=by dsimp [r];nlinarith only [hq]
  have hsmall : 1000*C*c*(A*(r+1))≤m:=by
    dsimp [den] at hrbound
    change 100000*C*c*A≤m at hbig
    nlinarith only [hrbound,hbig]
  have hja : j≤A := by
    have hh : j≤2^j:=Nat.lt_two_pow_self.le
    dsimp [A]
    omega
  have hcoef : 1≤1000*C*c:=by
    have hh : 0<1000*C*c:=by positivity
    omega
  have hdepth : j*r≤m := by
    calc
      j*r ≤ A*(r+1):=Nat.mul_le_mul hja (Nat.le_succ r)
      _ ≤ (1000*C*c)*(A*(r+1)):=by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (A*(r+1)) hcoef
      _ ≤ m:=hsmall
  have hrlarge : m<den*r:=Nat.lt_mul_div_succ m (by omega)
  have hrR : (m:ℝ)<(den:ℝ)*(r:ℝ):=by exact_mod_cast hrlarge
  have hrel : (m:ℝ)/(L:ℝ)≤(r:ℝ)/R := by
    have he : (L:ℝ)=(den:ℝ)*R:=by dsimp [L,R];push_cast;ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity) hR).mpr
    nlinarith only [hrR,hR]
  have hmoment:=Gate8J2.sixth_moment_of_cubic_bound L m hL hcube
  have hp:=pow_le_pow_left₀ (show (0:ℝ)≤(m:ℝ)/(L:ℝ) by positivity) hrel 6
  have hh:=hmoment.trans_le hp
  rw [div_pow] at hh
  have hscaled:=(lt_div_iff₀ (pow_pos hR 6)).mp hh
  exact ⟨r,hr,hrm,hdepth,by simpa only [A] using hsmall,by simpa only [R] using hscaled⟩

end OverfullWork.Gate8J2B
