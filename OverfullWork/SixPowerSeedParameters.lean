module

public import OverfullWork.RefinedSeedParameters

@[expose] public section


/-! # Seed parameters using a variance-controlled partition -/
namespace OverfullWork.Gate8J2C
open SimpleGraph
open scoped Classical
set_option maxHeartbeats 4000000

theorem sixth_moment_3000_of_cubic_bound (L m : ℕ) (hL : 0<L) (hm : 60*L^3<m) :
    3000*(m:ℝ)^4<((m:ℝ)/(L:ℝ))^6 := by
  have hLR : (0:ℝ)<(L:ℝ):=by exact_mod_cast hL
  have hlarge : (60:ℝ)*(L:ℝ)^3<(m:ℝ):=by exact_mod_cast hm
  have hmpos : (0:ℝ)<(m:ℝ):=by exact_mod_cast (show 0<m by omega)
  have hp : (0:ℝ)<((m:ℝ)-60*(L:ℝ)^3)*((m:ℝ)+60*(L:ℝ)^3) :=
    mul_pos (by linarith) (by positivity)
  have hs : (3000:ℝ)*(L:ℝ)^6<(m:ℝ)^2:=by nlinarith only [hp]
  have hmul:=mul_lt_mul_of_pos_right hs (show (0:ℝ)<(m:ℝ)^4 by positivity)
  rw [div_pow]
  apply (lt_div_iff₀ (pow_pos hLR 6)).mpr
  nlinarith only [hmul]

theorem palette_moment_of_variance_size (j m D r : ℕ) (hm : 1≤m) (hrm : r≤m)
    (hdepth : j*r≤m) (hD : D≤2*m) (hsize : 3000*(m:ℝ)^4<(r:ℝ)^6) :
    15*(2*m:ℝ)*(D/2+r+j*r+1:ℕ)^3<(2*r:ℝ)^6 := by
  have hq : D/2+r+j*r+1≤4*m:=by omega
  have hqR : ((D/2+r+j*r+1:ℕ):ℝ)≤4*(m:ℝ):=by exact_mod_cast hq
  have hp:=pow_le_pow_left₀ (Nat.cast_nonneg _) hqR 3
  have hmul:=mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤15*(2*(m:ℝ)) by positivity)
  nlinarith only [hmul,hsize,show (0:ℝ)≤(m:ℝ)^4 by positivity]

theorem explicit_variance_seed_parameters (j C c m : ℕ) (hC : 1000≤C) (hc : 0<c)
    (hbig : 100000*C*c*(4*2^j+2)≤m)
    (hcube : 60*(4000*C*c*(4*2^j+2))^3<m) :
    ∃ r : ℕ,1≤r ∧ r≤m ∧ j*r≤m ∧
      1000*C*c*((4*2^j+2)*(r+1))≤m ∧ 3000*(m:ℝ)^4<(r:ℝ)^6 := by
  let A:=4*2^j+2
  let den:=4000*C*c*A
  have hA : 1≤A:=by dsimp [A];omega
  have hden : 1<den:=by
    have hh:=Nat.mul_le_mul_left (4000*C*c) hA
    have hh':=Nat.mul_le_mul_left (4000*C) (show 1≤c by omega)
    have hcoef : 1<4000*C:=by omega
    dsimp [den]
    nlinarith only [hh,hh',hcoef]
  have hdenR : (0:ℝ)<(den:ℝ):=by exact_mod_cast (show 0<den by omega)
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
  have hrel : (m:ℝ)/(den:ℝ)≤(r:ℝ):=(div_le_iff₀ hdenR).mpr (by nlinarith only [hrR])
  have hmoment:=sixth_moment_3000_of_cubic_bound den m (by omega) hcube
  have hp:=pow_le_pow_left₀ (show (0:ℝ)≤(m:ℝ)/(den:ℝ) by positivity) hrel 6
  exact ⟨r,hr,hrm,hdepth,by simpa only [A] using hsmall,hmoment.trans_le hp⟩

end OverfullWork.Gate8J2C
