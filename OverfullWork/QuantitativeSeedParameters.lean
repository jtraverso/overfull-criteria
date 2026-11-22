module

public import OverfullWork.UniformFactorization

@[expose] public section


/-! # Explicit cubic size threshold for the sixth-moment seed -/
namespace OverfullWork.Gate8J2
open SimpleGraph
open scoped Classical
set_option maxHeartbeats 4000000

theorem sixth_moment_of_cubic_bound (L m : ℕ) (hL : 0<L) (hm : 6*L^3<m) :
    30*(m:ℝ)^4<((m:ℝ)/(L:ℝ))^6 := by
  have hLR : (0:ℝ)<(L:ℝ):=by exact_mod_cast hL
  have hlarge : (6:ℝ)*(L:ℝ)^3<(m:ℝ):=by exact_mod_cast hm
  have hmpos : (0:ℝ)<(m:ℝ):=by exact_mod_cast (show 0<m by omega)
  have hp : (0:ℝ)<((m:ℝ)-6*(L:ℝ)^3)*((m:ℝ)+6*(L:ℝ)^3) :=
    mul_pos (by linarith) (by positivity)
  have hs : (30:ℝ)*(L:ℝ)^6<(m:ℝ)^2:=by nlinarith only [hp]
  have hmul:=mul_lt_mul_of_pos_right hs (show (0:ℝ)<(m:ℝ)^4 by positivity)
  rw [div_pow]
  apply (lt_div_iff₀ (pow_pos hLR 6)).mpr
  nlinarith only [hmul]

/-- The two scalar bounds replace the former existential threshold. -/
theorem explicit_seed_parameters (j c m : ℕ) (hc : 1000≤c)
    (hbig : 100000*c*c*(4*2^j+2)≤m)
    (hcube : 6*(4000*c*c*(4*2^j+2)*(2^j*(j+3)))^3<m) :
    ∃ r : ℕ,1≤r ∧ r≤m ∧
      1000*c*c*((4*2^j+2)*(r+1))≤m ∧
      30*(m:ℝ)^4*(((2^j:ℕ):ℝ)*(j+3:ℕ))^6<(r:ℝ)^6 := by
  let A:=4*2^j+2
  let den:=4000*c*c*A
  let R : ℝ:=((2^j:ℕ):ℝ)*(j+3:ℕ)
  let L:=den*(2^j*(j+3))
  have hA : 1≤A:=by dsimp [A];omega
  have hden : 1<den:=by
    have hh:=Nat.mul_le_mul_left (4000*c*c) hA
    have hcoef : 1<4000*c*c:=by nlinarith only [hc]
    dsimp [den]
    nlinarith only [hh,hcoef]
  have hdenR : (0:ℝ)<(den:ℝ):=by exact_mod_cast (show 0<den by omega)
  have hR : 0<R:=by dsimp [R];positivity
  have hL : 0<L:=by dsimp [L];positivity
  have hmpos : 0<m:=by omega
  let r:=m/den+1
  have hr : 1≤r:=Nat.succ_le_succ (Nat.zero_le (m/den))
  have hrm : r≤m:=Nat.succ_le_of_lt (Nat.div_lt_self hmpos hden)
  have hq:=Nat.mul_div_le m den
  have hrbound : den*r≤m+den:=by dsimp [r];nlinarith only [hq]
  have hsmall : 1000*c*c*(A*(r+1))≤m:=by
    dsimp [den] at hrbound
    change 100000*c*c*A≤m at hbig
    nlinarith only [hrbound,hbig]
  have hrlarge : m<den*r:=Nat.lt_mul_div_succ m (by omega)
  have hrR : (m:ℝ)<(den:ℝ)*(r:ℝ):=by exact_mod_cast hrlarge
  have hrel : (m:ℝ)/(L:ℝ)≤(r:ℝ)/R := by
    have he : (L:ℝ)=(den:ℝ)*R:=by dsimp [L,R];push_cast;ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity) hR).mpr
    nlinarith only [hrR,hR]
  have hmoment:=sixth_moment_of_cubic_bound L m hL hcube
  have hp:=pow_le_pow_left₀ (show (0:ℝ)≤(m:ℝ)/(L:ℝ) by positivity) hrel 6
  have hh:=hmoment.trans_le hp
  rw [div_pow] at hh
  have hscaled:=(lt_div_iff₀ (pow_pos hR 6)).mp hh
  exact ⟨r,hr,hrm,by simpa only [A] using hsmall,by simpa only [R] using hscaled⟩

end OverfullWork.Gate8J2
