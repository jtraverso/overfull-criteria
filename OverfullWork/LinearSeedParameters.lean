module

public import OverfullWork.SixPowerSeedParameters

@[expose] public section


/-! # Linear-scale numerical parameters for an additive-multiplicity seed

This module is purely numerical. It does not assert existence of a new
multicolouring or seed. A caller must construct the required seed.
-/
namespace OverfullWork.Gate8J2I
open SimpleGraph
open scoped Classical
set_option maxHeartbeats 4000000

def linearHalfBound (C S : ℕ) : ℕ:=(10:ℕ)^24*C^6*S

theorem linear_size_conditions (C S m : ℕ) (hC : 4000≤C) (hS : 1≤S)
    (hsize : linearHalfBound C S≤m) :
    1000*(256000*C*C)≤m ∧ 60*(256000*C*C)^3<m ∧
      (256000*C*C)*(4*S)≤m := by
  let P:=C^6*S
  have hP : 0<P:=by dsimp [P];positivity
  have hK : (10:ℕ)^24*P≤m:=by simpa [linearHalfBound,P,Nat.mul_assoc] using hsize
  have hCp : C^2≤C^6:=pow_le_pow_right₀ (by omega : 1≤C) (by omega)
  have hCSP : C^6≤P := by
    have hh:=Nat.mul_le_mul_left (C^6) hS
    simpa only [Nat.mul_one] using hh
  have hfirst : 1000*(256000*C*C)≤256000000*P := by
    calc
      _ = 256000000*C^2:=by ring
      _ ≤ 256000000*C^6:=Nat.mul_le_mul_left _ hCp
      _ ≤ _:=Nat.mul_le_mul_left _ hCSP
  have hcube : 60*(256000*C*C)^3≤(60*256000^3)*P := by
    calc
      _ = (60*256000^3)*C^6:=by ring
      _ ≤ _:=Nat.mul_le_mul_left _ hCSP
  have hscale : (256000*C*C)*(4*S)≤1024000*P := by
    calc
      _ = 1024000*(C^2*S):=by ring
      _ ≤ 1024000*(C^6*S):=Nat.mul_le_mul_left _ (Nat.mul_le_mul_right S hCp)
      _ = _:=rfl
  refine ⟨hfirst.trans ((Nat.mul_le_mul_right P (by norm_num)).trans hK),?_,?_⟩
  · calc
      _ ≤ (60*256000^3)*P:=hcube
      _ < (10:ℕ)^24*P:=Nat.mul_lt_mul_of_pos_right (by norm_num) hP
      _ ≤ _:=hK
  · exact hscale.trans ((Nat.mul_le_mul_right P (by norm_num)).trans hK)

/-- A single radius dominates every multiplicity cap at most 4S, while
retaining a fixed residue cutoff and the existing sixth-moment budget. -/
theorem linear_seed_parameters (C S m : ℕ) (hC : 4000≤C) (hS : 1≤S)
    (hsize : linearHalfBound C S≤m) :
    ∃ r : ℕ,1≤r ∧ r≤m ∧ 4*S<r ∧
      1000*C*C*(2*(64*r))≤m ∧ 3000*(m:ℝ)^4<(r:ℝ)^6 := by
  obtain ⟨hbig,hcube,hscale⟩:=linear_size_conditions C S m hC hS hsize
  let den:=256000*C*C
  have hden : 1<den:=by dsimp [den];nlinarith only [hC]
  have hdenpos : 0<den:=by omega
  have hdenR : (0:ℝ)<(den:ℝ):=by exact_mod_cast hdenpos
  have hmpos : 0<m:=by omega
  have hdenm : den≤m:=by change 1000*den≤m at hbig;omega
  let r:=m/den+1
  have hr : 1≤r:=Nat.succ_le_succ (Nat.zero_le (m/den))
  have hrm : r≤m:=Nat.succ_le_of_lt (Nat.div_lt_self hmpos hden)
  have hdiv:=Nat.mul_div_le m den
  have hdenr : den*r≤m+den:=by dsimp [r];nlinarith only [hdiv]
  have he : den*r=2*(1000*C*C*(2*(64*r))) := by dsimp [den];ring
  have hsmall : 1000*C*C*(2*(64*r))≤m:=by rw [he] at hdenr;omega
  have hscaleDiv : 4*S≤m/den := by
    apply (Nat.le_div_iff_mul_le hdenpos).mpr
    simpa only [den,Nat.mul_comm] using hscale
  have hlarge : 4*S<r:=by dsimp [r];omega
  have hrlarge : m<den*r:=Nat.lt_mul_div_succ m hdenpos
  have hrR : (m:ℝ)<(den:ℝ)*(r:ℝ):=by exact_mod_cast hrlarge
  have hrel : (m:ℝ)/(den:ℝ)≤(r:ℝ):=
    (div_le_iff₀ hdenR).mpr (by nlinarith only [hrR])
  have hmoment:=Gate8J2C.sixth_moment_3000_of_cubic_bound den m hdenpos hcube
  have hp:=pow_le_pow_left₀ (show (0:ℝ)≤(m:ℝ)/(den:ℝ) by positivity) hrel 6
  exact ⟨r,hr,hrm,hlarge,hsmall,hmoment.trans_le hp⟩

/-- Any actually constructed seed error t bounded by 64r fits the same
small-error budget. This does not supply a seed or an edge colouring. -/
theorem linear_error_mono (C r t m : ℕ) (ht : t≤64*r)
    (hsmall : 1000*C*C*(2*(64*r))≤m) : 1000*C*C*(2*t)≤m := by
  have hh:=Nat.mul_le_mul_left (1000*C*C*2) ht
  nlinarith only [hh,hsmall]

end OverfullWork.Gate8J2I
