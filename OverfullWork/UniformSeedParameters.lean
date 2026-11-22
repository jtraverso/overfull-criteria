module

public import OverfullWork.GeneralInternalCover
public import OverfullWork.UniformCompletionMargins

@[expose] public section


/-! # Uniform moments and small error for every fixed binary depth -/
namespace OverfullWork.Gate8H2
open SimpleGraph
open scoped Classical
set_option maxHeartbeats 4000000

/-- The threshold precedes both the order and every graph. -/
theorem exists_uniform_parameters (j c : ℕ) (hc : 1000≤c) :
    ∃ m₀ : ℕ,∀ m : ℕ,m₀≤m → ∃ r : ℕ,1≤r ∧ r≤m ∧
      1000*c*c*((4*2^j+2)*(r+1))≤m ∧
      30*(m:ℝ)^4*(((2^j:ℕ):ℝ)*(j+3:ℕ))^6<(r:ℝ)^6 := by
  let A:=4*2^j+2
  let den:=4000*c*c*A
  let R : ℝ:=((2^j:ℕ):ℝ)*(j+3:ℕ)
  have hA : 1≤A:=by dsimp [A];omega
  have hden : 1<den:=by
    have hh:=Nat.mul_le_mul_left (4000*c*c) hA
    have hcoef : 1<4000*c*c:=by nlinarith only [hc]
    dsimp [den]
    nlinarith only [hh,hcoef]
  have hdenR : (0:ℝ)<(den:ℝ):=by exact_mod_cast (show 0<den by omega)
  have hR : 0<R:=by dsimp [R];positivity
  let ε : ℝ:=1/((den:ℝ)*R)
  have hε : 0<ε:=by dsimp [ε];positivity
  obtain ⟨N,hN⟩:=MultiGraph.eventually_sixth_size ε hε
  refine ⟨max N (100000*c*c*A),fun m hm => ?_⟩
  have hmN : N≤m:=(le_max_left _ _).trans hm
  have hbig : 100000*c*c*A≤m:=(le_max_right _ _).trans hm
  have hmpos : 0<m:=by
    have hp : 0<100000*c*c*A:=by positivity
    omega
  let r:=m/den+1
  have hr : 1≤r:=Nat.succ_le_succ (Nat.zero_le (m/den))
  have hrm : r≤m:=Nat.succ_le_of_lt (Nat.div_lt_self hmpos hden)
  have hq:=Nat.mul_div_le m den
  have hrbound : den*r≤m+den:=by dsimp [r];nlinarith only [hq]
  have hsmall : 1000*c*c*(A*(r+1))≤m:=by
    dsimp [den] at hrbound
    nlinarith only [hrbound,hbig]
  have hrlarge : m<den*r:=Nat.lt_mul_div_succ m (by omega)
  have hrR : (m:ℝ)<(den:ℝ)*(r:ℝ):=by exact_mod_cast hrlarge
  have hrel : ε*(m:ℝ)≤(r:ℝ)/R := by
    dsimp [ε]
    apply (le_div_iff₀ hR).mpr
    have hle : (m:ℝ)/(den:ℝ)≤(r:ℝ):=(div_le_iff₀ hdenR).mpr (by nlinarith only [hrR])
    calc
      1 / (↑den * R) * ↑m * R = (m:ℝ)/(den:ℝ) := by
        field_simp
      _ ≤ (r:ℝ) := hle
  have hmoment:=hN m hmN
  have hp:=pow_le_pow_left₀ (show (0:ℝ)≤ε*(m:ℝ) by positivity) hrel 6
  have hh:=hmoment.trans_le hp
  rw [div_pow] at hh
  have hscaled:= (lt_div_iff₀ (pow_pos hR 6)).mp hh
  exact ⟨r,hr,hrm,by simpa only [A] using hsmall,by simpa only [R] using hscaled⟩

/-- A single stronger sixth moment implies both moments used by the engine. -/
theorem binary_moments_of_strong_moment (j m D r : ℕ) (hm : 1≤m) (hrm : r≤m)
    (hD : D≤2*m)
    (hsize : 30*(m:ℝ)^4*(((2^j:ℕ):ℝ)*(j+3:ℕ))^6<(r:ℝ)^6) :
    30*(m:ℝ)^4<(2*(r:ℝ)/(2^j:ℕ))^6 ∧
      15*(2*m:ℝ)*(D/2+r+j*r+1:ℕ)^3<(2*r:ℝ)^6 := by
  let μ : ℝ:=((2^j:ℕ):ℝ)
  let J : ℝ:=(j+3:ℕ)
  let R : ℝ:=μ*J
  have hμ : 1≤μ:=by dsimp [μ];exact_mod_cast (Nat.one_le_pow j 2 (by omega))
  have hJ : 1≤J:=by dsimp [J];exact_mod_cast (show 1≤j+3 by omega)
  have hμR : μ≤R:=by dsimp [R];nlinarith only [hμ,hJ]
  have hJR : J≤R:=by dsimp [R];nlinarith only [hμ,hJ]
  have hR : 1≤R:=hJ.trans hJR
  have hpowμ : μ^6≤R^6:=pow_le_pow_left₀ (by linarith) hμR 6
  have hpowJ : J^3≤R^6 := by
    calc
      J^3 ≤ R^3:=pow_le_pow_left₀ (by linarith) hJR 3
      _ ≤ R^6:=pow_le_pow_right₀ hR (by omega)
  have hdouble : (r:ℝ)^6≤(2*(r:ℝ))^6:=pow_le_pow_left₀ (by positivity) (by nlinarith [Nat.cast_nonneg r (α:=ℝ)]) 6
  have hstrong : 30*(m:ℝ)^4*R^6<(r:ℝ)^6:=hsize
  constructor
  · rw [div_pow]
    apply (lt_div_iff₀ (show (0:ℝ)<((2^j:ℕ):ℝ)^6 by positivity)).mpr
    have hmul:=mul_le_mul_of_nonneg_left hpowμ (show (0:ℝ)≤30*(m:ℝ)^4 by positivity)
    exact hmul.trans_lt (hstrong.trans_le hdouble)
  · have hjr:=Nat.mul_le_mul_left j hrm
    have hq : D/2+r+j*r+1≤(j+3)*m:=by nlinarith [show D/2≤m by omega]
    have hqR : ((D/2+r+j*r+1:ℕ):ℝ)≤J*(m:ℝ):=by dsimp [J];exact_mod_cast hq
    have hpow:=pow_le_pow_left₀ (Nat.cast_nonneg _) hqR 3
    have hmul:=mul_le_mul_of_nonneg_left hpow (show (0:ℝ)≤15*(2*(m:ℝ)) by positivity)
    have hmulJ:=mul_le_mul_of_nonneg_left hpowJ (show (0:ℝ)≤30*(m:ℝ)^4 by positivity)
    calc
      _ ≤ 30*(m:ℝ)^4*J^3:=by nlinarith only [hmul]
      _ ≤ 30*(m:ℝ)^4*R^6:=hmulJ
      _ < (r:ℝ)^6:=hstrong
      _ ≤ _:=hdouble

end OverfullWork.Gate8H2
