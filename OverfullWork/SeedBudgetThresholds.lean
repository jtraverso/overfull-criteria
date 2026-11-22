module

public import OverfullWork.FlexibleSeeds

@[expose] public section


namespace OverfullWork.Gate8G
set_option maxRecDepth 4096

theorem four_parameters_improved (m : ℕ) (hm : 200000000000000≤m) :
    ∃ r : ℕ,1≤r ∧ r≤m ∧ 1000*(16*r+20)≤m ∧
      30*(m:ℝ)^4<((r:ℝ)/2)^6 := by
  let r:=m/16000-2
  have hr : 1≤r:=by dsimp [r];omega
  have hrsmall : 1000*(16*r+20)≤m:=by dsimp [r];omega
  have hrlarge : m<16001*r:=by dsimp [r];omega
  have hmR : (200000000000000:ℝ)≤(m:ℝ):=by exact_mod_cast hm
  have hbase : 30*(m:ℝ)^4<((m:ℝ)/32002)^6 := by
    have hp : (0:ℝ)<(m:ℝ)^4:=by positivity
    have hconst : (30:ℝ)*32002^6<(200000000000000:ℝ)^2:=by norm_num
    have hsq:=hconst.trans_le (pow_le_pow_left₀ (by norm_num) hmR 2)
    have hmul:=mul_lt_mul_of_pos_right hsq hp
    rw [div_pow,lt_div_iff₀ (show (0:ℝ)<32002^6 by positivity)]
    convert hmul using 1 <;> ring
  have hreal : (m:ℝ)/32002≤(r:ℝ)/2 := by
    have hh : (m:ℝ)<16001*(r:ℝ):=by exact_mod_cast hrlarge
    linarith
  have hpow:=pow_le_pow_left₀ (show (0:ℝ)≤(m:ℝ)/32002 by positivity) hreal 6
  exact ⟨r,hr,by dsimp [r];omega,hrsmall,hbase.trans_le hpow⟩

theorem eight_parameters (m : ℕ) (hm : 20000000000000000000≤m) :
    ∃ r : ℕ,1≤r ∧ r≤m ∧ 10000*(32*r+40)≤m ∧
      30*(m:ℝ)^4<((r:ℝ)/4)^6 := by
  let r:=m/320000-2
  have hr : 1≤r:=by dsimp [r];omega
  have hrsmall : 10000*(32*r+40)≤m:=by dsimp [r];omega
  have hrlarge : m<320001*r:=by dsimp [r];omega
  have hmR : (20000000000000000000:ℝ)≤(m:ℝ):=by exact_mod_cast hm
  have hbase : 30*(m:ℝ)^4<((m:ℝ)/1280004)^6 := by
    have hp : (0:ℝ)<(m:ℝ)^4:=by positivity
    have hconst : (30:ℝ)*1280004^6<(20000000000000000000:ℝ)^2:=by norm_num
    have hsq:=hconst.trans_le (pow_le_pow_left₀ (by norm_num) hmR 2)
    have hmul:=mul_lt_mul_of_pos_right hsq hp
    rw [div_pow,lt_div_iff₀ (show (0:ℝ)<1280004^6 by positivity)]
    convert hmul using 1 <;> ring
  have hreal : (m:ℝ)/1280004≤(r:ℝ)/4 := by
    have hh : (m:ℝ)<320001*(r:ℝ):=by exact_mod_cast hrlarge
    linarith
  have hpow:=pow_le_pow_left₀ (show (0:ℝ)≤(m:ℝ)/1280004 by positivity) hreal 6
  exact ⟨r,hr,by dsimp [r];omega,hrsmall,hbase.trans_le hpow⟩

end OverfullWork.Gate8G
