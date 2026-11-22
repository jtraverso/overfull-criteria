module

public import OverfullWork.FourEfficientSeed

@[expose] public section


/-! # Explicit compatible numerical budgets for the multiplicity-four seed -/
namespace SimpleGraph.MultiGraph

theorem four_palette_size_of_partition_size (m D r : ℕ) (hm : 1≤m) (hD : D≤2*m)
    (hr : r≤m) (hsize : 30*(m:ℝ)^4<(r:ℝ)^6) :
    15*(2*m:ℝ)*(D/2+r+r+1:ℕ)^3<(2*r:ℝ)^6 := by
  have hq : D/2+r+r+1≤4*m:=by omega
  have hqR : ((D/2+r+r+1:ℕ):ℝ)≤4*(m:ℝ):=by exact_mod_cast hq
  have hpow:=pow_le_pow_left₀ (Nat.cast_nonneg (D/2+r+r+1)) hqR 3
  have hmul:=mul_le_mul_of_nonneg_left hpow (show (0:ℝ)≤15*(2*(m:ℝ)) by positivity)
  have he : (15:ℝ)*(2*(m:ℝ))*(4*(m:ℝ))^3=1920*(m:ℝ)^4:=by ring
  calc
    _ ≤ 1920*(m:ℝ)^4:=by simpa only [he] using hmul
    _ < 64*(r:ℝ)^6:=by linarith
    _ = _ := by ring

end SimpleGraph.MultiGraph

namespace OverfullWork.Gate8F2
set_option maxRecDepth 4096

/-- Conservative explicit seed threshold. This does not assert regular
completion of the colour classes or multiplicity-four factorization. -/
theorem explicit_seed_parameters (m : ℕ) (hm : 1000000000000000≤m) :
    ∃ r : ℕ,1≤r ∧ r≤m ∧ 1000*(16*r+20)≤m ∧
      30*(m:ℝ)^4<((r:ℝ)/2)^6 := by
  let r:=m/20000+1
  have hr : 1≤r:=by dsimp [r];omega
  have hrsmall : 20000*r≤m+20000:=by dsimp [r];omega
  have hrlarge : m<20000*r:=by dsimp [r];omega
  have hmR : (1000000000000000:ℝ)≤(m:ℝ):=by exact_mod_cast hm
  have hbase : 30*(m:ℝ)^4<((m:ℝ)/40000)^6 := by
    have hp : (0:ℝ)<(m:ℝ)^4:=by positivity
    have hconst : (30:ℝ)*40000^6<(1000000000000000:ℝ)^2:=by norm_num
    have hsq:=hconst.trans_le (pow_le_pow_left₀ (by norm_num) hmR 2)
    have hmul:=mul_lt_mul_of_pos_right hsq hp
    rw [div_pow,lt_div_iff₀ (show (0:ℝ)<40000^6 by positivity)]
    convert hmul using 1 <;> ring
  have hreal : (m:ℝ)/40000≤(r:ℝ)/2 := by
    have hh : (m:ℝ)<20000*(r:ℝ):=by exact_mod_cast hrlarge
    linarith
  have hpow:=pow_le_pow_left₀ (show (0:ℝ)≤(m:ℝ)/40000 by positivity) hreal 6
  exact ⟨r,hr,by omega,by omega,hbase.trans_le hpow⟩

theorem four_palette_with_reserve (m D r k : ℕ) (hmD : m≤D)
    (hsmall : 1000*(16*r+20)≤m) (hk : k≤D/2+7*r+4) :
    k+300*(16*r+20)<D := by omega

end OverfullWork.Gate8F2
