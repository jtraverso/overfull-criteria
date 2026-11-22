module

public import OverfullWork.EfficientPointSeed

@[expose] public section


/-! # The small-deficiency seed parameters exist uniformly for large orders -/

namespace OverfullWork.SeedThreshold

open SimpleGraph

/-- The moment constraint and the small error budget are simultaneously
satisfiable. This concerns the initial seed, not its regular completion. -/
theorem exists_parameters : ∃ m₀ : ℕ,∀ m : ℕ,m₀≤m →
    ∃ r : ℕ,1≤r ∧ r≤m ∧ 100000*(8*r+10)≤m ∧
      30*(m:ℝ)^4<(r:ℝ)^6 := by
  obtain ⟨N,hN⟩:=MultiGraph.eventually_sixth_size ((1:ℝ)/100000000) (by norm_num)
  refine ⟨max N 100000000,fun m hm => ?_⟩
  have hmN : N≤m:=(le_max_left N 100000000).trans hm
  have hm' : 100000000≤m:=(le_max_right N 100000000).trans hm
  let r:=m/100000000+1
  have hr1 : 1≤r:=by dsimp [r]; omega
  have hrsmall : 100000000*r≤m+100000000:=by dsimp [r]; omega
  have hrlarge : m<100000000*r:=by dsimp [r]; omega
  have hreal : (1:ℝ)/100000000*(m:ℝ)≤(r:ℝ) := by
    have h : (m:ℝ)<100000000*(r:ℝ):=by exact_mod_cast hrlarge
    linarith
  have hpow:=pow_le_pow_left₀ (show (0:ℝ)≤1/100000000*(m:ℝ) by positivity) hreal 6
  refine ⟨r,hr1,by omega,by omega,(hN m hmN).trans_le hpow⟩

/-- Reserving 300t extra colours for the sparse internal remainder still
leaves a strict palette margin. This is arithmetic, not a completion lemma. -/
theorem palette_with_reserve (m D r k : ℕ) (hmD : m≤D)
    (hsmall : 100000*(8*r+10)≤m) (hk : k≤D/2+3*r+2) :
    k+300*(8*r+10)<D := by omega

end OverfullWork.SeedThreshold
