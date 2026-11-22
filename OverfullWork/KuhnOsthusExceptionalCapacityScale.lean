module

public import OverfullWork.KuhnOsthusWoundEndpointBudget

@[expose] public section


/-! Integer capacities for Lemma 7.6 from a common scale on the
retained style cells. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical

/-- Both capacity choices can be rounded down from the same cell
scale. The greedy endpoint loss is linear in the exceptional count,
and the route capacity retains at least half of the nominal scale. -/
theorem kuhn_osthus_exceptional_capacities (m c z e : ℕ)
    (hc : 32 ≤ c) (hm : 2*c ≤ m) (he : e ≤ m/4) :
    let cap := m/c
    let budget := (2*z)/cap
    let loss := cap+(cap+2)+2*cap
    0 < cap ∧ 2*z < cap*(budget+1) ∧ 2*z+budget*m ≤ (4*c+2)*z ∧
      (m:ℝ)/(2*(c:ℝ)) ≤ (cap:ℝ) ∧ loss ≤ m/4 ∧
      2*(cap+2+2*cap)+e < m-cap := by
  intro cap budget loss
  have hc₀ : 0 < c := by omega
  have hcap : 1 ≤ cap := by
    apply (Nat.le_div_iff_mul_le hc₀).mpr
    omega
  have hUpper : c*cap ≤ m := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
  have hLower : m ≤ (2*c)*cap := by
    have hh := (Nat.lt_mul_div_succ m hc₀).le.trans
      (Nat.mul_le_mul_left c (show cap+1 ≤ 2*cap by omega))
    simpa only [mul_left_comm c 2,mul_assoc] using hh
  have hBudget : budget*cap ≤ 2*z := Nat.div_mul_le_self _ _
  have hSpend : budget*m ≤ (4*c)*z := calc
    _ ≤ budget*((2*c)*cap) := Nat.mul_le_mul_left budget hLower
    _ = (2*c)*(budget*cap) := by ring
    _ ≤ (2*c)*(2*z) := Nat.mul_le_mul_left _ hBudget
    _ = _ := by ring
  have hEnd : 2*z+budget*m ≤ (4*c+2)*z := by
    rw [Nat.add_mul]
    omega
  have hScale : (m:ℝ)/(2*(c:ℝ)) ≤ (cap:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(c:ℝ))).mpr
    exact_mod_cast (show m ≤ cap*(2*c) by rwa [mul_comm cap])
  have hCap : 32*cap ≤ m := (Nat.mul_le_mul_right _ hc).trans hUpper
  have hBig : 64 ≤ m := by omega
  have hLoss : loss ≤ m/4 := by dsimp only [loss]; omega
  refine ⟨hcap,exceptional_endpoint_cluster_budget z cap hcap,hEnd,hScale,hLoss,?_⟩
  omega

end OverfullWork.DirectedRobustExpansion
