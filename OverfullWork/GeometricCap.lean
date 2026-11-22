module

public import OverfullWork.PolynomialSeedBounds

@[expose] public section


/-! # Geometric caps with even binary depth

A fourth-power cap gives a square-root palette scale. These are finite
integer inequalities, without logarithms or asymptotic hypotheses.
-/
namespace OverfullWork.Gate8J2C
set_option maxHeartbeats 1000000

theorem square_binary_scale (h : ℕ) : (2^h)^2=4^h := by
  rw [←pow_mul,Nat.mul_comm h 2,pow_mul]
  norm_num

theorem even_binary_depth_cap (h : ℕ) : 2^(2*h)=4^h := by
  rw [pow_mul]
  norm_num

theorem exists_four_power_cap (s : ℕ) :
    ∃ h : ℕ,s+1≤4^h ∧ 4^h≤4*(s+1) := by
  induction s with
  | zero => exact ⟨0,by norm_num,by norm_num⟩
  | succ s ih =>
    obtain ⟨h,hlo,hhi⟩:=ih
    by_cases hnext : s+2≤4^h
    · exact ⟨h,by omega,by omega⟩
    · have he : 4^h=s+1:=by omega
      refine ⟨h+1,?_,?_⟩
      · rw [pow_succ,he];omega
      · rw [pow_succ,he];omega

/-- Upper bounds needed when the regularization gap is S-1 and the
palette error is measured on the binary square-root scale. -/
theorem geometric_scale_bounds (S h : ℕ) (hS : 1≤S) (hcap : 4^h≤4*S) :
    2^h≤2*S ∧ (2^h)^3≤8*S^2 ∧ S^3*(2^h)^3≤8*S^5 := by
  have hsq : (2^h)^2≤4*S := by rwa [square_binary_scale]
  have hSsq : S≤S^2 := by nlinarith only [hS]
  have hsq' : (2^h)^2≤(2*S)^2 := by
    calc
      _ ≤ 4*S:=hsq
      _ ≤ 4*S^2:=Nat.mul_le_mul_left 4 hSsq
      _ = _:=by ring
  have hlinear : 2^h≤2*S := by
    by_contra hn
    have hh : 2*S+1≤2^h:=by omega
    have hp:=Nat.pow_le_pow_left hh 2
    have hbad:=hp.trans hsq'
    ring_nf at hbad
    omega
  have hcubic : (2^h)^3≤8*S^2 := by
    calc
      _ = (2^h)*(2^h)^2:=by ring
      _ ≤ (2*S)*(4*S):=Nat.mul_le_mul hlinear hsq
      _ = _:=by ring
  refine ⟨hlinear,hcubic,?_⟩
  calc
    _ ≤ S^3*(8*S^2):=Nat.mul_le_mul_left (S^3) hcubic
    _ = _:=by ring

/-- An optimized cap preserving even binary depth. S=s+1 is the needed
multiplicity, mu=4^h is the chosen cap, and N=2^h its square root. -/
theorem exists_geometric_cap (s : ℕ) :
    ∃ h : ℕ,s+1≤4^h ∧ 4^h≤4*(s+1) ∧
      (2^h)^2=4^h ∧ 2^(2*h)=4^h ∧
      2^h≤2*(s+1) ∧ (2^h)^3≤8*(s+1)^2 ∧
      (s+1)^3*(2^h)^3≤8*(s+1)^5 := by
  obtain ⟨h,hlo,hhi⟩:=exists_four_power_cap s
  obtain ⟨hN,hN3,hS3N3⟩:=geometric_scale_bounds (s+1) h (by omega) hhi
  exact ⟨h,hlo,hhi,square_binary_scale h,even_binary_depth_cap h,hN,hN3,hS3N3⟩

end OverfullWork.Gate8J2C
