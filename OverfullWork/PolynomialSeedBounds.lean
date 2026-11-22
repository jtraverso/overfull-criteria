module

public import OverfullWork.QuantitativeSeedParameters

@[expose] public section


/-! # Polynomial order bound using a near-minimal binary depth -/
namespace OverfullWork.Gate8J2
set_option maxHeartbeats 4000000

def polynomialHalfBound (C S : ℕ) : ℕ:=1000000000000000000*C^6*S^15

/-- A cap within a factor two of the required multiplicity, with a simple
depth bound. This avoids the exponential loss of depth s+1. -/
theorem exists_efficient_binary_cap (s : ℕ) :
    ∃ j : ℕ,s+1≤2^j ∧ 2^j≤2*(s+1) ∧ j≤s+1 := by
  induction s with
  | zero => exact ⟨0,by norm_num,by norm_num,by omega⟩
  | succ s ih =>
    obtain ⟨j,hlo,hhi,hj⟩:=ih
    by_cases hnext : s+2≤2^j
    · exact ⟨j,by omega,by omega,by omega⟩
    · have he : 2^j=s+1:=by omega
      refine ⟨j+1,?_,?_,by omega⟩
      · rw [pow_succ,he];omega
      · rw [pow_succ,he];omega

/-- The polynomial bound pays both the small-error and cubic-moment
thresholds; all constants and exponents are finite inequalities. -/
theorem polynomial_seed_conditions (C S j m : ℕ) (hC : 4000≤C) (hS : 1≤S)
    (hmu : 2^j≤2*S) (hj : j≤S) (hsize : polynomialHalfBound C S≤m) :
    100000*(C*S)*(C*S)*(4*2^j+2)≤m ∧
      6*(4000*(C*S)*(C*S)*(4*2^j+2)*(2^j*(j+3)))^3<m := by
  let P:=C^6*S^15
  have hP : 0<P:=by dsimp [P];positivity
  have hA : 4*2^j+2≤10*S:=by omega
  have hR : 2^j*(j+3)≤8*S^2 := by
    calc
      _ ≤ (2*S)*(S+3):=Nat.mul_le_mul hmu (by omega)
      _ ≤ _:=by nlinarith only [hS]
  have hden : 4000*(C*S)*(C*S)*(4*2^j+2)≤40000*C^2*S^3 := by
    calc
      _ ≤ 4000*(C*S)*(C*S)*(10*S):=Nat.mul_le_mul_left _ hA
      _ = _:=by ring
  have hL : 4000*(C*S)*(C*S)*(4*2^j+2)*(2^j*(j+3))≤320000*C^2*S^5 := by
    calc
      _ ≤ (40000*C^2*S^3)*(8*S^2):=Nat.mul_le_mul hden hR
      _ = _:=by ring
  have hLcube : (4000*(C*S)*(C*S)*(4*2^j+2)*(2^j*(j+3)))^3≤320000^3*P := by
    have hh:=Nat.pow_le_pow_left hL 3
    convert hh using 1 <;> dsimp [P] <;> ring
  have hCp : C^2≤C^6:=pow_le_pow_right₀ (by omega : 1≤C) (by omega)
  have hSp : S^3≤S^15:=pow_le_pow_right₀ hS (by omega)
  have hfirst : 100000*(C*S)*(C*S)*(4*2^j+2)≤1000000*P := by
    calc
      _ ≤ 100000*(C*S)*(C*S)*(10*S):=Nat.mul_le_mul_left _ hA
      _ = 1000000*(C^2*S^3):=by ring
      _ ≤ _:=Nat.mul_le_mul_left 1000000 (Nat.mul_le_mul hCp hSp)
  have hK : 1000000000000000000*P≤m:=by simpa [polynomialHalfBound,P,Nat.mul_assoc] using hsize
  constructor
  · exact hfirst.trans ((Nat.mul_le_mul_right P (by norm_num)).trans hK)
  · calc
      _ ≤ (6*320000^3)*P:=by nlinarith only [hLcube]
      _ < 1000000000000000000*P:=Nat.mul_lt_mul_of_pos_right (by norm_num) hP
      _ ≤ m:=hK

end OverfullWork.Gate8J2
