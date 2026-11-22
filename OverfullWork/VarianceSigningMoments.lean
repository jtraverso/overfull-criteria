module

public import OverfullWork.SigningMoments

@[expose] public section


/-! # Signing moments controlled by the sum of squared coefficients

No bound on individual coefficients is required. The induction uses the
exact moment recurrences and keeps the variance instead of the dimension.
-/
namespace OverfullWork.VarianceSigningMoments
open Finset SigningMoments
set_option maxHeartbeats 2000000

def squareSum {m : ℕ} (a : Fin m → ℝ) : ℝ:=∑ i,(a i)^2

theorem squareSum_nonneg {m : ℕ} (a : Fin m → ℝ) : 0≤squareSum a :=
  sum_nonneg (fun _ _ => sq_nonneg _)

theorem squareSum_succ {m : ℕ} (a : Fin (m+1) → ℝ) :
    squareSum a=(a 0)^2+squareSum (fun i => a i.succ) := by
  exact Fin.sum_univ_succ _

theorem variance_moments (m : ℕ) (a : Fin m → ℝ) :
    moment a 2=squareSum a*2^m ∧
    moment a 4≤3*(squareSum a)^2*2^m ∧
    moment a 6≤15*(squareSum a)^3*2^m := by
  induction m with
  | zero => simp [moment,signedSum,squareSum]
  | succ m ih =>
    obtain ⟨h2,h4,h6⟩:=ih (fun i => a i.succ)
    have hV:=squareSum_nonneg (fun i => a i.succ)
    have hP : 0≤(2:ℝ)^m:=by positivity
    constructor
    · rw [moment_two_succ,h2,squareSum_succ,pow_succ (2:ℝ) m]
      ring
    constructor
    · rw [moment_four_succ,h2]
      calc
        _ ≤ 2*(3*(squareSum (fun i => a i.succ))^2*2^m)+
            12*(a 0)^2*(squareSum (fun i => a i.succ)*2^m)+2*(a 0)^4*2^m := by
          nlinarith only [h4]
        _ ≤ _ := by
          rw [squareSum_succ,pow_succ (2:ℝ) m]
          have hh : 0≤(a 0)^4*(2:ℝ)^m:=by positivity
          nlinarith only [hh]
    · rw [moment_six_succ,h2]
      have h4mul:=mul_le_mul_of_nonneg_left h4 (show 0≤30*(a 0)^2 by positivity)
      have h6mul:=mul_le_mul_of_nonneg_left h6 (show (0:ℝ)≤2 by norm_num)
      calc
        _ ≤ 2*(15*(squareSum (fun i => a i.succ))^3*2^m)+
            30*(a 0)^2*(3*(squareSum (fun i => a i.succ))^2*2^m)+
            30*(a 0)^4*(squareSum (fun i => a i.succ)*2^m)+2*(a 0)^6*2^m := by
          nlinarith only [h4mul,h6mul]
        _ ≤ _ := by
          rw [squareSum_succ,pow_succ (2:ℝ) m]
          have hh₁ : 0≤(a 0)^4*squareSum (fun i => a i.succ)*(2:ℝ)^m:=by positivity
          have hh₂ : 0≤(a 0)^6*(2:ℝ)^m:=by positivity
          nlinarith only [hh₁,hh₂]

/-- One signing controls all rows using their actual squared energies. -/
theorem exists_signing_sixth_variance_bound {R : Type*} [Fintype R] (m : ℕ)
    (a : R → Fin m → ℝ) :
    ∃ s : Fin m → Bool,∀ r,
      (signedSum (a r) s)^6≤15*∑ q : R,(squareSum (a q))^3 := by
  classical
  have hsum : (∑ s : Fin m → Bool,∑ r,(signedSum (a r) s)^6)≤
      ∑ _s : Fin m → Bool,15*∑ q : R,(squareSum (a q))^3 := by
    rw [sum_comm]
    calc
      _ ≤ ∑ q : R,15*(squareSum (a q))^3*(2:ℝ)^m := by
        exact sum_le_sum (fun r _ => (variance_moments m (a r)).2.2)
      _ = _ := by rw [sum_constant_signs];simp only [← mul_sum,← sum_mul]
  obtain ⟨s,_,hs⟩:=exists_le_of_sum_le (s:=univ) univ_nonempty hsum
  refine ⟨s,fun r => le_trans ?_ hs⟩
  exact single_le_sum (f:=fun r => (signedSum (a r) s)^6)
    (fun _ _ => by positivity) (mem_univ r)

/-- Numerical discrepancy criterion with unrestricted coefficients. -/
theorem exists_signing_variance_discrepancy {R : Type*} [Fintype R] (m : ℕ)
    (a : R → Fin m → ℝ) (b : ℝ) (hb : 0≤b)
    (hsize : 15*(∑ q : R,(squareSum (a q))^3)<b^6) :
    ∃ s : Fin m → Bool,∀ r,|signedSum (a r) s|<b := by
  obtain ⟨s,hs⟩:=exists_signing_sixth_variance_bound m a
  refine ⟨s,fun r => ?_⟩
  by_contra hn
  have hp:=pow_le_pow_left₀ hb (le_of_not_gt hn) 6
  rw [←abs_pow,abs_of_nonneg (by positivity : 0≤(signedSum (a r) s)^6)] at hp
  exact (not_lt_of_ge (le_trans hp (hs r))) hsize

end OverfullWork.VarianceSigningMoments
