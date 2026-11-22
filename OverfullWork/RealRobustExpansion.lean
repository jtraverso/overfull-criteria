module

public import OverfullWork.CanonicalAboveHalfGlobalRobust

@[expose] public section


/-! # Real normalized global robustness in the published convention

Both the robust neighbour threshold and the expansion gain are nu times
the full order. The admissible set sizes are tau*n through (1-tau)*n.
-/
namespace OverfullWork.RobustExpansion
open SimpleGraph Finset PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

noncomputable def realNeighbourhood (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : ℝ) (S : Finset V) : Finset V :=
  univ.filter fun v=>ν*(Fintype.card V:ℝ)≤(neighboursIn G S v:ℝ)

def IsRealRobust (G : SimpleGraph V) [DecidableRel G.Adj] (ν τ : ℝ) : Prop :=
  ∀S : Finset V,τ*(Fintype.card V:ℝ)≤(S.card:ℝ) →
    (S.card:ℝ)≤(1-τ)*(Fintype.card V:ℝ) →
    (S.card:ℝ)+ν*(Fintype.card V:ℝ)≤((realNeighbourhood G ν S).card:ℝ)

theorem isRealRobust_of_integer (G : SimpleGraph V) [DecidableRel G.Adj]
    (r t : ℕ) (ν τ : ℝ) (hRobust : IsRobustAt G r t)
    (hν : ν*(Fintype.card V:ℝ)≤(r:ℝ))
    (hτ : (t:ℝ)≤τ*(Fintype.card V:ℝ)) : IsRealRobust G ν τ := by
  intro S hlo hhi
  have hLow:t≤S.card:=by exact_mod_cast (hτ.trans hlo)
  have hHigh:S.card+t≤Fintype.card V:=by
    exact_mod_cast (show (S.card:ℝ)+(t:ℝ)≤(Fintype.card V:ℝ) by linarith only [hhi,hτ])
  have hCount:=hRobust S hLow hHigh
  have hSub:neighbourhood G r S⊆realNeighbourhood G ν S:=by
    intro v hv
    have hh:(r:ℝ)≤(neighboursIn G S v:ℝ):=by exact_mod_cast (mem_filter.mp hv).2
    exact mem_filter.mpr ⟨mem_univ _,hν.trans hh⟩
  have hCard:(S.card:ℝ)+(r:ℝ)≤((realNeighbourhood G ν S).card:ℝ):=by
    exact_mod_cast hCount.trans (card_le_card hSub)
  linarith only [hCard,hν]

end OverfullWork.RobustExpansion

namespace OverfullWork.CanonicalGlobalRobust
set_option maxHeartbeats 12000000

noncomputable def globalNu (P : ℕ) : ℝ := 1/(2^33*(P:ℝ)^3)
noncomputable def globalTau (P : ℕ) : ℝ := 1/(1024*(P:ℝ))

theorem normalized_parameters (P : ℕ) (hP : 2≤P) :
    0<globalNu P ∧ globalNu P≤globalTau P ∧ 0<globalTau P ∧ globalTau P<1/3 := by
  have hPR:(2:ℝ)≤P:=by exact_mod_cast hP
  have hPpos:(0:ℝ)<P:=by positivity
  have hSquare:(1:ℝ)≤(P:ℝ)^2:=by nlinarith only [hPR,sq_nonneg ((P:ℝ)-1)]
  have hCube:=mul_le_mul_of_nonneg_right hSquare hPpos.le
  have hDen:1024*(P:ℝ)≤2^33*(P:ℝ)^3:=by nlinarith only [hCube,hPpos.le]
  refine ⟨by unfold globalNu;positivity,?_,by unfold globalTau;positivity,?_⟩
  · exact one_div_le_one_div_of_le (by positivity) hDen
  · unfold globalTau
    apply (div_lt_iff₀ (show 0<1024*(P:ℝ) by positivity)).mpr
    nlinarith only [hPR]

theorem integer_thresholds_pay_real (P m : ℕ) (hP : 2≤P)
    (hr : 0<m/(2^30*P^3)) :
    globalNu P*((2*m:ℕ):ℝ)≤((m/(2^30*P^3):ℕ):ℝ) ∧
    ((m/(1024*P):ℕ):ℝ)≤globalTau P*((2*m:ℕ):ℝ) := by
  let d:=2^30*P^3
  let r:=m/d
  have hd:0<d:=by dsimp [d];positivity
  have hRem:m<d*(r+1):=Nat.lt_mul_div_succ m hd
  have hPos:1≤r:=by exact hr
  have hRev:m≤2*d*r:=by
    have hh:=Nat.mul_le_mul_left d (show r+1≤2*r by omega)
    nlinarith only [hRem,hh]
  have hNat:2*m≤r*(2^33*P^3):=by dsimp [d] at hRev;nlinarith only [hRev]
  constructor
  · unfold globalNu
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (show 0<2^33*(P:ℝ)^3 by positivity)).mpr
    exact_mod_cast hNat
  · unfold globalTau
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (show 0<1024*(P:ℝ) by positivity)).mpr
    have hh:=Nat.mul_div_le m (1024*P)
    exact_mod_cast (show (m/(1024*P))*(1024*P)≤2*m by nlinarith only [hh])

end OverfullWork.CanonicalGlobalRobust

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun CanonicalGlobalRobust
open scoped Classical
universe u

theorem above_half_real_global_robust_at_fixed_scale (ε : ℝ) (hε : 0<ε)
    (P : ℕ) (hP : 2≤P) (hPε : 1≤ε*(P:ℝ)) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),N≤Fintype.card V →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*P^2))+6 → K≤Fintype.card V/(4096*P^2)+1 →
      RobustExpansion.IsRealRobust p.completed.supportGraph (globalNu P) (globalTau P) := by
  obtain ⟨N,hN⟩:=above_half_global_robust_at_fixed_scale.{u} ε hε P hP hPε
  refine ⟨N,?_⟩
  intro V _ _ G _ B K c p hn hdense hB hK
  obtain ⟨hRobust,hPos,hSize⟩:=hN G c p hn hdense hB hK
  obtain ⟨hν,hτ⟩:=integer_thresholds_pay_real P (p.pairIndex+1) hP hPos
  apply RobustExpansion.isRealRobust_of_integer p.completed.supportGraph _ _ _ _ hRobust
  · simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm] using hν
  · simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm] using hτ

end OverfullWork.NormalizedCanonicalCandidate
