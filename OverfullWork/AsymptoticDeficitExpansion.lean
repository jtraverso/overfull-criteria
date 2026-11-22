module

public import OverfullWork.SparseDeficitExpansionScale

@[expose] public section


/-! # Uniform robust expansion from a quadratic deficit estimate

For each positive above-half density margin, the scale and deficit
coefficient are chosen before the graph. The deficit estimate remains an
explicit hypothesis. These conclusions concern robust expansion only;
no critical average-degree or edge-colouring theorem is assumed.
-/
namespace OverfullWork.RobustExpansion
open SimpleGraph Finset SparseDeficitCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 2000000

/-- A real quadratic deficit estimate implies the strict integer mass
budget required by the nonvacuous scale construction. -/
theorem integer_mass_budget_of_quadratic_bound (n q B : ℕ) (hq : 0<q)
    (hB : (B:ℝ)≤(1/(262144*(q:ℝ)^3))*(n:ℝ)^2) :
    B<(n/(8*q)+1)*(n/(4096*q^2)+1) := by
  let a:=n/(8*q)
  let k:=n/(4096*q^2)
  have ha : n<8*q*(a+1) := Nat.lt_mul_div_succ n (by positivity)
  have hk : n<4096*q^2*(k+1) := Nat.lt_mul_div_succ n (by positivity)
  have hprod : n^2<32768*q^3*(a+1)*(k+1) := by
    calc
      _ = n*n := by ring
      _ ≤ (8*q*(a+1))*n := Nat.mul_le_mul_right n ha.le
      _ < (8*q*(a+1))*(4096*q^2*(k+1)) :=
        Nat.mul_lt_mul_of_pos_left hk (by positivity)
      _ = _ := by ring
  have hprodR : (n:ℝ)^2<32768*(q:ℝ)^3*((a:ℝ)+1)*((k:ℝ)+1) := by
    exact_mod_cast hprod
  have hqR : (0:ℝ)<(q:ℝ) := by exact_mod_cast hq
  have hden : (0:ℝ)<262144*(q:ℝ)^3 := by positivity
  have hBdiv : (B:ℝ)≤(n:ℝ)^2/(262144*(q:ℝ)^3) := by
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using hB
  have hBscaled := (le_div_iff₀ hden).mp hBdiv
  have hsmall : 32768*(q:ℝ)^3*(B:ℝ)≤(n:ℝ)^2 := by
    have hnonneg : (0:ℝ)≤(q:ℝ)^3*(B:ℝ) := by positivity
    nlinarith only [hBscaled,hnonneg]
  have hstrict : 32768*(q:ℝ)^3*(B:ℝ)<
      32768*(q:ℝ)^3*(((a:ℝ)+1)*((k:ℝ)+1)) := by
    nlinarith only [hsmall,hprodR]
  have hh : (B:ℝ)<((a:ℝ)+1)*((k:ℝ)+1) :=
    (mul_lt_mul_iff_of_pos_left (by positivity : (0:ℝ)<32768*(q:ℝ)^3)).mp hstrict
  exact_mod_cast hh

/-- At a fixed integer scale, the ordinary above-half real density
hypothesis supplies the integer minimum-degree margin automatically. -/
theorem isRobustAt_of_quadratic_deficit_scale (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0<ε) (q : ℕ) (hq : 2≤q)
    (hqe : (5:ℝ)≤16*(q:ℝ)*ε) (hn : 4096*q^2≤Fintype.card V)
    (hdense : ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ))
    (hmass : (totalDeficit G G.maxDegree:ℝ)≤
      (1/(262144*(q:ℝ)^3))*(Fintype.card V:ℝ)^2) :
    let a:=Fintype.card V/(8*q)
    let k:=Fintype.card V/(4096*q^2)
    0<k+1 ∧ 2*(a+k)≤Fintype.card V ∧ IsRobustAt G (k+1) (a+k) := by
  let a:=Fintype.card V/(8*q)
  have hafloor : 8*q*a≤Fintype.card V := Nat.mul_div_le (Fintype.card V) (8*q)
  have hafloorR : 8*(q:ℝ)*(a:ℝ)≤(Fintype.card V:ℝ) := by exact_mod_cast hafloor
  have haeps : 5*(a:ℝ)≤2*ε*(Fintype.card V:ℝ) := by
    have hfirst := mul_le_mul_of_nonneg_right hqe (Nat.cast_nonneg a : (0:ℝ)≤(a:ℝ))
    have hsecond := mul_le_mul_of_nonneg_left hafloorR (by positivity : (0:ℝ)≤2*ε)
    nlinarith only [hfirst,hsecond]
  have hdenseInt : Fintype.card V+5*a≤2*G.maxDegree := by
    exact_mod_cast (show (Fintype.card V:ℝ)+5*(a:ℝ)≤2*(G.maxDegree:ℝ) by
      nlinarith only [hdense,haeps])
  have hmassInt := integer_mass_budget_of_quadratic_bound (Fintype.card V) q
    (totalDeficit G G.maxDegree) (by omega) hmass
  exact isRobustAt_of_nonvacuous_deficit_scale G q hq hn hmassInt hdenseInt

/-- A uniform deficit coefficient and order threshold yield robust
expansion at explicit linear scales. All choices precede the graph. -/
theorem above_half_quadratic_deficit_robust_expansion (ε : ℝ) (hε : 0<ε) :
    ∃ q : ℕ,2≤q ∧ ∃ η : ℝ,0<η ∧ ∃ N : ℕ,
      ∀ {W : Type*} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        (totalDeficit G G.maxDegree:ℝ)≤η*(Fintype.card W:ℝ)^2 →
        let a:=Fintype.card W/(8*q)
        let k:=Fintype.card W/(4096*q^2)
        0<k+1 ∧ 2*(a+k)≤Fintype.card W ∧ IsRobustAt G (k+1) (a+k) := by
  obtain ⟨q,hq⟩ := exists_nat_gt (max (2:ℝ) (5/(16*ε)))
  have hqlo : (2:ℝ)<(q:ℝ) := lt_of_le_of_lt (le_max_left _ _) hq
  have hqNat : 2≤q := by exact_mod_cast hqlo.le
  have hqeps : (5:ℝ)≤16*(q:ℝ)*ε := by
    have hh : 5/(16*ε)<(q:ℝ) := lt_of_le_of_lt (le_max_right _ _) hq
    have hm := (div_lt_iff₀ (by positivity : (0:ℝ)<16*ε)).mp hh
    nlinarith only [hm]
  refine ⟨q,hqNat,1/(262144*(q:ℝ)^3),by positivity,4096*q^2,?_⟩
  intro W _ _ G _ hn hdense hmass
  exact isRobustAt_of_quadratic_deficit_scale G ε hε q hqNat hqeps hn hdense hmass

end OverfullWork.RobustExpansion
