module

public import OverfullWork.DoubleDegreeCutBudget
public import OverfullWork.BiasedExponentialSigning
public import Mathlib.Data.Fintype.Powerset

@[expose] public section


/-! A biased actual selection for two semidegree rows per vertex and all
cut rows. The finite exponential budget covers every row simultaneously. -/
namespace OverfullWork.BiasedDegreeCutSelection
open Finset Real
open scoped Classical
universe u v
set_option maxHeartbeats 24000000

def value {E : Type*} [Fintype E] (p : ℝ) (a : E → ℝ) (s : E → Bool) : ℝ :=
  ∑ e,if s e then (1-p)*a e else -p*a e

theorem exists_degree_cut_selection_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ,∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {E : Type v} [Fintype E]
      (degreeRow : V × Bool → E → ℝ) (cutRow : Finset V × Finset V → E → ℝ),
      N ≤ Fintype.card V →
      (∀ x,(∑ e,degreeRow x e^2) ≤ (Fintype.card V:ℝ)) →
      (∀ ST,(∑ e,cutRow ST e^2) ≤ 2*(Fintype.card V:ℝ)^2) →
      ∃ s : E → Bool,
        (∀ x,|value p (degreeRow x) s| < ε*(Fintype.card V:ℝ)) ∧
        ∀ S T : Finset V,|value p (cutRow (S,T)) s| < ε*(Fintype.card V:ℝ)^2 := by
  obtain ⟨N,hN⟩ := DoubleDegreeCutBudget.eventual_budget ε hε
  refine ⟨N,?_⟩
  intro p hp hp1 V _ _ E _ degreeRow cutRow hn hVarDegree hVarCuts
  let n := Fintype.card V
  let Rows := (V × Bool) ⊕ (Finset V × Finset V)
  let a : Rows → E → ℝ := Sum.elim degreeRow cutRow
  let t : Rows → ℝ := fun _ => ε/4
  let b : Rows → ℝ := Sum.elim (fun _ => ε*(n:ℝ)) (fun _ => ε*(n:ℝ)^2)
  have hVertex : ∀ v : V × Bool,
      2*exp ((t (.inl v))^2*(∑ e,a (.inl v) e^2)/2-t (.inl v)*b (.inl v)) ≤
        2*exp (-(ε^2*(n:ℝ))/8) := by
    intro v
    have hVar := hVarDegree v
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
    dsimp only [a,t,b,Sum.elim_inl]
    have hh := mul_le_mul_of_nonneg_left hVar (sq_nonneg (ε/4))
    change (ε/4)^2*(∑ e,degreeRow v e^2) ≤ (ε/4)^2*(n:ℝ) at hh
    have he : (0:ℝ) ≤ ε^2*(n:ℝ) := by positivity
    nlinarith only [hh,he]
  have hCuts : ∀ ST : Finset V × Finset V,
      2*exp ((t (.inr ST))^2*(∑ e,a (.inr ST) e^2)/2-t (.inr ST)*b (.inr ST)) ≤
        2*exp (-(ε^2*(n:ℝ)^2)/8) := by
    intro ST
    have hVar := hVarCuts ST
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
    dsimp only [a,t,b,Sum.elim_inr]
    have hh := mul_le_mul_of_nonneg_left hVar (sq_nonneg (ε/4))
    change (ε/4)^2*(∑ e,cutRow ST e^2) ≤ (ε/4)^2*(2*(n:ℝ)^2) at hh
    have he : (0:ℝ) ≤ ε^2*(n:ℝ)^2 := by positivity
    nlinarith only [hh,he]
  have hBudget : (∑ r : Rows,2*exp ((t r)^2*(∑ e,a r e^2)/2-t r*b r)) < 1 := by
    rw [Fintype.sum_sum_type]
    have h₁ := sum_le_sum (s:=univ) (fun v _ => hVertex v)
    have h₂ := sum_le_sum (s:=univ) (fun ST _ => hCuts ST)
    have hCard : Fintype.card (Finset V × Finset V)=4^n := by
      simp only [Fintype.card_prod,Fintype.card_finset]
      dsimp only [n]
      rw [←mul_pow]
      norm_num
    simp only [sum_const,card_univ,nsmul_eq_mul,hCard,Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat] at h₁ h₂
    have hFinal := hN n hn
    have hLe := add_le_add h₁ h₂
    change _ ≤ ((n:ℝ)*2)*(2*exp (-(ε^2*(n:ℝ))/8))+
      ((4^n:ℕ):ℝ)*(2*exp (-(ε^2*(n:ℝ)^2)/8)) at hLe
    push_cast at hLe
    nlinarith only [hLe,hFinal]
  obtain ⟨s,hs⟩ := BiasedExponentialSigning.exists_finite_selection_of_budget p hp hp1 a t b
    (by intro r;dsimp only [t];positivity) hBudget
  refine ⟨s,?_,?_⟩
  · intro v
    have hh := hs (.inl v)
    change |value p (degreeRow v) s| < ε*(n:ℝ) at hh
    exact hh
  · intro S T
    have hh := hs (.inr (S,T))
    change |value p (cutRow (S,T)) s| < ε*(n:ℝ)^2 at hh
    exact hh

theorem exists_degree_cut_selection (p ε : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      {E : Type v} [Fintype E]
      (degreeRow : V × Bool → E → ℝ) (cutRow : Finset V × Finset V → E → ℝ),
      N ≤ Fintype.card V →
      (∀ x,(∑ e,degreeRow x e^2) ≤ (Fintype.card V:ℝ)) →
      (∀ ST,(∑ e,cutRow ST e^2) ≤ 2*(Fintype.card V:ℝ)^2) →
      ∃ s : E → Bool,
        (∀ x,|value p (degreeRow x) s| < ε*(Fintype.card V:ℝ)) ∧
        ∀ S T : Finset V,|value p (cutRow (S,T)) s| < ε*(Fintype.card V:ℝ)^2 := by
  obtain ⟨N,hN⟩ := exists_degree_cut_selection_uniform.{u,v} ε hε
  exact ⟨N,hN p hp hp1⟩

end OverfullWork.BiasedDegreeCutSelection
