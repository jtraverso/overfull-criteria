module

public import OverfullWork.CaoChenRootPaletteNormalization
public import OverfullWork.CaoChenClaim52

@[expose] public section


/-! # Uniform numerical budgets for finite palette progress

The cutoff depends only on k and pays for initial normalization, all
secondary margins at most 4*k+5, and Claim 5.2 before normalization.
No progress or iteration theorem is assumed here.
-/
namespace OverfullWork.CaoChenUniformPaletteBudgets
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
set_option maxHeartbeats 4000000

def cutoff (k : ℕ) : ℕ := 1000*(k+1)^4

def secondaryCost (k M : ℕ) : ℕ :=
  4*k+3+(2*k+4)*(k+1)+(M+2)*(3*k+1)

/-- One graph-independent budget pays for every secondary step. -/
theorem secondary_budgets (k M : ℕ) (hM : M≤4*k+5) :
    2*k+2+k*(secondaryCost k M+1)≤cutoff k ∧
      secondaryCost k M+(k+1)*(2*k+2)≤cutoff k := by
  have hm:=Nat.mul_le_mul_right (3*k+1) (show M+2≤4*k+7 by omega)
  have hb : secondaryCost k M≤14*k^2+35*k+14 := by
    dsimp [secondaryCost]
    nlinarith only [hm]
  have hpoly₁ : 14*k^3+35*k^2+17*k+2≤cutoff k := by
    dsimp [cutoff]
    nlinarith only [Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3),Nat.zero_le (k^4)]
  have hpoly₂ : 16*k^2+39*k+16≤cutoff k := by
    dsimp [cutoff]
    nlinarith only [Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3),Nat.zero_le (k^4)]
  constructor
  · have hh:=Nat.mul_le_mul_left k (Nat.add_le_add_right hb 1)
    nlinarith only [hh,hpoly₁]
  · nlinarith only [hb,hpoly₂]

/-- The initial normalization uses at most 3*k+1 selected colours and
two extra protected colours. -/
theorem initial_budgets (k c e : ℕ) (hc : c≤3*k+1) (he : e≤2) :
    4*k+5+(c-1)*(e+(4*k+8)*c+1)≤cutoff k ∧
      e+(4*k+8)*c+c*(4*k+5)≤cutoff k := by
  have hsub : c-1≤3*k := by omega
  have hh:=Nat.mul_le_mul_left (4*k+8) hc
  have hi : e+(4*k+8)*c+1≤12*k^2+28*k+11 := by nlinarith only [hh,he]
  have hmul:=Nat.mul_le_mul hsub hi
  have hpoly₁ : 36*k^3+84*k^2+37*k+5≤cutoff k := by
    dsimp [cutoff]
    nlinarith only [Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3),Nat.zero_le (k^4)]
  have hm:=Nat.mul_le_mul_left (8*k+13) hc
  have hpoly₂ : 24*k^2+47*k+15≤cutoff k := by
    dsimp [cutoff]
    nlinarith only [Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3),Nat.zero_le (k^4)]
  exact ⟨by nlinarith only [hmul,hpoly₁],by nlinarith only [hm,he,hpoly₂]⟩

/-- Claim 5.2 is paid for k+1 candidates, at most 3*k*(k+1) protected
colours, and overlap threshold zero. -/
theorem claim52_budgets (k c : ℕ) (hc : c≤3*k*(k+1)) :
    c+k*(k+1+3*c+1)≤cutoff k ∧
      k+1+3*c+(k+1)*c≤cutoff k := by
  have hm:=Nat.mul_le_mul_left (3*k) hc
  have hpoly₁ : 9*k^3+13*k^2+5*k≤cutoff k := by
    dsimp [cutoff]
    nlinarith only [Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3),Nat.zero_le (k^4)]
  have hm₂:=Nat.mul_le_mul_left (k+4) hc
  have hpoly₂ : 3*k^3+15*k^2+13*k+1≤cutoff k := by
    dsimp [cutoff]
    nlinarith only [Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3),Nat.zero_le (k^4)]
  exact ⟨by nlinarith only [hc,hm,hpoly₁],by nlinarith only [hm₂,hpoly₂]⟩

/-- The same cutoff pays for the root normalization in Lemma 8: k+2
selected spine colours, 3*k+1 common bad colours, and margin 3*k+1. -/
theorem lemma8_budgets (k : ℕ) :
    3*k+1+(k+2-1)*(3*k+1+(3*k+4)*(k+2)+1)≤cutoff k ∧
      3*k+1+(3*k+4)*(k+2)+(k+2)*(3*k+1)≤cutoff k := by
  have h₁ : 3*k^3+16*k^2+26*k+11≤cutoff k := by
    dsimp [cutoff]
    nlinarith only [Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3),Nat.zero_le (k^4)]
  have h₂ : 6*k^2+20*k+11≤cutoff k := by
    dsimp [cutoff]
    nlinarith only [Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3),Nat.zero_le (k^4)]
  constructor
  · have he : k+2-1=k+1 := by omega
    rw [he]
    nlinarith only [h₁]
  · nlinarith only [h₂]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- One maximum-degree bound supplies a strict root-missing budget at
every colouring of G-xy with a low root. -/
theorem missing_root_gt_cutoff {c : PEC G (Fin G.maxDegree)} {x y : V}
    (hcm : IsColMinus c x y) (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ)) :
    cutoff k<(missing c x).card := by
  have he : ε^2≤ε := by nlinarith only [hε,hεone]
  have heD:=mul_le_mul_of_nonneg_right he (Nat.cast_nonneg G.maxDegree : (0:ℝ)≤_)
  have hm:=hcm.card_missing_end (Or.inl rfl)
  have hmR : ((missing c x).card:ℝ)+(G.degree x:ℝ)=(G.maxDegree:ℝ)+1 := by
    exact_mod_cast hm
  have hh : (cutoff k:ℝ)<((missing c x).card:ℝ) := by
    nlinarith only [hlarge,heD,hmR,hx]
  exact_mod_cast hh

end OverfullWork.CaoChenUniformPaletteBudgets
