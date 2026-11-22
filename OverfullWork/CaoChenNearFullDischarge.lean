module

public import OverfullWork.CaoChenSmallChargeAssembly

@[expose] public section


/-! # The nearly-full-neighbour R1 case down to half the epsilon scale

The sharp donation quotient closes the near-full case for roots of degree
at least epsilon*Delta/2. Together with the small-root theorem this leaves
no unhandled strip between the two degree regimes.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 4000000

/-- Near-full high-neighbour counts discharge every root in the stated
medium range. The charge is the original real R1 transfer formula. -/
theorem charge_ge_of_near_full_half_margin
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (s : ℕ) (hs : 0<s)
    (hsmall : (s:ℝ)≤ε^2*(G.maxDegree:ℝ)/4) (x : V)
    (hxlo : ε*(G.maxDegree:ℝ)/2≤(G.degree x:ℝ))
    (hxhi : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hhigh : ∀y,G.Adj x y → G.maxDegree≤highCount G ((1-ε)*(G.maxDegree:ℝ)) y+s) :
    (1-ε)*(G.maxDegree:ℝ)≤R1Charge G ((1-ε)*(G.maxDegree:ℝ)) x := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  have hsR : (0:ℝ)<(s:ℝ):=by exact_mod_cast hs
  have hD : (0:ℝ)<(G.maxDegree:ℝ) := by
    have hn : (0:ℝ)≤(G.maxDegree:ℝ):=Nat.cast_nonneg _
    have hxN : (0:ℝ)≤(G.degree x:ℝ):=Nat.cast_nonneg _
    by_contra hp
    have hz : (G.maxDegree:ℝ)=0 := by linarith
    rw [hz,mul_zero] at hxhi
    linarith
  have heD : 0<ε*(G.maxDegree:ℝ):=mul_pos hε hD
  have he : ε^2≤ε := by nlinarith only [hε,hεone]
  have heDle:=mul_le_mul_of_nonneg_right he hD.le
  have hdon : ∀y∈G.neighborFinset x,ε*(G.maxDegree:ℝ)/(s:ℝ)≤donation G q y := by
    intro y hy
    have hxy:=(mem_neighborFinset G x y).mp hy
    have hh:=hhigh y hxy
    have hhR : (G.maxDegree:ℝ)≤(highCount G q y:ℝ)+(s:ℝ):=by exact_mod_cast hh
    have hq : q<(highCount G q y:ℝ) := by dsimp [q];nlinarith only [hhR,hsmall,heDle,heD]
    have hg:=donation_ge_of_high_neighbour_budget (G:=G) q hxy hxhi s hs hh hq
    have heq : (G.maxDegree:ℝ)-q=ε*(G.maxDegree:ℝ):=by dsimp [q];ring
    rwa [heq] at hg
  have hsum:=sum_le_sum hdon
  rw [sum_const,nsmul_eq_mul,card_neighborFinset_eq_degree] at hsum
  have htarget : (G.maxDegree:ℝ)≤(G.degree x:ℝ)*(ε*(G.maxDegree:ℝ)/(s:ℝ)) := by
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hsR).mpr
    have hfirst:=mul_le_mul_of_nonneg_right hxlo heD.le
    have hsecond:=mul_le_mul_of_nonneg_right hsmall hD.le
    nlinarith only [hfirst,hsecond]
  rw [low_charge_formula G q x hxhi]
  change q≤_
  have hxN : (0:ℝ)≤(G.degree x:ℝ):=Nat.cast_nonneg _
  dsimp [q] at *
  nlinarith only [hsum,htarget,hxN,heD]

end OverfullWork.CaoChenDischarging
