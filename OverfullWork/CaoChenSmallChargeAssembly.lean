module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public import OverfullWork.CaoChenR1SmallNumerics
public import OverfullWork.CaoChenSmallSpineCounts

@[expose] public section


/-! # Actual R1 charges from a bounded low-neighbour multiplicity

The final numerical estimate is applied to the real R1 transfer formula.
This module separates the finite low-neighbour budget from the charge
calculation; the former is constructed in the small-palette budget module.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenPalettes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

omit [DecidableEq V] in
/-- A minimum high-neighbour count gives the sharp reciprocal donation
bound at any neighbour of a low root. -/
theorem donation_ge_of_high_neighbour_budget (q : ℝ) {x u : V} (hxu : G.Adj x u)
    (hx : (G.degree x:ℝ)<q) (a : ℕ) (ha : 0<a)
    (hhigh : G.maxDegree≤highCount G q u+a)
    (hhq : q<(highCount G q u:ℝ)) :
    ((G.maxDegree:ℝ)-q)/(a:ℝ)≤donation G q u := by
  have hsN := lowCount_add_highCount G q u
  have hs : (lowCount G q u:ℝ)+(highCount G q u:ℝ)=(G.degree u:ℝ) := by exact_mod_cast hsN
  have hd : (G.degree u:ℝ)≤(G.maxDegree:ℝ) := by exact_mod_cast G.degree_le_maxDegree u
  have hb : (G.maxDegree:ℝ)≤(highCount G q u:ℝ)+(a:ℝ) := by exact_mod_cast hhigh
  have hlc : (0:ℝ)<(lowCount G q u:ℝ) := by
    exact_mod_cast lowCount_positive_of_low_neighbour G q hxu hx
  have haR : (0:ℝ)<(a:ℝ) := by exact_mod_cast ha
  have hsource : q<(G.degree u:ℝ) := by linarith
  rw [donation,if_pos hsource]
  apply (div_le_div_iff₀ haR hlc).mpr
  have hfirst : 0≤((highCount G q u:ℝ)-q)*((G.maxDegree:ℝ)-(G.degree u:ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  have hsecond : 0≤((a:ℝ)-(G.maxDegree:ℝ)+(highCount G q u:ℝ))*((G.degree u:ℝ)-q) :=
    mul_nonneg (by linarith) (by linarith)
  have he : (lowCount G q u:ℝ)=(G.degree u:ℝ)-(highCount G q u:ℝ) := by linarith
  rw [he]
  nlinarith only [hfirst,hsecond]

omit [DecidableEq V] in
/-- Positive low-neighbour denominators permit weighted Cauchy without
any square roots. -/
theorem reciprocal_lowCount_sum_ge (q : ℝ) {x : V} (hx : (G.degree x:ℝ)<q)
    (T : Finset V) (hT : T⊆G.neighborFinset x) (hpos : 0<T.card)
    (B : ℝ) (_hB : 0<B) (hbudget : (∑u∈T,(lowCount G q u:ℝ))≤B) :
    (T.card:ℝ)^2/B≤∑u∈T,1/(lowCount G q u:ℝ) := by
  have hlc : ∀u∈T,(0:ℝ)<(lowCount G q u:ℝ) := by
    intro u hu
    exact_mod_cast lowCount_positive_of_low_neighbour G q
      ((mem_neighborFinset G x u).mp (hT hu)) hx
  have hsumpos : (0:ℝ)<∑u∈T,(lowCount G q u:ℝ) :=
    sum_pos hlc (card_pos.mp hpos)
  have hc := Finset.sq_sum_div_le_sum_sq_div T (fun _ => (1:ℝ)) hlc
  have hc' : (T.card:ℝ)^2/(∑u∈T,(lowCount G q u:ℝ))≤∑u∈T,1/(lowCount G q u:ℝ) := by
    simpa only [sum_const,nsmul_eq_mul,mul_one,one_pow] using hc
  exact (div_le_div_of_nonneg_left (sq_nonneg _) hsumpos hbudget).trans hc'

/-- The combinatorial inputs concern only concrete degrees, neighbours
and counts. The conclusion is the actual R1 charge, not an assumed charge. -/
theorem charge_ge_of_small_root_counts
    (ε : ℝ) (hε : 0<ε) (K : ℕ) (hK : 1≤K) (hεK : 2≤ε*(K:ℝ))
    (x : V) (T : Finset V) (p : ℕ)
    (hT : T⊆G.neighborFinset x) (hpos : 0<T.card)
    (hpartition : T.card+p+1=G.degree x)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hxsmall : (G.degree x:ℝ)≤ε*(G.maxDegree:ℝ)/2)
    (hlarge : 2*(K+2)^4≤G.degree x)
    (hsource : ∀u∈T,G.maxDegree≤G.degree u+p)
    (hhigh : ∀u∈G.neighborFinset x,
      G.maxDegree≤highCount G ((1-ε)*(G.maxDegree:ℝ)) u+T.card)
    (hbudget : (∑u∈T,lowCount G ((1-ε)*(G.maxDegree:ℝ)) u)≤(K+2)*G.degree x) :
    (1-ε)*(G.maxDegree:ℝ)≤R1Charge G ((1-ε)*(G.maxDegree:ℝ)) x := by
  let q := (1-ε)*(G.maxDegree:ℝ)
  let d : ℝ := G.degree x
  let a : ℝ := T.card
  let B : ℝ := ((K:ℝ)+2)*d
  have hd : 0<d := by dsimp [d];exact_mod_cast (show 0<G.degree x by omega)
  have ha : 0<a := by dsimp [a];exact_mod_cast hpos
  have had : a≤d := by dsimp [a,d];exact_mod_cast (show T.card≤G.degree x by omega)
  have hB : 0<B := by dsimp [B];positivity
  have hpartitionR : a+(p:ℝ)+1=d := by dsimp [a,d];exact_mod_cast hpartition
  have hDpos : (0:ℝ)<(G.maxDegree:ℝ) := by
    have hh : 0<G.degree x := by omega
    exact_mod_cast hh.trans_le (G.degree_le_maxDegree x)
  have hepsD : 0<ε*(G.maxDegree:ℝ) := mul_pos hε hDpos
  have hgap : (G.maxDegree:ℝ)-q=ε*(G.maxDegree:ℝ) := by dsimp [q];ring
  have hhighq : ∀u∈G.neighborFinset x,q<(highCount G q u:ℝ) := by
    intro u hu
    have hh : (G.maxDegree:ℝ)≤(highCount G q u:ℝ)+a := by
      dsimp [a];exact_mod_cast hhigh u hu
    change d≤_ at hxsmall
    linarith
  have hdonAll : ∀u∈G.neighborFinset x,ε*(G.maxDegree:ℝ)/a≤donation G q u := by
    intro u hu
    have hh := donation_ge_of_high_neighbour_budget q
      ((mem_neighborFinset G x u).mp hu) hx T.card hpos (hhigh u hu) (hhighq u hu)
    simpa only [hgap] using hh
  have hdonT : ∀u∈T,(ε*(G.maxDegree:ℝ)/2)/(lowCount G q u:ℝ)≤donation G q u := by
    intro u hu
    have hsu := hsource u hu
    have hsuR : (G.maxDegree:ℝ)≤(G.degree u:ℝ)+(p:ℝ) := by exact_mod_cast hsu
    have hnum : ε*(G.maxDegree:ℝ)/2≤(G.degree u:ℝ)-q := by
      change d≤_ at hxsmall
      linarith
    have hsourceR : q<(G.degree u:ℝ) := by linarith
    rw [donation,if_pos hsourceR]
    exact div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)
  have hsumB : (∑u∈T,(lowCount G q u:ℝ))≤B := by
    dsimp [B,d,q]
    exact_mod_cast hbudget
  have hc := reciprocal_lowCount_sum_ge q hx T hT hpos B hB hsumB
  have hsumT : (ε*(G.maxDegree:ℝ)/2)*(a^2/B)≤∑u∈T,donation G q u := by
    have hs := sum_le_sum hdonT
    have he : (∑u∈T,(ε*(G.maxDegree:ℝ)/2)/(lowCount G q u:ℝ))=
        (ε*(G.maxDegree:ℝ)/2)*(∑u∈T,1/(lowCount G q u:ℝ)) := by
      simp only [div_eq_mul_inv,one_mul,mul_sum]
    rw [he] at hs
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans hs
  have hsumOther : (∑_u∈(G.neighborFinset x)\T,ε*(G.maxDegree:ℝ)/a)≤
      ∑u∈(G.neighborFinset x)\T,donation G q u :=
    sum_le_sum (fun u hu => hdonAll u (mem_sdiff.mp hu).1)
  rw [sum_const,nsmul_eq_mul] at hsumOther
  have hotherCard : ((G.neighborFinset x)\T).card=p+1 := by
    rw [card_sdiff_of_subset hT,card_neighborFinset_eq_degree]
    omega
  rw [hotherCard] at hsumOther
  have htotal : (∑u∈G.neighborFinset x,donation G q u)=
      (∑u∈T,donation G q u)+(∑u∈(G.neighborFinset x)\T,donation G q u) := by
    have hs := sum_sdiff (f:=fun u => donation G q u) hT
    linarith only [hs]
  have hn := small_root_fraction_bound_nat hK ha had hlarge
  have hnScale := mul_le_mul_of_nonneg_left hn (show 0≤ε*(G.maxDegree:ℝ) by positivity)
  have htarget : q≤d+(ε*(G.maxDegree:ℝ)/2)*(a^2/B)+
      ((p+1:ℕ):ℝ)*(ε*(G.maxDegree:ℝ)/a) := by
    have hfac : d+(ε*(G.maxDegree:ℝ)/2)*(a^2/B)+
        ((p+1:ℕ):ℝ)*(ε*(G.maxDegree:ℝ)/a)=
        d+ε*(G.maxDegree:ℝ)*(a^2/(2*((K:ℝ)+2)*d)+d/a-1) := by
      have hpR : ((p+1:ℕ):ℝ)=d-a := by push_cast;linarith
      rw [hpR]
      dsimp [B]
      have hKpos : (0:ℝ)<(K:ℝ)+2 := by positivity
      field_simp [ne_of_gt ha,ne_of_gt hd,ne_of_gt hKpos]
      ring
    rw [hfac]
    have hpay := mul_le_mul_of_nonneg_right hεK (Nat.cast_nonneg G.maxDegree : (0:ℝ)≤_)
    dsimp [q]
    linarith
  rw [low_charge_formula G q x hx,htotal]
  change q≤_
  linarith

end OverfullWork.CaoChenDischarging
