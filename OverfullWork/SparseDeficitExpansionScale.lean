module

public import OverfullWork.SparseDeficitExpansion

@[expose] public section


/-! # A nonvacuous integer scale for sparse-deficit robust expansion

The degree-deficit bound remains an explicit hypothesis. The chosen
threshold is positive and its admissible set-size interval is nonempty;
no critical average-degree or edge-colouring theorem is assumed.
-/
namespace OverfullWork.RobustExpansion
open SimpleGraph Finset SparseDeficitCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 2000000

/-- Explicit scales with enough room for the robust-neighbour threshold
and for a nonempty interval of admissible set sizes. -/
theorem sparse_deficit_integer_scales (n q : ℕ) (hq : 2≤q)
    (hn : 4096*q^2≤n) :
    let a := n/(8*q)
    let k := n/(4096*q^2)
    k≤a ∧ 0<2*k+1 ∧ 2*k+1≤a ∧
      4*(2*k+1)*n≤a^2 ∧ 2*(a+k)≤n := by
  let a := n/(8*q)
  let k := n/(4096*q^2)
  change k≤a ∧ 0<2*k+1 ∧ 2*k+1≤a ∧
    4*(2*k+1)*n≤a^2 ∧ 2*(a+k)≤n
  have hqpos : 0<q := by omega
  have hdpos : 0<4096*q^2 := by positivity
  have hepos : 0<8*q := by positivity
  have hden : 8*q≤4096*q^2 := by nlinarith only [hq]
  have haone : 1≤a := by
    apply (Nat.le_div_iff_mul_le hepos).mpr
    simpa only [Nat.one_mul] using hden.trans hn
  have hkone : 1≤k := by
    apply (Nat.le_div_iff_mul_le hdpos).mpr
    simpa only [Nat.one_mul] using hn
  have hafloor : 8*q*a≤n := Nat.mul_div_le n (8*q)
  have hkfloor : 4096*q^2*k≤n := Nat.mul_div_le n (4096*q^2)
  have hatop : n<8*q*(a+1) := Nat.lt_mul_div_succ n hepos
  have haweak : n≤16*q*a := by
    have hh := Nat.mul_le_mul_left (8*q) haone
    nlinarith only [hatop,hh]
  have hkstrong : 256*q*k≤a := by
    apply Nat.le_of_mul_le_mul_left (c:=16*q) ?_ (by positivity)
    nlinarith only [hkfloor,haweak]
  have hthree : 3*k≤a := by
    have hp : 3≤256*q := by omega
    exact (Nat.mul_le_mul_right k hp).trans hkstrong
  have hrthree : 2*k+1≤3*k := by omega
  have hka : k≤a := by omega
  have hr : 2*k+1≤a := hrthree.trans hthree
  have hsquare : n^2≤256*q^2*a^2 := by
    have hh := Nat.pow_le_pow_left haweak 2
    nlinarith only [hh]
  have hkn : 16*k*n≤a^2 := by
    have hh := Nat.mul_le_mul_right n hkfloor
    apply Nat.le_of_mul_le_mul_left (c:=256*q^2) ?_ (by positivity)
    nlinarith only [hh,hsquare]
  have hscale : 4*(2*k+1)*n≤a^2 := by
    have hh := Nat.mul_le_mul_right (4*n) hrthree
    nlinarith only [hh,hkn]
  have hfour : 4*a≤n := by
    have hp : 4≤8*q := by omega
    exact (Nat.mul_le_mul_right a hp).trans hafloor
  exact ⟨hka,by omega,hr,hscale,by omega⟩

/-- This robust-expansion conclusion has a positive threshold and a
nonempty set-size interval. The mass and density assumptions are explicit. -/
theorem isRobustAt_of_nonvacuous_deficit_scale (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (hq : 2≤q) (hn : 4096*q^2≤Fintype.card V)
    (hmass : totalDeficit G G.maxDegree<
      (Fintype.card V/(8*q)+1)*(Fintype.card V/(4096*q^2)+1))
    (hdense : Fintype.card V+5*(Fintype.card V/(8*q))≤2*G.maxDegree) :
    let a := Fintype.card V/(8*q)
    let k := Fintype.card V/(4096*q^2)
    0<k+1 ∧ 2*(a+k)≤Fintype.card V ∧ IsRobustAt G (k+1) (a+k) := by
  let a := Fintype.card V/(8*q)
  let k := Fintype.card V/(4096*q^2)
  change 0<k+1 ∧ 2*(a+k)≤Fintype.card V ∧ IsRobustAt G (k+1) (a+k)
  obtain ⟨hka,hrpos,hra,hscale,hrange⟩ := sparse_deficit_integer_scales (Fintype.card V) q hq hn
  change k≤a at hka
  change 0<2*k+1 at hrpos
  change 2*k+1≤a at hra
  change 4*(2*k+1)*Fintype.card V≤a^2 at hscale
  change 2*(a+k)≤Fintype.card V at hrange
  have hmass' : totalDeficit G G.maxDegree<(a+1)*(k+1) := hmass
  have hdense' : Fintype.card V+5*a≤2*G.maxDegree := hdense
  have hrobust := isRobustAt_of_deficit_mass G a k a (2*k+1) (k+1) a hmass'
    (by omega) hrpos hra hra (by simpa only [pow_two] using hscale) (by omega)
  exact ⟨by omega,hrange,hrobust⟩

end OverfullWork.RobustExpansion
