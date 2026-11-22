module

public import OverfullWork.WeightedColouringAudit
public import OverfullWork.WeightedComponents
public import OverfullWork.WeightedMissingBudget

@[expose] public section


/-! # Weighted occupied-mass bounds for a residue palette

Existence of a weighted recolouring is not asserted here. The bounds
apply to an actual colouring once its pairwise load spread is proved.
-/
namespace OverfullWork.Gate8J2C
open Finset

theorem load_three_mul_le (q u D S : ℕ) (hu : 0<u) (hq : q=3*u)
    (load : Fin q → ℕ) (hspread : ∀ i j,load i≤load j+2*S)
    (htotal : (∑ j,load j)≤u*D) (i : Fin q) : 3*load i≤D+6*S := by
  have hsum : q*load i≤(∑ j,load j)+q*(2*S) := by
    have hh:=sum_le_sum (s:=univ) (fun j _ => hspread i j)
    simpa only [sum_const,sum_add_distrib,card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_id] using hh
  subst q
  have hscaled : u*(3*load i)≤u*(D+6*S):=by nlinarith only [hsum,htotal]
  exact Nat.le_of_mul_le_mul_left hscaled hu

/-- There is no additional rounding error beyond floor(D/3). -/
theorem load_le_third_floor_add (q u D S : ℕ) (hu : 0<u) (hq : q=3*u)
    (load : Fin q → ℕ) (hspread : ∀ i j,load i≤load j+2*S)
    (htotal : (∑ j,load j)≤u*D) (i : Fin q) : load i≤D/3+2*S := by
  have hh:=load_three_mul_le q u D S hu hq load hspread htotal i
  have hfloor:=Nat.lt_mul_div_succ D (show 0<3 by decide)
  omega

end OverfullWork.Gate8J2C

namespace SimpleGraph.MultiGraph.EdgeColoring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {H : MultiGraph V} {k : ℕ}

theorem sum_weightedLoad (C : H.EdgeColoring k) (w : V → ℕ) :
    (∑ i,C.weightedLoad w i)=∑ v,w v*H.degree v := by
  unfold weightedLoad
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [←mul_sum,C.sum_colour_degree]

theorem sum_coveredWeight (C : H.EdgeColoring k) (T : Finset V) (w : V → ℕ) :
    (∑ i,C.coveredWeight T w i)=∑ v∈T,w v*H.degree v := by
  unfold coveredWeight
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [←mul_sum,C.sum_colour_degree]

theorem sum_coveredWeight_le (C : H.EdgeColoring k) (T : Finset V) (w : V → ℕ)
    (u D : ℕ) (hdeg : ∀ v∈T,H.degree v≤u) (hweight : (∑ v∈T,w v)≤D) :
    (∑ i,C.coveredWeight T w i)≤u*D := by
  rw [C.sum_coveredWeight]
  calc
    _ ≤ ∑ v∈T,w v*u:=sum_le_sum (fun v hv => Nat.mul_le_mul_left (w v) (hdeg v hv))
    _ = u*(∑ v∈T,w v):=by rw [←sum_mul];ring
    _ ≤ _:=Nat.mul_le_mul_left u hweight

/-- A globally supported weighted load may be bounded by its support T. -/
theorem sum_weightedLoad_le_of_support (C : H.EdgeColoring k) (T : Finset V) (w : V → ℕ)
    (u D : ℕ) (hdeg : ∀ v∈T,H.degree v≤u) (hzero : ∀ v,v∉T → H.degree v=0)
    (hweight : (∑ v∈T,w v)≤D) : (∑ i,C.weightedLoad w i)≤u*D := by
  rw [C.sum_weightedLoad]
  have he : (∑ v,w v*H.degree v)=∑ v∈T,w v*H.degree v := by
    symm
    apply sum_subset (subset_univ T)
    intro v _ hv
    rw [hzero v hv,Nat.mul_zero]
  rw [he]
  have hh:=C.sum_coveredWeight_le T w u D hdeg hweight
  rwa [C.sum_coveredWeight] at hh

/-- The generic subset version is the Hall budget used on one side. -/
theorem coveredWeight_le_third_floor_add {c t : ℕ}
    (C : H.EdgeColoring (3*c*t)) (T : Finset V) (w : V → ℕ) (D S : ℕ)
    (hc : 0<c) (ht : 0<t) (hdeg : ∀ v∈T,H.degree v≤c*t)
    (hweight : (∑ v∈T,w v)≤D)
    (hspread : ∀ i j,C.coveredWeight T w i≤C.coveredWeight T w j+2*S) :
    ∀ i,C.coveredWeight T w i≤D/3+2*S := by
  have hu : 0<c*t:=Nat.mul_pos hc ht
  exact OverfullWork.Gate8J2C.load_le_third_floor_add (3*c*t) (c*t) D S hu (by ring)
    (C.coveredWeight T w) hspread (C.sum_coveredWeight_le T w (c*t) D hdeg hweight)

theorem weightedLoad_le_third_floor_add_of_support {c t : ℕ}
    (C : H.EdgeColoring (3*c*t)) (T : Finset V) (w : V → ℕ) (D S : ℕ)
    (hc : 0<c) (ht : 0<t) (hdeg : ∀ v∈T,H.degree v≤c*t)
    (hzero : ∀ v,v∉T → H.degree v=0) (hweight : (∑ v∈T,w v)≤D)
    (hspread : ∀ i j,C.weightedLoad w i≤C.weightedLoad w j+2*S) :
    ∀ i,C.weightedLoad w i≤D/3+2*S := by
  have hu : 0<c*t:=Nat.mul_pos hc ht
  exact OverfullWork.Gate8J2C.load_le_third_floor_add (3*c*t) (c*t) D S hu (by ring)
    (C.weightedLoad w) hspread (C.sum_weightedLoad_le_of_support T w (c*t) D hdeg hzero hweight)

/-- Whole-graph form when the weights already have total mass at most D. -/
theorem weightedLoad_le_third_floor_add {c t : ℕ}
    (C : H.EdgeColoring (3*c*t)) (w : V → ℕ) (D S : ℕ)
    (hc : 0<c) (ht : 0<t) (hdeg : ∀ v,H.degree v≤c*t)
    (hweight : (∑ v,w v)≤D)
    (hspread : ∀ i j,C.weightedLoad w i≤C.weightedLoad w j+2*S) :
    ∀ i,C.weightedLoad w i≤D/3+2*S := by
  exact C.weightedLoad_le_third_floor_add_of_support univ w D S hc ht
    (fun v _ => hdeg v) (fun v hv => False.elim (hv (mem_univ v))) hweight hspread

end SimpleGraph.MultiGraph.EdgeColoring
