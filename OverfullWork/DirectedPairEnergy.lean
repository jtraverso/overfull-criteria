module

public import OverfullWork.DirectedRegularPairs

@[expose] public section


/-! Weighted directed pair energy for the standard energy-increment
proof underlying KOT Lemma 11. Ordered pairs retain their direction;
empty cells have zero mass and require no division by a positive size. -/
namespace OverfullWork.DirectedPairEnergy
open Finset DirectedRobustExpansion DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 8000000

noncomputable def mass (A B : Finset V) : ℝ := (A.card:ℝ)*(B.card:ℝ)
noncomputable def pairEnergy (D : Digraph V) (A B : Finset V) : ℝ :=
  mass A B*(density D A B)^2

theorem density_nonneg (D : Digraph V) (A B : Finset V) : 0 ≤ density D A B := by
  unfold density
  positivity

theorem density_le_one (D : Digraph V) (A B : Finset V) : density D A B ≤ 1 := by
  apply div_le_one_of_le₀
  · exact_mod_cast DirectedArcSelection.incidences_le D A B
  · positivity

theorem density_mass (D : Digraph V) (A B : Finset V) :
    mass A B*density D A B=(incidences D A B:ℝ) := by
  have hNonneg : 0 ≤ mass A B := by unfold mass;positivity
  have hBound : (incidences D A B:ℝ) ≤ mass A B := by
    unfold mass
    exact_mod_cast DirectedArcSelection.incidences_le D A B
  by_cases hZero : mass A B=0
  · have hE : (incidences D A B:ℝ)=0 := by
      have hh := Nat.cast_nonneg (incidences D A B) (α:=ℝ)
      rw [hZero] at hBound
      linarith
    simp only [hZero,zero_mul,hE]
  · exact mul_div_cancel₀ _ hZero

theorem pairEnergy_nonneg (D : Digraph V) (A B : Finset V) : 0 ≤ pairEnergy D A B := by
  unfold pairEnergy mass
  positivity

theorem pairEnergy_le_mass (D : Digraph V) (A B : Finset V) : pairEnergy D A B ≤ mass A B := by
  have hd0 := density_nonneg D A B
  have hd1 := density_le_one D A B
  have hSq : (density D A B)^2 ≤ 1 := by nlinarith only [hd0,hd1]
  have hMass : 0 ≤ mass A B := by unfold mass;positivity
  simpa only [pairEnergy,mul_one] using mul_le_mul_of_nonneg_left hSq hMass

theorem weighted_variance_identity {I : Type*} [Fintype I]
    (w d : I → ℝ) (μ : ℝ)
    (hBalance : ∑ i,w i*d i=(∑ i,w i)*μ) :
    (∑ i,w i*(d i-μ)^2)=(∑ i,w i*(d i)^2)-(∑ i,w i)*μ^2 := by
  have hExpand : ∀ i,w i*(d i-μ)^2=w i*(d i)^2-2*μ*(w i*d i)+μ^2*w i := by
    intro i;ring
  simp_rw [hExpand]
  rw [sum_add_distrib,sum_sub_distrib,←mul_sum,←mul_sum,hBalance]
  ring

theorem weighted_energy_gain_at {I : Type*} [Fintype I]
    (w d : I → ℝ) (μ : ℝ) (hW : ∀ i,0 ≤ w i)
    (hBalance : ∑ i,w i*d i=(∑ i,w i)*μ) (j : I) :
    (∑ i,w i)*μ^2+w j*(d j-μ)^2 ≤ ∑ i,w i*(d i)^2 := by
  have hVar := weighted_variance_identity w d μ hBalance
  have hSingle := single_le_sum (s:=univ)
    (f:=fun i => w i*(d i-μ)^2) (fun i _ => mul_nonneg (hW i) (sq_nonneg _)) (mem_univ j)
  linarith only [hVar,hSingle]

theorem weighted_energy_mono {I : Type*} [Fintype I]
    (w d : I → ℝ) (μ : ℝ) (hW : ∀ i,0 ≤ w i)
    (hBalance : ∑ i,w i*d i=(∑ i,w i)*μ) :
    (∑ i,w i)*μ^2 ≤ ∑ i,w i*(d i)^2 := by
  have hh := weighted_variance_identity w d μ hBalance
  have hNonneg := sum_nonneg (s:=univ) (fun i _ => mul_nonneg (hW i) (sq_nonneg (d i-μ)))
  linarith only [hh,hNonneg]

end OverfullWork.DirectedPairEnergy
