module

public import OverfullWork.DirectedPairEnergy
public import Mathlib.Order.Partition.Finpartition

@[expose] public section


/-! Bounded weighted energy on ONE common directed partition.
Diagonal ordered pairs are included; the value lies in [0,1], also
for the empty host. This is a potential for common refinement, not
an assertion of a final regular partition or Hamiltonicity. -/
namespace OverfullWork.DirectedPairEnergy
open Finset Finpartition DirectedRobustExpansion DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 8000000

noncomputable def partitionEnergy (D : Digraph V) (P : Finpartition (univ : Finset V)) : ℝ :=
  (∑ A∈P.parts,∑ B∈P.parts,pairEnergy D A B)/(Fintype.card V:ℝ)^2

theorem partition_mass_sum (P : Finpartition (univ : Finset V)) :
    (∑ A∈P.parts,∑ B∈P.parts,mass A B)=(Fintype.card V:ℝ)^2 := by
  have hCard : (∑ A∈P.parts,(A.card:ℝ))=(Fintype.card V:ℝ) := by
    exact_mod_cast P.sum_card_parts
  simp_rw [mass,←mul_sum]
  rw [←sum_mul,hCard]
  ring

theorem partitionEnergy_nonneg (D : Digraph V) (P : Finpartition (univ : Finset V)) :
    0 ≤ partitionEnergy D P := by
  apply div_nonneg
  · exact sum_nonneg (fun A _ => sum_nonneg (fun B _ => pairEnergy_nonneg D A B))
  · positivity

theorem partitionEnergy_le_one (D : Digraph V) (P : Finpartition (univ : Finset V)) :
    partitionEnergy D P ≤ 1 := by
  apply div_le_one_of_le₀
  · calc
      (∑ A∈P.parts,∑ B∈P.parts,pairEnergy D A B)
          ≤ ∑ A∈P.parts,∑ B∈P.parts,mass A B :=
        sum_le_sum (fun A _ => sum_le_sum (fun B _ => pairEnergy_le_mass D A B))
      _ = _ := partition_mass_sum P
  · positivity

end OverfullWork.DirectedPairEnergy
