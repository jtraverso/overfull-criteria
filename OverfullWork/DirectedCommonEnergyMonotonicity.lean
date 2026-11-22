module

public import OverfullWork.DirectedPartitionEnergy
public import OverfullWork.DirectedRefinementEnergy

@[expose] public section


/-! Monotonicity of the bounded directed energy when ONE common
partition is refined in every cell. This is the common-refinement
interface needed to accumulate local irregularity gains. -/
namespace OverfullWork.DirectedPairEnergy
open Finset Finpartition
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 12000000

theorem sum_parts_bind {A : Finset V} (P : Finpartition A)
    (Q : ∀ U∈P.parts,Finpartition U) (F : Finset V → ℝ) :
    (∑ U∈(P.bind Q).parts,F U)=∑ U : P.parts,∑ C∈(Q U.val U.property).parts,F C := by
  have hDis : (↑P.parts.attach : Set P.parts).PairwiseDisjoint
      (fun U => (Q U.val U.property).parts) := by
    intro U hU W hW hUW
    apply Finset.disjoint_left.mpr
    intro C hCU hCW
    have hNe : U.val≠W.val := fun hh => hUW (Subtype.ext hh)
    apply (Q U.val U.property).ne_bot hCU
    apply eq_bot_iff.mpr
    exact (le_inf ((Q U.val U.property).le hCU) ((Q W.val W.property).le hCW)).trans
      (P.disjoint U.property W.property hNe).le_bot
  rw [Finpartition.bind_parts,sum_biUnion hDis,Finset.attach_eq_univ]

theorem partitionEnergy_bind (D : Digraph V) (P : Finpartition (univ : Finset V))
    (Q : ∀ U∈P.parts,Finpartition U) :
    partitionEnergy D (P.bind Q)=
      (∑ U : P.parts,∑ W : P.parts,
        ∑ ij : (Q U.val U.property).parts × (Q W.val W.property).parts,
          pairEnergy D ij.1.val ij.2.val)/(Fintype.card V:ℝ)^2 := by
  unfold partitionEnergy
  congr 1
  rw [sum_parts_bind]
  apply sum_congr rfl
  intro U hU
  simp_rw [sum_parts_bind]
  rw [sum_comm]
  apply sum_congr rfl
  intro W hW
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_coe_sort (Q U.val U.property).parts
    (fun C => ∑ E : (Q W.val W.property).parts,pairEnergy D C E.val)]
  apply sum_congr rfl
  intro C hC
  exact (Finset.sum_coe_sort (Q W.val W.property).parts (fun E => pairEnergy D C E)).symm

theorem partitionEnergy_bind_mono (D : Digraph V) (P : Finpartition (univ : Finset V))
    (Q : ∀ U∈P.parts,Finpartition U) :
    partitionEnergy D P ≤ partitionEnergy D (P.bind Q) := by
  have hh : (∑ U : P.parts,∑ W : P.parts,pairEnergy D U.val W.val) ≤
      ∑ U : P.parts,∑ W : P.parts,
        ∑ ij : (Q U.val U.property).parts × (Q W.val W.property).parts,
          pairEnergy D ij.1.val ij.2.val := by
    apply sum_le_sum
    intro U hU
    apply sum_le_sum
    intro W hW
    exact rect_energy_mono D (Q U.val U.property) (Q W.val W.property)
  rw [partitionEnergy_bind]
  unfold partitionEnergy
  have hCoarse : (∑ U : P.parts,∑ W : P.parts,pairEnergy D U.val W.val)=
      ∑ U∈P.parts,∑ W∈P.parts,pairEnergy D U W := by
    rw [Finset.sum_coe_sort P.parts (fun U => ∑ W : P.parts,pairEnergy D U W.val)]
    apply sum_congr rfl
    intro U hU
    exact Finset.sum_coe_sort P.parts (fun W => pairEnergy D U W)
  rw [hCoarse] at hh
  exact div_le_div_of_nonneg_right hh (sq_nonneg (Fintype.card V:ℝ))

end OverfullWork.DirectedPairEnergy
