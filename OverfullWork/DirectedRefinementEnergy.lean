module

public import OverfullWork.DirectedPairEnergy
public import Mathlib.Order.Partition.Finpartition

@[expose] public section


/-! Weighted directed energy under arbitrary genuine rectangular
refinements. This lets simultaneous common refinement preserve local
gains, rather than slicing an arbitrary final bipartite partition. -/
namespace OverfullWork.DirectedPairEnergy
open Finset Finpartition DirectedRobustExpansion DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 12000000

theorem sum_partition {M : Type*} [AddCommMonoid M] {A : Finset V}
    (P : Finpartition A) (f : V → M) : (∑ U∈P.parts,∑ u∈U,f u)=∑ u∈A,f u := by
  have hh := Finset.sum_biUnion (f:=f) P.disjoint
  simpa only [id_eq,P.biUnion_parts] using hh.symm

theorem incidences_source_partition (D : Digraph V) {A : Finset V}
    (P : Finpartition A) (B : Finset V) :
    (∑ U∈P.parts,incidences D U B)=incidences D A B := by
  unfold incidences
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  simp only [inNeighbours,card_filter]
  exact sum_partition P _

theorem incidences_target_partition (D : Digraph V) (A : Finset V) {B : Finset V}
    (Q : Finpartition B) :
    (∑ W∈Q.parts,incidences D A W)=incidences D A B := by
  unfold incidences
  exact sum_partition Q _

theorem incidences_rect_partition (D : Digraph V) {A B : Finset V}
    (P : Finpartition A) (Q : Finpartition B) :
    (∑ U∈P.parts,∑ W∈Q.parts,incidences D U W)=incidences D A B := by
  rw [sum_comm]
  simp_rw [incidences_source_partition D P]
  exact incidences_target_partition D A Q

theorem rect_mass_sum {A B : Finset V} (P : Finpartition A) (Q : Finpartition B) :
    (∑ ij : P.parts × Q.parts,mass ij.1.val ij.2.val)=mass A B := by
  have hP : (∑ U : P.parts,(U.val.card:ℝ))=(A.card:ℝ) := by
    rw [Finset.sum_coe_sort P.parts (fun U => (U.card:ℝ))]
    exact_mod_cast P.sum_card_parts
  have hQ : (∑ W : Q.parts,(W.val.card:ℝ))=(B.card:ℝ) := by
    rw [Finset.sum_coe_sort Q.parts (fun W => (W.card:ℝ))]
    exact_mod_cast Q.sum_card_parts
  simp only [Fintype.sum_prod_type,sum_coe_sort,mass]
  simp_rw [←mul_sum]
  rw [←sum_mul,hP,hQ]

theorem rect_mass_density_sum (D : Digraph V) {A B : Finset V}
    (P : Finpartition A) (Q : Finpartition B) :
    (∑ ij : P.parts × Q.parts,mass ij.1.val ij.2.val*density D ij.1.val ij.2.val)=
      (incidences D A B:ℝ) := by
  simp only [density_mass,Fintype.sum_prod_type,sum_coe_sort]
  have hCount : (∑ U : P.parts,∑ W : Q.parts,incidences D U.val W.val)=incidences D A B := by
    rw [Finset.sum_coe_sort P.parts (fun U => ∑ W : Q.parts,incidences D U W.val)]
    have hConvert : ∀ U : Finset V,(∑ W : Q.parts,incidences D U W.val)=
        ∑ W∈Q.parts,incidences D U W := fun U => Finset.sum_coe_sort Q.parts _
    simp_rw [hConvert]
    exact incidences_rect_partition D P Q
  exact_mod_cast hCount

theorem rect_energy_mono (D : Digraph V) {A B : Finset V}
    (P : Finpartition A) (Q : Finpartition B) :
    pairEnergy D A B ≤ ∑ ij : P.parts × Q.parts,pairEnergy D ij.1.val ij.2.val := by
  let w := fun ij : P.parts × Q.parts => mass ij.1.val ij.2.val
  let d := fun ij : P.parts × Q.parts => density D ij.1.val ij.2.val
  have hMass : (∑ ij,w ij)=mass A B := rect_mass_sum P Q
  have hBalance : (∑ ij,w ij*d ij)=(∑ ij,w ij)*density D A B := by
    rw [hMass,density_mass]
    exact rect_mass_density_sum D P Q
  have hh := weighted_energy_mono w d (density D A B)
    (fun ij => by unfold w mass;positivity) hBalance
  rw [hMass] at hh
  exact hh

theorem rect_energy_gain_at (D : Digraph V) {A B : Finset V}
    (P : Finpartition A) (Q : Finpartition B) (X : P.parts) (Y : Q.parts) :
    pairEnergy D A B+mass X.val Y.val*(density D X.val Y.val-density D A B)^2 ≤
      ∑ ij : P.parts × Q.parts,pairEnergy D ij.1.val ij.2.val := by
  let w := fun ij : P.parts × Q.parts => mass ij.1.val ij.2.val
  let d := fun ij : P.parts × Q.parts => density D ij.1.val ij.2.val
  have hMass : (∑ ij,w ij)=mass A B := rect_mass_sum P Q
  have hBalance : (∑ ij,w ij*d ij)=(∑ ij,w ij)*density D A B := by
    rw [hMass,density_mass]
    exact rect_mass_density_sum D P Q
  have hh := weighted_energy_gain_at w d (density D A B)
    (fun ij => by unfold w mass;positivity) hBalance (X,Y)
  rw [hMass] at hh
  exact hh

end OverfullWork.DirectedPairEnergy
