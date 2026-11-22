module

public import OverfullWork.DirectedCommonWitnessRefinement

@[expose] public section


/-! The variance contribution of a union of atoms survives further
refinement. Summing these contributions gives the directed increment. -/
namespace OverfullWork.DirectedPairEnergy
open Finset Finpartition DirectedRegularPairs DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 14000000

theorem rect_variance_lower (D : Digraph V) {A B : Finset V}
    (P : Finpartition A) (Q : Finpartition B) (c : ℝ) :
    mass A B*(density D A B-c)^2 ≤
      ∑ ij : P.parts × Q.parts,
        mass ij.1.val ij.2.val*(density D ij.1.val ij.2.val-c)^2 := by
  let w := fun ij : P.parts × Q.parts => mass ij.1.val ij.2.val
  let d := fun ij : P.parts × Q.parts => density D ij.1.val ij.2.val
  have hw : (∑ i,w i)=mass A B := rect_mass_sum P Q
  have hb : (∑ i,w i*d i)=mass A B*density D A B := by
    rw [density_mass]
    exact rect_mass_density_sum D P Q
  have he : pairEnergy D A B ≤ ∑ i,w i*(d i)^2 := rect_energy_mono D P Q
  change mass A B*(density D A B-c)^2 ≤ ∑ i,w i*(d i-c)^2
  have hExpand : ∀ i,w i*(d i-c)^2=w i*(d i)^2-2*c*(w i*d i)+c^2*w i := by
    intro i;ring
  simp_rw [hExpand]
  rw [sum_add_distrib,sum_sub_distrib,←mul_sum,←mul_sum,hb,hw]
  unfold pairEnergy at he
  nlinarith only [he]

private theorem variance_sum_parts (D : Digraph V) (S T : Finset (Finset V)) (c : ℝ) :
    (∑ ij : S × T,mass ij.1.val ij.2.val*(density D ij.1.val ij.2.val-c)^2) =
      ∑ A ∈ S, ∑ B ∈ T,mass A B*(density D A B-c)^2 := by
  rw [Fintype.sum_prod_type,Finset.sum_coe_sort S
    (fun A => ∑ B : T,mass A B.val*(density D A B.val-c)^2)]
  apply sum_congr rfl
  intro A _
  exact Finset.sum_coe_sort T (fun B => mass A B*(density D A B-c)^2)

private theorem subfamily_partition {A : Finset V} (P : Finpartition A)
    (S : Finset (Finset V)) (hS : S ⊆ P.parts) :
    ∃ Q : Finpartition (S.biUnion id), Q.parts=S := by
  have hd : (↑S : Set (Finset V)).PairwiseDisjoint id :=
    fun U hU W hW hn => P.disjoint (hS hU) (hS hW) hn
  have hbot : (⊥ : Finset V) ∉ S := fun h => P.ne_bot (hS h) rfl
  have he : S.sup id=S.biUnion id := sup_eq_biUnion _ _
  let Q := (Finpartition.ofPairwiseDisjoint S hd).copy he
  refine ⟨Q,?_⟩
  change S.erase ⊥=S
  exact erase_eq_of_notMem hbot

theorem rect_energy_gain_of_unions (D : Digraph V) {A B : Finset V}
    (P : Finpartition A) (Q : Finpartition B)
    (S T : Finset (Finset V)) (hS : S ⊆ P.parts) (hT : T ⊆ Q.parts) :
    let X := S.biUnion id
    let Y := T.biUnion id
    pairEnergy D A B+mass X Y*(density D X Y-density D A B)^2 ≤
      ∑ ij : P.parts × Q.parts,pairEnergy D ij.1.val ij.2.val := by
  dsimp only
  obtain ⟨P',hP'⟩ := subfamily_partition P S hS
  obtain ⟨Q',hQ'⟩ := subfamily_partition Q T hT
  let c := density D A B
  let f := fun U W => mass U W*(density D U W-c)^2
  have hLocal := rect_variance_lower D P' Q' c
  rw [variance_sum_parts,hP',hQ'] at hLocal
  have hle : (∑ U ∈ S,∑ W ∈ T,f U W) ≤ ∑ U ∈ P.parts,∑ W ∈ Q.parts,f U W := by
    apply le_trans (sum_le_sum (fun U _ => sum_le_sum_of_subset_of_nonneg hT
      (fun W _ _ => by unfold f mass;positivity)))
    exact sum_le_sum_of_subset_of_nonneg hS (fun U _ _ =>
      sum_nonneg (fun W _ => by unfold f mass;positivity))
  let w := fun ij : P.parts × Q.parts => mass ij.1.val ij.2.val
  let d := fun ij : P.parts × Q.parts => density D ij.1.val ij.2.val
  have hm : (∑ ij,w ij)=mass A B := rect_mass_sum P Q
  have hb : (∑ ij,w ij*d ij)=(∑ ij,w ij)*c := by
    rw [hm]
    exact (rect_mass_density_sum D P Q).trans (density_mass D A B).symm
  have hv := weighted_variance_identity w d c hb
  rw [hm] at hv
  change (∑ ij : P.parts × Q.parts,f ij.1.val ij.2.val) =
    (∑ ij : P.parts × Q.parts,pairEnergy D ij.1.val ij.2.val)-pairEnergy D A B at hv
  rw [variance_sum_parts] at hv
  linarith only [hLocal,hle,hv]

end OverfullWork.DirectedPairEnergy
