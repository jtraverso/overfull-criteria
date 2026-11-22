module

public import OverfullWork.DirectedWitnessEnergyGain

@[expose] public section


namespace OverfullWork.DirectedPairEnergy
open Finset Finpartition DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 14000000

/-- Total normalized mass of irregular ordered rectangles. -/
noncomputable def irregularMass (D : Digraph V) (P : Finpartition (univ : Finset V))
    (ε : ℝ) : ℝ :=
  (∑ U : P.parts, ∑ W : P.parts,
    if IsUniform D ε U.val W.val then 0 else mass U.val W.val)/(Fintype.card V:ℝ)^2

theorem witnessRefinement_energy_increment (D : Digraph V)
    (P : Finpartition (univ : Finset V)) (ε : ℝ) (hε : 0 < ε) :
    partitionEnergy D P + ε^4*irregularMass D P ε ≤
      partitionEnergy D (witnessRefinement D P ε hε) := by
  let Q := fun U : Finset V => Finpartition.atomise U (witnessCuts D P ε hε U)
  let b := fun U W : P.parts =>
    if IsUniform D ε U.val W.val then 0 else mass U.val W.val
  have hLocal : ∀ U W : P.parts,
      pairEnergy D U.val W.val+ε^4*b U W ≤
        ∑ ij : (Q U.val).parts × (Q W.val).parts,pairEnergy D ij.1.val ij.2.val := by
    intro U W
    by_cases hReg : IsUniform D ε U.val W.val
    · simpa [b,hReg] using rect_energy_mono D (Q U.val) (Q W.val)
    let X := (pairWitness D ε hε U.val W.val).1
    let Y := (pairWitness D ε hε U.val W.val).2
    let S := (Q U.val).parts.filter (fun C => C⊆X ∧ C.Nonempty)
    let T := (Q W.val).parts.filter (fun C => C⊆Y ∧ C.Nonempty)
    have hX : S.biUnion id=X := outgoing_witness_recovered D P ε hε U.val W.val W.property
    have hY : T.biUnion id=Y := incoming_witness_recovered D P ε hε U.val W.val U.property
    have hg := rect_energy_gain_of_unions D (Q U.val) (Q W.val) S T
      (filter_subset _ _) (filter_subset _ _)
    dsimp only at hg
    rw [hX,hY] at hg
    obtain ⟨_,_,hx,hy,hgap,_⟩ := pairWitness_spec D ε hε U.val W.val hReg
    have hw : ε^2*mass U.val W.val ≤ mass X Y := by
      change (U.val.card:ℝ)*ε ≤ (X.card:ℝ) at hx
      change (W.val.card:ℝ)*ε ≤ (Y.card:ℝ) at hy
      have hh := mul_le_mul hx hy (by positivity) (by positivity)
      unfold mass
      nlinarith only [hh]
    have hs : ε^2 ≤ (density D X Y-density D U.val W.val)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hε.le hgap 2
    have hm := mul_le_mul hw hs (sq_nonneg ε) (show 0 ≤ mass X Y by unfold mass;positivity)
    simp only [b,if_neg hReg]
    nlinarith only [hg,hm]
  have hSum := sum_le_sum (s:=univ) (fun U (_ : U ∈ univ) =>
    sum_le_sum (s:=univ) (fun W (_ : W ∈ univ) => hLocal U W))
  simp_rw [sum_add_distrib,←mul_sum] at hSum
  have hCoarse : (∑ U : P.parts,∑ W : P.parts,pairEnergy D U.val W.val)=
      ∑ U∈P.parts,∑ W∈P.parts,pairEnergy D U W := by
    rw [Finset.sum_coe_sort P.parts (fun U => ∑ W : P.parts,pairEnergy D U W.val)]
    apply sum_congr rfl
    intro U _
    exact Finset.sum_coe_sort P.parts _
  rw [hCoarse] at hSum
  unfold witnessRefinement
  rw [partitionEnergy_bind]
  unfold partitionEnergy irregularMass
  rw [←mul_div_assoc,←add_div]
  exact div_le_div_of_nonneg_right hSum (sq_nonneg _)

theorem witnessRefinement_uniform_gain (D : Digraph V)
    (P : Finpartition (univ : Finset V)) (ε : ℝ) (hε : 0 < ε)
    (hBad : ε ≤ irregularMass D P ε) :
    partitionEnergy D P + ε^5 ≤
      partitionEnergy D (witnessRefinement D P ε hε) := by
  have hm := mul_le_mul_of_nonneg_left hBad (pow_nonneg hε.le 4)
  have hg := witnessRefinement_energy_increment D P ε hε
  nlinarith only [hm,hg]

end OverfullWork.DirectedPairEnergy
