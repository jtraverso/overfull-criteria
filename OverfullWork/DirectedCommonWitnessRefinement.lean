module

public import OverfullWork.DirectedIrregularEnergy
public import OverfullWork.DirectedCommonEnergyMonotonicity

@[expose] public section


/-! The actual simultaneous refinement by all directed irregularity
witnesses. Each parent is cut by outgoing AND incoming witnesses.
Mathlib atomise bounds the number of parts and exactly recovers each
witness as a union of atoms. This does not yet prove the global energy
increment or termination/equalization of directed regularity. -/
namespace OverfullWork.DirectedPairEnergy
open Finset Finpartition DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 12000000

noncomputable def pairWitness (D : Digraph V) (ε : ℝ) (hε : 0 < ε) (A B : Finset V) :
    Finset V × Finset V :=
  if h : IsUniform D ε A B then (∅,∅) else
    let hEx := irregular_pair_energy_increment D A B ε hε h
    (hEx.choose,hEx.choose_spec.2.choose)

theorem pairWitness_spec (D : Digraph V) (ε : ℝ) (hε : 0 < ε) (A B : Finset V)
    (hNot : ¬IsUniform D ε A B) :
    let X := (pairWitness D ε hε A B).1
    let Y := (pairWitness D ε hε A B).2
    X⊆A ∧ Y⊆B ∧ (A.card:ℝ)*ε ≤ (X.card:ℝ) ∧ (B.card:ℝ)*ε ≤ (Y.card:ℝ) ∧
      ε ≤ |density D X Y-density D A B| ∧
      pairEnergy D A B+ε^4*mass A B ≤ splitEnergy D A B X Y := by
  simp only [pairWitness,dif_neg hNot]
  have hEx := irregular_pair_energy_increment D A B ε hε hNot
  exact ⟨hEx.choose_spec.1,hEx.choose_spec.2.choose_spec.1,hEx.choose_spec.2.choose_spec.2⟩

theorem pairWitness_subsets (D : Digraph V) (ε : ℝ) (hε : 0 < ε) (A B : Finset V) :
    (pairWitness D ε hε A B).1⊆A ∧ (pairWitness D ε hε A B).2⊆B := by
  by_cases h : IsUniform D ε A B
  · simp only [pairWitness,dif_pos h]
    exact ⟨empty_subset _,empty_subset _⟩
  · have hh := pairWitness_spec D ε hε A B h
    exact ⟨hh.1,hh.2.1⟩

noncomputable def witnessCuts (D : Digraph V) (P : Finpartition (univ : Finset V))
    (ε : ℝ) (hε : 0 < ε) (U : Finset V) : Finset (Finset V) :=
  (P.parts.image fun W => (pairWitness D ε hε U W).1) ∪
    (P.parts.image fun W => (pairWitness D ε hε W U).2)

theorem witnessCuts_card (D : Digraph V) (P : Finpartition (univ : Finset V))
    (ε : ℝ) (hε : 0 < ε) (U : Finset V) :
    (witnessCuts D P ε hε U).card ≤ 2*P.parts.card := by
  have hUnion := card_union_le
    (P.parts.image fun W => (pairWitness D ε hε U W).1)
    (P.parts.image fun W => (pairWitness D ε hε W U).2)
  have hOut := card_image_le (s:=P.parts) (f:=fun W => (pairWitness D ε hε U W).1)
  have hIn := card_image_le (s:=P.parts) (f:=fun W => (pairWitness D ε hε W U).2)
  unfold witnessCuts
  omega

noncomputable def witnessRefinement (D : Digraph V) (P : Finpartition (univ : Finset V))
    (ε : ℝ) (hε : 0 < ε) : Finpartition (univ : Finset V) :=
  P.bind fun U _ => Finpartition.atomise U (witnessCuts D P ε hε U)

theorem witnessRefinement_card (D : Digraph V) (P : Finpartition (univ : Finset V))
    (ε : ℝ) (hε : 0 < ε) :
    (witnessRefinement D P ε hε).parts.card ≤ P.parts.card*2^(2*P.parts.card) := by
  unfold witnessRefinement
  rw [Finpartition.card_bind]
  calc
    _ ≤ ∑ _U∈P.parts.attach,2^(2*P.parts.card) := by
      apply sum_le_sum
      intro U hU
      exact Finpartition.card_atomise_le.trans
        (Nat.pow_le_pow_right (by omega) (witnessCuts_card D P ε hε U.val))
    _ = _ := by simp

theorem witnessRefinement_energy_mono (D : Digraph V) (P : Finpartition (univ : Finset V))
    (ε : ℝ) (hε : 0 < ε) :
    partitionEnergy D P ≤ partitionEnergy D (witnessRefinement D P ε hε) :=
  partitionEnergy_bind_mono D P _

theorem outgoing_witness_recovered (D : Digraph V) (P : Finpartition (univ : Finset V))
    (ε : ℝ) (hε : 0 < ε) (U W : Finset V) (hW : W∈P.parts) :
    let X := (pairWitness D ε hε U W).1
    ((Finpartition.atomise U (witnessCuts D P ε hε U)).parts.filter
      (fun C => C⊆X ∧ C.Nonempty)).biUnion id=X := by
  apply Finpartition.biUnion_filter_atomise
  · exact mem_union_left _ (mem_image.mpr ⟨W,hW,rfl⟩)
  · exact (pairWitness_subsets D ε hε U W).1

theorem incoming_witness_recovered (D : Digraph V) (P : Finpartition (univ : Finset V))
    (ε : ℝ) (hε : 0 < ε) (U W : Finset V) (hU : U∈P.parts) :
    let Y := (pairWitness D ε hε U W).2
    ((Finpartition.atomise W (witnessCuts D P ε hε W)).parts.filter
      (fun C => C⊆Y ∧ C.Nonempty)).biUnion id=Y := by
  apply Finpartition.biUnion_filter_atomise
  · exact mem_union_right _ (mem_image.mpr ⟨U,hU,rfl⟩)
  · exact (pairWitness_subsets D ε hε U W).2

end OverfullWork.DirectedPairEnergy
