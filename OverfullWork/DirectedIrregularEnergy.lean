module

public import OverfullWork.DirectedPairSplitEnergy

@[expose] public section


/-! Extract an actual non-regularity witness and pay its local energy
increment, as required by the standard directed regularity proof.
No regular partition is assumed to exist or concluded here. -/
namespace OverfullWork.DirectedPairEnergy
open Finset DirectedRobustExpansion DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 8000000

theorem irregular_pair_energy_increment (D : Digraph V) (A B : Finset V) (ε : ℝ)
    (hε : 0 < ε) (hNot : ¬IsUniform D ε A B) :
    ∃ X⊆A,∃ Y⊆B,
      (A.card:ℝ)*ε ≤ (X.card:ℝ) ∧ (B.card:ℝ)*ε ≤ (Y.card:ℝ) ∧
      ε ≤ |density D X Y-density D A B| ∧
      pairEnergy D A B+ε^4*mass A B ≤ splitEnergy D A B X Y := by
  by_contra hNo
  apply hNot
  intro X hX Y hY hSizeX hSizeY
  by_contra hGap
  have hWitness : ε ≤ |density D X Y-density D A B| := le_of_not_gt hGap
  exact hNo ⟨X,hX,Y,hY,hSizeX,hSizeY,hWitness,
    split_energy_gain_of_witness D A B X Y ε hε.le hX hY hSizeX hSizeY hWitness⟩

theorem irregular_pair_strict_increment (D : Digraph V) (A B : Finset V) (ε : ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hε : 0 < ε) (hNot : ¬IsUniform D ε A B) :
    ∃ X⊆A,∃ Y⊆B,pairEnergy D A B < splitEnergy D A B X Y := by
  obtain ⟨X,hX,Y,hY,_,_,_,hGain⟩ := irregular_pair_energy_increment D A B ε hε hNot
  have hMass : 0 < mass A B := by
    have ha : (0:ℝ) < A.card := by exact_mod_cast card_pos.mpr hA
    have hb : (0:ℝ) < B.card := by exact_mod_cast card_pos.mpr hB
    exact mul_pos ha hb
  have hPos : 0 < ε^4*mass A B := mul_pos (pow_pos hε _) hMass
  exact ⟨X,hX,Y,hY,by linarith only [hGain,hPos]⟩

end OverfullWork.DirectedPairEnergy
