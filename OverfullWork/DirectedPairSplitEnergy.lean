module

public import OverfullWork.DirectedPairEnergy

@[expose] public section


/-! The actual four-rectangle refinement of one directed pair.
Mass and arc counts are preserved exactly; energy is monotone, with
an epsilon^4 gain for an actual witness of non-regularity. -/
namespace OverfullWork.DirectedPairEnergy
open Finset DirectedRobustExpansion DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 12000000

noncomputable def splitCell (A X : Finset V) (b : Bool) : Finset V := if b then X else A\X

noncomputable def splitEnergy (D : Digraph V) (A B X Y : Finset V) : ℝ :=
  ∑ ij : Bool × Bool,pairEnergy D (splitCell A X ij.1) (splitCell B Y ij.2)

theorem incidences_source_split (D : Digraph V) (A X B : Finset V) (hX : X⊆A) :
    incidences D X B+incidences D (A\X) B=incidences D A B := by
  unfold incidences inNeighbours
  simp only [card_filter]
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  exact (add_comm _ _).trans (sum_sdiff hX)

theorem incidences_target_split (D : Digraph V) (A B Y : Finset V) (hY : Y⊆B) :
    incidences D A Y+incidences D A (B\Y)=incidences D A B := by
  unfold incidences
  exact (add_comm _ _).trans (sum_sdiff hY)

theorem split_mass_sum (A B X Y : Finset V) (hX : X⊆A) (hY : Y⊆B) :
    (∑ ij : Bool × Bool,mass (splitCell A X ij.1) (splitCell B Y ij.2))=mass A B := by
  have hA : (X.card:ℝ)+((A\X).card:ℝ)=(A.card:ℝ) := by
    exact_mod_cast ((add_comm _ _).trans (card_sdiff_add_card_eq_card hX))
  have hB : (Y.card:ℝ)+((B\Y).card:ℝ)=(B.card:ℝ) := by
    exact_mod_cast ((add_comm _ _).trans (card_sdiff_add_card_eq_card hY))
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,splitCell,Bool.false_eq_true,if_false,if_true,mass]
  nlinarith only [congrArg (fun z : ℝ => z*(B.card:ℝ)) hA,
    congrArg (fun z : ℝ => (X.card:ℝ)*z) hB,
    congrArg (fun z : ℝ => ((A\X).card:ℝ)*z) hB]

theorem split_mass_density_sum (D : Digraph V) (A B X Y : Finset V) (hX : X⊆A) (hY : Y⊆B) :
    (∑ ij : Bool × Bool,mass (splitCell A X ij.1) (splitCell B Y ij.2)*
      density D (splitCell A X ij.1) (splitCell B Y ij.2))=(incidences D A B:ℝ) := by
  simp only [density_mass]
  have hCount : (∑ ij : Bool × Bool,incidences D (splitCell A X ij.1) (splitCell B Y ij.2))=
      incidences D A B := by
    have h₁ := incidences_source_split D A X Y hX
    have h₂ := incidences_source_split D A X (B\Y) hX
    have h₃ := incidences_target_split D A B Y hY
    simp only [Fintype.sum_prod_type,Fintype.sum_bool,splitCell,Bool.false_eq_true,if_false,if_true]
    omega
  exact_mod_cast hCount

theorem split_energy_mono (D : Digraph V) (A B X Y : Finset V) (hX : X⊆A) (hY : Y⊆B) :
    pairEnergy D A B ≤ splitEnergy D A B X Y := by
  let w := fun ij : Bool × Bool => mass (splitCell A X ij.1) (splitCell B Y ij.2)
  let d := fun ij : Bool × Bool => density D (splitCell A X ij.1) (splitCell B Y ij.2)
  have hMass : (∑ ij,w ij)=mass A B := split_mass_sum A B X Y hX hY
  have hBalance : (∑ ij,w ij*d ij)=(∑ ij,w ij)*density D A B := by
    rw [hMass,density_mass]
    exact split_mass_density_sum D A B X Y hX hY
  have hh := weighted_energy_mono w d (density D A B)
    (fun ij => by unfold w mass;positivity) hBalance
  rw [hMass] at hh
  exact hh

theorem split_energy_gain_of_witness (D : Digraph V) (A B X Y : Finset V) (ε : ℝ)
    (hε : 0 ≤ ε) (hX : X⊆A) (hY : Y⊆B)
    (hSizeX : (A.card:ℝ)*ε ≤ (X.card:ℝ)) (hSizeY : (B.card:ℝ)*ε ≤ (Y.card:ℝ))
    (hGap : ε ≤ |density D X Y-density D A B|) :
    pairEnergy D A B+ε^4*mass A B ≤ splitEnergy D A B X Y := by
  let w := fun ij : Bool × Bool => mass (splitCell A X ij.1) (splitCell B Y ij.2)
  let d := fun ij : Bool × Bool => density D (splitCell A X ij.1) (splitCell B Y ij.2)
  have hMass : (∑ ij,w ij)=mass A B := split_mass_sum A B X Y hX hY
  have hBalance : (∑ ij,w ij*d ij)=(∑ ij,w ij)*density D A B := by
    rw [hMass,density_mass]
    exact split_mass_density_sum D A B X Y hX hY
  have hGain := weighted_energy_gain_at w d (density D A B)
    (fun ij => by unfold w mass;positivity) hBalance (true,true)
  rw [hMass] at hGain
  change pairEnergy D A B+mass X Y*(density D X Y-density D A B)^2 ≤ splitEnergy D A B X Y at hGain
  have hWeight : ε^2*mass A B ≤ mass X Y := by
    have hh := mul_le_mul hSizeX hSizeY
      (mul_nonneg (Nat.cast_nonneg _) hε) (Nat.cast_nonneg _)
    unfold mass
    nlinarith only [hh]
  have hSquare : ε^2 ≤ (density D X Y-density D A B)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hε hGap 2
  have hMult := mul_le_mul hWeight hSquare (sq_nonneg ε)
    (show 0 ≤ mass X Y by unfold mass;positivity)
  have hWitness : ε^4*mass A B ≤ mass X Y*(density D X Y-density D A B)^2 := by
    nlinarith only [hMult]
  linarith only [hGain,hWitness]

end OverfullWork.DirectedPairEnergy
