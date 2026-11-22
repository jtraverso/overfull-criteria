module

public import OverfullWork.SecondAnchorNeighbourAvailability

@[expose] public section


/-! # Pay the occupied-vertex bound for both actual residue palette blocks

Internal matching classes occupy exactly twice their per-side edge mass.
Use the Stage I unit masses and the proved Stage II average/residue ratio
to bound all occupied sets. No occupied-set hypothesis is added.
-/
namespace SimpleGraph.MultiGraph.EdgeColoring
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {A : Finset V}
set_option maxHeartbeats 24000000

theorem occupied_card_eq_twice_internal {k : ℕ} (C : (M.internalPart A).EdgeColoring k) (i : Fin k) :
    (A\C.missingSet A i).card=2*(C.colourGraph i).edgesWithin A := by
  have hMissing := C.internal_missing_count A i
  have hSplit := card_sdiff_add_card_eq_card (show C.missingSet A i ⊆ A from filter_subset _ _)
  omega

theorem occupied_bound_of_two_stage {q h R : ℕ} (C : (M.internalPart A).EdgeColoring (q+3*h))
    (u : ℝ) (hu : 0 ≤ u)
    (hFirst : ∀ i : Fin q, (C.colourGraph (Fin.castAdd (3*h) i)).edgesWithin A=1)
    (hSecond : ∀ i : Fin (3*h), (3*h)*(C.colourGraph (Fin.natAdd q i)).edgesWithin A ≤ R+3*h)
    (hResidue : 4*(R:ℝ) ≤ u*(h:ℝ)/1024) (i : Fin (q+3*h)) :
    ((A\C.missingSet A i).card:ℝ) ≤ u/100+2 := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [C.occupied_card_eq_twice_internal,hFirst]
    norm_num
    linarith
  · intro j
    have hPositive : (0:ℝ) < h := by
      have hh : 0 < h := by have hj := j.isLt;omega
      exact_mod_cast hh
    have hMass : (3:ℝ)*(h:ℝ)*((C.colourGraph (Fin.natAdd q j)).edgesWithin A:ℝ) ≤ (R:ℝ)+3*(h:ℝ) := by
      exact_mod_cast hSecond j
    have hCompare : (h:ℝ)*((C.colourGraph (Fin.natAdd q j)).edgesWithin A:ℝ) ≤
        (h:ℝ)*(u/12288+1) := by nlinarith only [hMass,hResidue]
    have hBound := le_of_mul_le_mul_left hCompare hPositive
    have hCard : ((A\C.missingSet A (Fin.natAdd q j)).card:ℝ)=
        2*((C.colourGraph (Fin.natAdd q j)).edgesWithin A:ℝ) := by
      exact_mod_cast C.occupied_card_eq_twice_internal (Fin.natAdd q j)
    linarith

end SimpleGraph.MultiGraph.EdgeColoring
