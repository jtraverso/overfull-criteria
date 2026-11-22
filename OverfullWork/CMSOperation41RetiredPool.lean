module

public import OverfullWork.CMSOperation41EmptyActiveChoice

@[expose] public section


/-! The ordinary part of the current active graph consists of the
fixed core and the surviving retired vertices. The parity test in S2.3
and S2.4 can therefore be read before the spokes are assigned. -/
namespace OverfullWork.CMSTrimmingRound

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def retiredTrimmingPool (initial current active : Finset V) : Finset V :=
  (active ∩ initial) \ current

theorem ordinary_and_retired_trimming_partition (initial current active : Finset V)
    (hCurrent : current ⊆ initial) (hCore : initialᶜ ⊆ active) :
    active \ current = initialᶜ ∪ retiredTrimmingPool initial current active ∧
      Disjoint initialᶜ (retiredTrimmingPool initial current active) := by
  constructor
  · ext v
    rw [retiredTrimmingPool,mem_sdiff,mem_union,mem_sdiff,mem_inter,mem_compl]
    by_cases h : v ∈ initial
    · simp only [h,not_true_eq_false,and_true,false_or]
    · have ha := hCore (mem_compl.mpr h)
      have hc : v ∉ current := fun hv => h (hCurrent hv)
      simp [h,ha,hc]
  · rw [disjoint_left]
    intro v hv hRetired
    exact mem_compl.mp hv (mem_inter.mp (mem_sdiff.mp hRetired).1).2

theorem trimming_parity_for_retired_spokes (initial current active : Finset V)
    (hCurrent : current ⊆ initial) (hCore : initialᶜ ⊆ active) :
    let B := retiredTrimmingPool initial current active
    let X := active \ current
    (initialᶜ.card+B.card = X.card) ∧
      (∀ z ∈ current,initialᶜ.card+(insert z B).card = X.card+1) ∧
      ∀ z ∈ X,(initialᶜ.erase z).card+(B.erase z).card+1 = X.card := by
  intro B X
  obtain ⟨hUnion,hDis⟩ := ordinary_and_retired_trimming_partition initial current active hCurrent hCore
  change X = initialᶜ ∪ B at hUnion
  change Disjoint initialᶜ B at hDis
  have hCard : initialᶜ.card+B.card = X.card := by rw [hUnion,card_union_of_disjoint hDis]
  refine ⟨hCard,?_,?_⟩
  · intro z hz
    have hNot : z ∉ B := fun h => (mem_sdiff.mp h).2 hz
    rw [card_insert_of_notMem hNot,←hCard,add_assoc]
  · intro z hz
    rw [hUnion] at hz
    rcases mem_union.mp hz with hz | hz
    · have hNot := disjoint_left.mp hDis hz
      rw [erase_eq_of_notMem hNot,←hCard]
      have hErase := card_erase_add_one hz
      omega
    · have hNot := disjoint_left.mp hDis.symm hz
      rw [erase_eq_of_notMem hNot,←hCard]
      have hErase := card_erase_add_one hz
      omega

end OverfullWork.CMSTrimmingRound
