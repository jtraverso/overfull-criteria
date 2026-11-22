module

public import OverfullWork.CMSOperation42NearTightRun
public import OverfullWork.SecondLowTerminalData

@[expose] public section


/-! The exact stop from Operation 4.2 has the same alternatives as
the regularization stage. Zero-degree vertices in the complement
do not affect the crossing degree sum. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph NormalizedAlmostStoppingRun
open NormalizedClassTwoStep
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem matching_removal_stop_cases {B K : ℕ} (s : State V B K)
    (hStop : IsMatchingRemovalStop s.graph s.cut.set)
    (hRoom : 2*B < s.graph.maxDegree+2) :
    let G := s.graph
    let X := s.cut.set
    let Y := Xᶜ
    (∑ y ∈ Y,G.degree y) = 0 ∨
      (0 < ∑ y ∈ Y,G.degree y) ∧ (∀ x ∈ X,(∑ y ∈ Y,G.degree y) ≤ G.degree x) ∨
      Nonempty (SecondLowData s) := by
  intro G X Y
  by_cases hEmpty : (∑ y ∈ Y,G.degree y) = 0
  · exact Or.inl hEmpty
  right
  by_cases hSmall : ∀ x ∈ X,(∑ y ∈ Y,G.degree y) ≤ G.degree x
  · exact Or.inl ⟨Nat.pos_of_ne_zero hEmpty,hSmall⟩
  right
  push Not at hSmall
  obtain ⟨u,hu,hU⟩ := hSmall
  have hU' : G.degree u < ∑ y ∈ Y,G.degree y := hU
  have hActive : 2 ≤ (Y.filter (fun y => 0 < G.degree y)).card :=
    ClassTwoGlobalNoOverfull.two_active_of_large_centre G s.cut u hu hU'
  change IsMatchingRemovalStop G X at hStop
  rcases hStop with hOne | ⟨x,hx,hMin,hEnd⟩
  · exact False.elim ((Nat.not_le_of_lt (show 1 < (Y.filter (fun y => 0 < G.degree y)).card from hActive)) hOne)
  have hLarge : G.degree x < ∑ y ∈ Y,G.degree y := (hMin u hu).trans_lt hU'
  rcases hEnd with h | ⟨v,hv,hvx,hLow⟩
  · exact False.elim (Nat.not_le_of_lt hLarge h)
  have hLow' : G.degree v ≤ G.maxDegree-G.degree x := Nat.le_sub_of_add_le hLow
  have hInd := enlarged_independent_of_second_low G s.cut s.ready hx hLarge hv hvx hLow' hRoom
  exact ⟨⟨x,hx,hLarge,v,hv,hvx,hLow',hInd⟩⟩

end OverfullWork.CMSMatchingRemoval
