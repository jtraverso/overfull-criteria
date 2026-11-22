module

public import OverfullWork.CMSOperation42Round
public import OverfullWork.ClassTwoMatchingRun

@[expose] public section


/-! Termination count of CMS Operation 4.2. The loss incurred in
cleanup is charged against the decrease in complementary degree mass. -/
namespace OverfullWork.ClassTwoCleanupRound

open Finset SimpleGraph OddCutDeficit
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1200000 in
theorem CleanRound.excess_decreases {G : SimpleGraph V} [DecidableRel G.Adj] {X : Finset V}
    (s : CleanRound G X) (hMinimum : ∀ v ∈ X,G.degree s.anchor ≤ G.degree v)
    (hLarge : G.degree s.anchor < ∑ v ∈ Xᶜ,G.degree v) (v : V) (hv : v ∈ X) :
    ((∑ w ∈ Xᶜ,s.graph.degree w)-s.graph.degree v)+1 ≤
      (∑ w ∈ Xᶜ,G.degree w)-G.degree s.anchor := by
  let R := G \ s.round.matching
  let H := s.graph
  let loss (u : V) := R.degree u-H.degree u
  let B := ∑ u ∈ X, loss u
  let d := H.maxDegree
  have hRMax : R.maxDegree = G.maxDegree-1 := by
    simpa only [R,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
      using s.round.residual_maxDegree
  have hMax : R.maxDegree = d := hRMax.trans s.maximum.symm
  have hDiff : deficitMass R d X+B = deficitMass H d X := by
    unfold deficitMass
    change _ + (∑ u ∈ X,loss u) = _
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro u _
    have hLe := SimpleGraph.degree_le_of_le s.le_residue (v := u)
    have hR := R.degree_le_maxDegree u
    have hH := H.degree_le_maxDegree u
    change H.degree u ≤ R.degree u at hLe
    rw [hMax] at hR
    dsimp only [loss,d] at *
    omega
  have hBudget := s.budget_drop_three
  have hDef := s.round.deficit_mass_add_one s.anchor_mem s.anchor_nonmaximum
  change (deficitMass R R.maxDegree X)+1 = deficitMass G G.maxDegree X at hDef
  rw [hMax] at hDef
  change (deficitMass H d X+(∑ u ∈ Xᶜ,H.degree u))+3 =
    deficitMass G G.maxDegree X+(∑ u ∈ Xᶜ,G.degree u) at hBudget
  have hExact : B+(∑ u ∈ Xᶜ,H.degree u)+2 = ∑ u ∈ Xᶜ,G.degree u := by omega
  have hOne : loss v ≤ B :=
    single_le_sum (f := loss) (fun _ _ => Nat.zero_le _) hv
  have hDrop : R.degree v+s.round.matching.degree v=G.degree v := by
    simpa only [R,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G s.round.matching s.round.le_original v
  have hLe : H.degree v ≤ R.degree v := SimpleGraph.degree_le_of_le s.le_residue (v := v)
  have hDegree := hMinimum v hv
  have hLayer := s.round.degree_le_one v
  change ((∑ w ∈ Xᶜ,H.degree w)-H.degree v)+1 ≤
    (∑ w ∈ Xᶜ,G.degree w)-G.degree s.anchor
  dsimp only [loss] at hOne
  omega

end OverfullWork.ClassTwoCleanupRound
