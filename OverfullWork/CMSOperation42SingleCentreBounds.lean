module

public import OverfullWork.CMSOperation42StopCases
public import OverfullWork.CMSOneCentreTerminalColouring

@[expose] public section


/-! Bounds for the actual one-centre stopping graph. If the quotient
order were at most the maximum degree, the ordinary core alone
would force a budget of at least twice its order. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph OddCutDeficit RobustExpansion
open NormalizedAlmostStoppingRun IndependentSetIdentification NearTightOddSetGeometry
open scoped Classical
universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem maxDegree_lt_single_centre_order (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hSmall : B+K ≤ c.set.card) :
    G.maxDegree < Fintype.card (Vertices c.setᶜ) := by
  let X := c.set
  let d := G.maxDegree
  let n := Fintype.card V
  have hX : 0 < X.card := by obtain ⟨k,hk⟩ := c.odd; change X.card = _ at hk; omega
  obtain ⟨v,hv⟩ := card_pos.mp hX
  letI : Nonempty V := ⟨v⟩
  have hD : d < n := G.maxDegree_lt_card_verts
  have hSum : X.card+Xᶜ.card = n := card_add_card_compl X
  have hComp : Xᶜ.card ≤ K := c.complement_small
  have hInd : G.IsIndepSet (↑(Xᶜ) : Set V) := by simpa only [X,coe_compl] using c.independent
  have hEq := internal_cut_deficit_identity G d G.degree_le_maxDegree X
  rw [MatchingOddDeficiency.cut_eq_complementary_degree_sum G X hInd] at hEq
  have hBudget := c.budget
  change deficitMass G d X+(∑ v ∈ Xᶜ,G.degree v) ≤ d+B at hBudget
  have hBound := internalEdges_le_card_mul_half G X c.odd
  have hCard : Fintype.card (Vertices c.setᶜ) = X.card+1 := by
    rw [card_vertices,compl_compl]
  rw [hCard]
  by_contra! hLarge
  change X.card+1 ≤ d at hLarge
  have hLess := Nat.mul_le_mul_right X.card hLarge
  have hOddSize : 2*(X.card/2)+1 = X.card := by
    obtain ⟨k,hk⟩ := c.odd
    change X.card = _ at hk
    omega
  have hComplete : 2*internalEdges G X+X.card ≤ X.card*X.card := calc
    _ ≤ 2*(X.card*(X.card/2))+X.card := by omega
    _ = X.card*(2*(X.card/2)+1) := by ring
    _ = _ := by rw [hOddSize]
  have hProd : (X.card+1)*X.card = X.card*X.card+X.card := by ring
  change B+K ≤ X.card at hSmall
  omega

end OverfullWork.CMSMatchingRemoval
