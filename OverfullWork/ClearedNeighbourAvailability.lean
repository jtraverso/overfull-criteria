module

public import OverfullWork.AnchorPrescriptions
public import OverfullWork.PaperCentreNeighbourhood

@[expose] public section


/-! # The first-anchor reserve when the complete neighbourhood is cleared

This is the small-centre Stage II branch in CMS Step 4. Every available
centre neighbor lies in the cleared set. The strict palette reserve and
the regular ambient degree supply an actual remaining crossing copy.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 24000000

theorem first_anchor_mass_of_cleared_neighbours (P : M.PartialColouring k) (A Z : Finset V)
    (a : V) (D : ℕ) (i : Fin k) (ha : a ∈ A) (hRegular : M.IsRegularOfDegree D)
    (hPalette : k < D) (hCover : P.CoversInternal A)
    (hNeighbour : ∀ v, M.supportGraph.Adj a v → v ∈ Z)
    (hClear : ∀ v ∈ Z, v ∈ Aᶜ → (P.colouring.colourGraph i).degree v=0) :
    0 < P.available.degreeInto (P.colouring.missingSet Aᶜ i) a := by
  have hDegree := P.available_degree a
  have hBound := P.colouring.degree_le_palette a
  rw [hRegular a] at hDegree
  have hPositive : 0 < P.available.degree a := by omega
  rw [MultiGraph.degree_eq_sum_mult] at hPositive
  obtain ⟨v,hv,hCopy⟩ := sum_pos_iff.mp hPositive
  have hAmbient : M.supportGraph.Adj a v := by
    change 0 < M.mult s(a,v)
    have hLe : P.available.mult s(a,v) ≤ M.mult s(a,v) := Nat.sub_le _ _
    omega
  have hvZ := hNeighbour v hAmbient
  have hvSide : v ∉ A := by
    intro hvA
    have hFull := hCover a v (by tauto)
    change 0 < M.mult s(a,v)-P.graph.mult s(a,v) at hCopy
    rw [hFull,Nat.sub_self] at hCopy
    omega
  have hvMissing : v ∈ P.colouring.missingSet Aᶜ i :=
    mem_filter.mpr ⟨mem_compl.mpr hvSide,hClear v hvZ (mem_compl.mpr hvSide)⟩
  exact sum_pos_iff.mpr ⟨v,hvMissing,hCopy⟩

end SimpleGraph.MultiGraph.PartialColouring
