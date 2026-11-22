module

public import OverfullWork.CaseTwoProtectedExceptions

@[expose] public section


/-! # The full small-centre neighbourhood in CMS condition S3.3

The paper's Z consists of every simple neighbour when the centre has
small simple degree; it is empty in the other branch. It must not be
replaced by the set of large-multiplicity neighbours.
-/
namespace OverfullWork.PaperCentreNeighbourhood
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def protectedNeighbours (G : SimpleGraph V) (a : V) (cut : ℕ) : Finset V :=
  if G.degree a < cut then G.neighborFinset a else ∅

theorem card_le_cut (G : SimpleGraph V) (a : V) (cut : ℕ) :
    (protectedNeighbours G a cut).card ≤ cut := by
  unfold protectedNeighbours
  split_ifs with hSmall
  · rw [card_neighborFinset_eq_degree]
    omega
  · simp

theorem contains_neighbour_of_small (G : SimpleGraph V) (a : V) (cut : ℕ)
    (hSmall : G.degree a < cut) (v : V) (hAdj : G.Adj a v) :
    v ∈ protectedNeighbours G a cut := by
  rw [protectedNeighbours,if_pos hSmall]
  exact (mem_neighborFinset G a v).mpr hAdj

theorem empty_of_large (G : SimpleGraph V) (a : V) (cut : ℕ) (hLarge : cut ≤ G.degree a) :
    protectedNeighbours G a cut=∅ := by
  rw [protectedNeighbours,if_neg (by omega)]

end OverfullWork.PaperCentreNeighbourhood
