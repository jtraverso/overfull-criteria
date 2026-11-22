module

public import OverfullWork.ExceptionalPureDigraph
public import OverfullWork.DirectedRegularPairs

@[expose] public section


/-! Exact off-diagonal pair preservation by exceptional pure cleaning.
Any established regularity/density data transfer with no extra error. -/
namespace OverfullWork.DirectedRegularPairs
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 6000000

theorem incidences_congr_on (D H : Digraph V) (U W : Finset V)
    (h : ∀ u∈U,∀ v∈W,D.Adj u v ↔ H.Adj u v) : incidences D U W=incidences H U W := by
  unfold incidences
  apply sum_congr rfl
  intro v hv
  unfold inNeighbours
  congr 1
  apply filter_congr
  intro u hu
  exact h u hu v hv

theorem density_congr_on (D H : Digraph V) (U W : Finset V)
    (h : ∀ u∈U,∀ v∈W,D.Adj u v ↔ H.Adj u v) : density D U W=density H U W := by
  unfold density
  rw [incidences_congr_on D H U W h]

theorem uniform_congr_on (D H : Digraph V) (U W : Finset V) (ε : ℝ)
    (h : ∀ u∈U,∀ v∈W,D.Adj u v ↔ H.Adj u v) :
    IsUniform D ε U W ↔ IsUniform H ε U W := by
  have hBase := density_congr_on D H U W h
  constructor
  · intro hUniform A hA B hB hSizeA hSizeB
    have hSmall := density_congr_on D H A B (fun u hu v hv => h u (hA hu) v (hB hv))
    rw [←hSmall,←hBase]
    exact hUniform A hA B hB hSizeA hSizeB
  · intro hUniform A hA B hB hSizeA hSizeB
    have hSmall := density_congr_on D H A B (fun u hu v hv => h u (hA hu) v (hB hv))
    rw [hSmall,hBase]
    exact hUniform A hA B hB hSizeA hSizeB

end OverfullWork.DirectedRegularPairs

namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRegularPairs
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

theorem exceptionalPure_pair_data (D H : Digraph V) (hLe : H≤D) (f : V → Option I)
    (i j : I) (hij : i≠j) (ε : ℝ) :
    density (exceptionalPure D H f) (cluster f i) (cluster f j)=density H (cluster f i) (cluster f j) ∧
    (IsUniform (exceptionalPure D H f) ε (cluster f i) (cluster f j) ↔
      IsUniform H ε (cluster f i) (cluster f j)) := by
  have hPair := fun u hu v hv => exceptionalPure_between D H hLe f i j hij u v hu hv
  exact ⟨density_congr_on _ _ _ _ hPair,uniform_congr_on _ _ _ _ ε hPair⟩

end OverfullWork.DirectedClusterQuotient
