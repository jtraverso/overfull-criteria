module

public import OverfullWork.DirectedDegreeTrimming
public import OverfullWork.DirectedRegularPairs
public import OverfullWork.DirectedClusterQuotient

@[expose] public section


/-! Move actual vertices with excessive losses to the exceptional set.
The remaining fibres, their sizes and their directed regular pairs are
tracked explicitly. Equalizing the remaining fibres is separate. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRobustExpansion DirectedRegularPairs
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

noncomputable def trim (f : V → Option I) (X : Finset V) : V → Option I :=
  fun v => if v ∈ X then none else f v

theorem cluster_trim (f : V → Option I) (X : Finset V) (i : I) :
    cluster (trim f X) i=cluster f i\X := by
  ext v
  simp only [mem_cluster,mem_sdiff,trim]
  by_cases hv : v ∈ X <;> simp [hv]

theorem exceptional_trim (f : V → Option I) (X : Finset V) :
    exceptional (trim f X)=exceptional f ∪ X := by
  ext v
  simp only [mem_exceptional,mem_union,trim]
  by_cases hv : v ∈ X <;> simp [hv]

theorem exceptional_trim_card_le (f : V → Option I) (X : Finset V) :
    (exceptional (trim f X)).card ≤ (exceptional f).card+X.card := by
  rw [exceptional_trim]
  exact card_union_le _ _

theorem cluster_trim_card_bounds (f : V → Option I) (X : Finset V) (i : I) :
    (cluster f i).card ≤ (cluster (trim f X) i).card+X.card ∧
    (cluster (trim f X) i).card ≤ (cluster f i).card := by
  rw [cluster_trim]
  constructor
  · have hh := card_sdiff_add_card_inter (cluster f i) X
    have hSub := card_le_card (s:=cluster f i ∩ X) (t:=X) inter_subset_right
    omega
  · exact card_le_card sdiff_subset

theorem trim_uniform (D : Digraph V) (f : V → Option I) (X : Finset V)
    (i j : I) (ε ε' : ℝ)
    (hUniform : IsUniform D ε (cluster f i) (cluster f j))
    (hI : ((cluster f i).card:ℝ)*ε ≤ ((cluster (trim f X) i).card:ℝ))
    (hJ : ((cluster f j).card:ℝ)*ε ≤ ((cluster (trim f X) j).card:ℝ))
    (hIScale : ((cluster f i).card:ℝ)*ε ≤ ((cluster (trim f X) i).card:ℝ)*ε')
    (hJScale : ((cluster f j).card:ℝ)*ε ≤ ((cluster (trim f X) j).card:ℝ)*ε')
    (hTol : 2*ε ≤ ε') : IsUniform D ε' (cluster (trim f X) i) (cluster (trim f X) j) := by
  apply uniform_on_subcells D hUniform ?_ ?_ hI hJ hIScale hJScale hTol
  · rw [cluster_trim];exact sdiff_subset
  · rw [cluster_trim];exact sdiff_subset

theorem trim_density (D : Digraph V) (f : V → Option I) (X : Finset V)
    (i j : I) (ε d : ℝ)
    (hUniform : IsUniform D ε (cluster f i) (cluster f j))
    (hDensity : d ≤ density D (cluster f i) (cluster f j))
    (hI : ((cluster f i).card:ℝ)*ε ≤ ((cluster (trim f X) i).card:ℝ))
    (hJ : ((cluster f j).card:ℝ)*ε ≤ ((cluster (trim f X) j).card:ℝ)) :
    d-ε < density D (cluster (trim f X) i) (cluster (trim f X) j) := by
  apply density_on_subcells D hUniform hDensity ?_ ?_ hI hJ
  · rw [cluster_trim];exact sdiff_subset
  · rw [cluster_trim];exact sdiff_subset

theorem trimmed_loss_bounds (D H : Digraph V) (f : V → Option I) (L : ℕ) :
    ∀ v,trim f (DirectedDegreeTrimming.bad (D\H) L) v ≠ none →
      inDegree (D\H) v ≤ L ∧ outDegree (D\H) v ≤ L := by
  intro v hv
  have hNot : v ∉ DirectedDegreeTrimming.bad (D\H) L := by
    intro hh
    exact hv (by simp only [trim,if_pos hh])
  exact DirectedDegreeTrimming.loss_outside_bad (D\H) L v hNot

theorem exists_trimmed_partition (D H : Digraph V) (f : V → Option I) (L B : ℕ)
    (hTotal : DirectedDegreeTrimming.total (D\H) ≤ B) :
    ∃ (X : Finset V) (g : V → Option I),
      X.card*(L+1) ≤ 2*B ∧ g=trim f X ∧
      (exceptional g).card ≤ (exceptional f).card+X.card ∧
      (∀ i,(cluster f i).card ≤ (cluster g i).card+X.card ∧
        (cluster g i).card ≤ (cluster f i).card) ∧
      (∀ v,g v ≠ none → inDegree (D\H) v ≤ L ∧ outDegree (D\H) v ≤ L) := by
  let X := DirectedDegreeTrimming.bad (D\H) L
  refine ⟨X,trim f X,?_,rfl,exceptional_trim_card_le f X,
    cluster_trim_card_bounds f X,trimmed_loss_bounds D H f L⟩
  exact (DirectedDegreeTrimming.bad_budget (D\H) L).trans (Nat.mul_le_mul_left 2 hTotal)

end OverfullWork.DirectedClusterQuotient
