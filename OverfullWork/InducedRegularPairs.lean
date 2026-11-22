module

public import OverfullWork.InducedDigraphSampling
public import OverfullWork.DirectedRegularPairs
public import OverfullWork.DirectedClusterQuotient

@[expose] public section


/-! Transport directed regular pairs to the actual induced digraph.
The host images and sampled cluster fibres are identified exactly. -/
namespace OverfullWork.InducedDigraphSampling
open Finset DirectedRobustExpansion DirectedRegularPairs DirectedClusterQuotient
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

noncomputable def host (X : Finset V) (A : Finset X) : Finset V :=
  A.map ⟨Subtype.val,Subtype.val_injective⟩

theorem host_card (X : Finset V) (A : Finset X) : (host X A).card=A.card := card_map _

theorem host_mono (X : Finset V) {A B : Finset X} (h : A ⊆ B) : host X A ⊆ host X B :=
  map_subset_map.mpr h

theorem induced_inNeighbours (D : Digraph V) (X : Finset V) (A : Finset X) (v : X) :
    inNeighbours (induced D X) A v=inNeighbours D (host X A) v.val := by
  unfold inNeighbours
  apply card_bij (fun u _ => u.val)
  · intro u hu
    exact mem_filter.mpr ⟨mem_map.mpr ⟨u,(mem_filter.mp hu).1,rfl⟩,(mem_filter.mp hu).2⟩
  · intro u _ w _ hh
    exact Subtype.ext hh
  · intro u hu
    obtain ⟨w,hw,rfl⟩ := mem_map.mp (mem_filter.mp hu).1
    exact ⟨w,mem_filter.mpr ⟨hw,(mem_filter.mp hu).2⟩,rfl⟩

theorem induced_incidences (D : Digraph V) (X : Finset V) (A B : Finset X) :
    incidences (induced D X) A B=incidences D (host X A) (host X B) := by
  unfold incidences
  conv_rhs => rw [host,sum_map]
  exact sum_congr rfl fun v _ => induced_inNeighbours D X A v

theorem induced_density (D : Digraph V) (X : Finset V) (A B : Finset X) :
    density (induced D X) A B=density D (host X A) (host X B) := by
  simp only [density,induced_incidences,host_card]

theorem uniform_induced (D : Digraph V) (X : Finset V) (U W : Finset X) (ε : ℝ)
    (hUniform : IsUniform D ε (host X U) (host X W)) :
    IsUniform (induced D X) ε U W := by
  intro A hA B hB hASize hBSize
  rw [induced_density,induced_density]
  apply hUniform (host X A) (host_mono X hA) (host X B) (host_mono X hB)
  · simpa only [host_card] using hASize
  · simpa only [host_card] using hBSize

theorem host_cluster (X : Finset V) (f : V → Option I) (i : I) :
    host X (cluster (fun v : X => f v.val) i)=X ∩ cluster f i := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
    exact mem_inter.mpr ⟨w.property,(mem_cluster f i w.val).mpr
      ((mem_cluster (fun v : X => f v.val) i w).mp hw)⟩
  · intro hv
    exact mem_map.mpr ⟨⟨v,(mem_inter.mp hv).1⟩,
      (mem_cluster (fun v : X => f v.val) i _).mpr ((mem_cluster f i v).mp (mem_inter.mp hv).2),rfl⟩

theorem sampled_cluster_card (X : Finset V) (f : V → Option I) (i : I) :
    (cluster (fun v : X => f v.val) i).card=(X ∩ cluster f i).card := by
  rw [←host_cluster,host_card]

theorem sampled_exceptional_card_le (X : Finset V) (f : V → Option I) :
    (exceptional (fun v : X => f v.val)).card ≤ (exceptional f).card := by
  rw [←host_card X]
  apply card_le_card
  intro v hv
  obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
  exact (mem_exceptional f w.val).mpr ((mem_exceptional (fun v : X => f v.val) w).mp hw)

end OverfullWork.InducedDigraphSampling
