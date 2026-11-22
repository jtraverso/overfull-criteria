module

public import OverfullWork.BipartiteRegularitySource
public import OverfullWork.ChunkedCellPartitions
public import OverfullWork.AlignedCellPartitions

@[expose] public section


/-! Equal directed source or target subcells of the bounded parent
partition. Parent cells may mix the two copies; no common host partition
is inferred from that mixing. -/
namespace OverfullWork.BipartiteRegularitySource
open Finset Finpartition DirectedClusterQuotient
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 18000000

def sideEmbedding (b : Bool) : V ↪ (V ⊕ V) :=
  if b then Function.Embedding.inr else Function.Embedding.inl

noncomputable def sideCell (P : Finpartition (univ : Finset (V ⊕ V)))
    (b : Bool) (i : P.parts) : Finset V := univ.filter fun v => sideEmbedding b v ∈ i.val

theorem side_cells_disjoint (P : Finpartition (univ : Finset (V ⊕ V))) (b : Bool)
    (i j : P.parts) (hij : i ≠ j) : Disjoint (sideCell P b i) (sideCell P b j) := by
  apply disjoint_left.mpr
  intro v hi hj
  exact hij (Subtype.ext (P.eq_of_mem_parts i.property j.property (mem_filter.mp hi).2 (mem_filter.mp hj).2))

theorem side_cells_cover (P : Finpartition (univ : Finset (V ⊕ V))) (b : Bool) :
    univ.biUnion (sideCell P b)=univ := by
  apply eq_univ_iff_forall.mpr
  intro v
  obtain ⟨U,hU,hv⟩ := P.exists_mem (mem_univ (sideEmbedding b v))
  exact mem_biUnion.mpr ⟨⟨U,hU⟩,mem_univ _,mem_filter.mpr ⟨mem_univ _,hv⟩⟩

theorem exists_equal_side_cells (P : Finpartition (univ : Finset (V ⊕ V)))
    (b : Bool) (m : ℕ) (hm : 0 < m) :
    ∃ f : V → Option (Σ i : P.parts,Fin ((sideCell P b i).card/m)),
      (∀ j,(cluster f j).card=m) ∧
      (∀ j,(cluster f j).map (sideEmbedding b) ⊆ j.1.val) ∧
      (exceptional f).card ≤ P.parts.card*(m-1) := by
  obtain ⟨f,hSize,hSub,hExc⟩ := exists_chunked_partition (sideCell P b) m hm
    (side_cells_disjoint P b) (side_cells_cover P b)
  refine ⟨f,hSize,?_,?_⟩
  · intro j v hv
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hv
    exact (mem_filter.mp (hSub j hu)).2
  · simpa only [Fintype.card_coe] using hExc

theorem exists_aligned_side_cells (P : Finpartition (univ : Finset (V ⊕ V)))
    (m : ℕ) (hm : 0 < m) :
    ∃ (k : ℕ) (π σ : Fin k → P.parts) (f g : V → Option (Fin k)),
      (∀ i,(cluster f i).card=m) ∧ (∀ i,(cluster g i).card=m) ∧
      (∀ i,(cluster f i).map (sideEmbedding false) ⊆ (π i).val) ∧
      (∀ i,(cluster g i).map (sideEmbedding true) ⊆ (σ i).val) ∧
      (exceptional f).card=(exceptional g).card ∧
      (exceptional f).card ≤ P.parts.card*(m-1) ∧
      m*k ≤ Fintype.card V ∧ Fintype.card V ≤ P.parts.card*(m-1)+m*k := by
  obtain ⟨f,hF,hFP,hFE⟩ := exists_equal_side_cells P false m hm
  obtain ⟨g,hG,hGP,hGE⟩ := exists_equal_side_cells P true m hm
  obtain ⟨ρ,ζ,f',g',hρ,hζ,hF',hG',hSame,hCost⟩ := exists_aligned_cells f g m hF hG
  let k := min (Fintype.card (Σ i : P.parts,Fin ((sideCell P false i).card/m)))
    (Fintype.card (Σ i : P.parts,Fin ((sideCell P true i).card/m)))
  have hE : (exceptional f').card ≤ P.parts.card*(m-1) := hCost.trans (max_le hFE hGE)
  have hOrder := order_eq f' m hF'
  simp only [Fintype.card_fin] at hOrder
  change Fintype.card V=(exceptional f').card+m*k at hOrder
  refine ⟨k,(fun i => (ρ i).1),(fun i => (ζ i).1),f',g',hF',hG',?_,?_,hSame,hE,by omega,by omega⟩
  · intro i;rw [hρ];exact hFP (ρ i)
  · intro i;rw [hζ];exact hGP (ζ i)

theorem exists_punctured_side_cells (P : Finpartition (univ : Finset (V ⊕ V)))
    (b : Bool) (X : Finset V) (m : ℕ) (hm : 0 < m) :
    ∃ f : V → Option (Σ i : P.parts,Fin (((sideCell P b i)\X).card/m)),
      (∀ j,(cluster f j).card=m) ∧
      (∀ j,(cluster f j).map (sideEmbedding b) ⊆ j.1.val) ∧
      (∀ v,f v ≠ none → v ∉ X) ∧
      (exceptional f).card ≤ X.card+P.parts.card*(m-1) := by
  let A := fun i : P.parts => sideCell P b i\X
  have hDis : ∀ i j,i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    exact (side_cells_disjoint P b i j hij).mono sdiff_subset sdiff_subset
  obtain ⟨f,hSize,hSub,hExc⟩ := exists_chunked_subpartition A m hm hDis
  have hMissing : univ\univ.biUnion A ⊆ X := by
    intro v hv
    by_contra hx
    have hCover := side_cells_cover P b
    have hvCover : v ∈ univ.biUnion (sideCell P b) := by rw [hCover];exact mem_univ _
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hvCover
    exact (mem_sdiff.mp hv).2 (mem_biUnion.mpr ⟨i,mem_univ _,mem_sdiff.mpr ⟨hi,hx⟩⟩)
  refine ⟨f,hSize,?_,?_,?_⟩
  · intro j v hv
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hv
    exact (mem_filter.mp (mem_sdiff.mp (hSub j hu)).1).2
  · intro v hv
    cases hh : f v with
    | none => exact False.elim (hv hh)
    | some i => exact (mem_sdiff.mp (hSub i ((mem_cluster f i v).mpr hh))).2
  · have hM := card_le_card hMissing
    simp only [Fintype.card_coe] at hExc
    omega

theorem exists_aligned_punctured_cells (P : Finpartition (univ : Finset (V ⊕ V)))
    (X : Finset V) (m : ℕ) (hm : 0 < m) :
    ∃ (k : ℕ) (π σ : Fin k → P.parts) (f g : V → Option (Fin k)),
      (∀ i,(cluster f i).card=m) ∧ (∀ i,(cluster g i).card=m) ∧
      (∀ i,(cluster f i).map (sideEmbedding false) ⊆ (π i).val) ∧
      (∀ i,(cluster g i).map (sideEmbedding true) ⊆ (σ i).val) ∧
      (∀ v,f v ≠ none → v ∉ X) ∧ (∀ v,g v ≠ none → v ∉ X) ∧
      (exceptional f).card=(exceptional g).card ∧
      (exceptional f).card ≤ X.card+P.parts.card*(m-1) := by
  obtain ⟨f,hF,hFP,hFX,hFE⟩ := exists_punctured_side_cells P false X m hm
  obtain ⟨g,hG,hGP,hGX,hGE⟩ := exists_punctured_side_cells P true X m hm
  obtain ⟨ρ,ζ,f',g',hρ,hζ,hF',hG',hSame,hCost⟩ := exists_aligned_cells f g m hF hG
  refine ⟨_,(fun i => (ρ i).1),(fun i => (ζ i).1),f',g',hF',hG',?_,?_,?_,?_,hSame,?_⟩
  · intro i;rw [hρ];exact hFP (ρ i)
  · intro i;rw [hζ];exact hGP (ζ i)
  · intro v hv
    cases hh : f' v with
    | none => exact False.elim (hv hh)
    | some i =>
      have hi : v ∈ cluster f (ρ i) := by rw [←hρ];exact (mem_cluster f' i v).mpr hh
      exact hFX v (by rw [(mem_cluster f (ρ i) v).mp hi];exact Option.some_ne_none _)
  · intro v hv
    cases hh : g' v with
    | none => exact False.elim (hv hh)
    | some i =>
      have hi : v ∈ cluster g (ζ i) := by rw [←hζ];exact (mem_cluster g' i v).mpr hh
      exact hGX v (by rw [(mem_cluster g (ζ i) v).mp hi];exact Option.some_ne_none _)
  · exact hCost.trans (max_le hFE hGE)

end OverfullWork.BipartiteRegularitySource
