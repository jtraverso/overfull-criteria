module

public import OverfullWork.MaximumMatchingAugmentation
public import OverfullWork.AugmentedTutteComponents

@[expose] public section


/-! # Transporting high odd components to original vertex sets

A residual component avoiding the completed low clique contains only old
maximum-degree vertices. Its original preimage has the same cardinality;
its original edge boundary lies in the deleted original vertices.
-/
namespace OverfullWork.MaximumMatching
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 3000000

noncomputable def componentVertices {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (U : Set W) (C : (residual H U).ConnectedComponent) : Finset W :=
  C.supp.toFinset.image Subtype.val

noncomputable def oldComponentSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (C : (residual (augmentation G) U).ConnectedComponent) : Finset V :=
  univ.filter fun v => Sum.inl v∈componentVertices (augmentation G) U C

noncomputable def deletedOld (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) : Finset V := univ.filter fun v => Sum.inl v∈U

theorem mem_componentVertices {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (U : Set W) (C : (residual H U).ConnectedComponent) (z : W) :
    z∈componentVertices H U C ↔ ∃x,x∈C.supp ∧ x.val=z := by
  simp only [componentVertices,mem_image,Set.mem_toFinset]

theorem mem_oldComponentSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (C : (residual (augmentation G) U).ConnectedComponent) (v : V) :
    v∈oldComponentSet G U C ↔ Sum.inl v∈componentVertices (augmentation G) U C := by
  simp only [oldComponentSet,mem_filter,mem_univ,true_and]

omit [DecidableEq V] in
theorem mem_deletedOld (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (v : V) : v∈deletedOld G U ↔ Sum.inl v∈U := by
  simp only [deletedOld,mem_filter,mem_univ,true_and]

theorem componentVertices_not_deleted {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (U : Set W) (C : (residual H U).ConnectedComponent)
    (z : W) (hz : z∈componentVertices H U C) : z∉U := by
  obtain ⟨x,_,rfl⟩:=(mem_componentVertices H U C z).mp hz
  exact x.property.2

theorem componentVertices_card {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (U : Set W) (C : (residual H U).ConnectedComponent) :
    (componentVertices H U C).card=C.supp.ncard := by
  rw [componentVertices,card_image_of_injective _ Subtype.val_injective]
  exact (Set.ncard_eq_toFinset_card' _).symm

theorem componentVertices_disjoint {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (U : Set W) (C D : (residual H U).ConnectedComponent)
    (hne : C≠D) : Disjoint (componentVertices H U C) (componentVertices H U D) := by
  apply Finset.disjoint_left.mpr
  intro z hzC hzD
  obtain ⟨x,hx,hxz⟩:=(mem_componentVertices H U C z).mp hzC
  obtain ⟨y,hy,hyz⟩:=(mem_componentVertices H U D z).mp hzD
  have he : x=y:=Subtype.ext (hxz.trans hyz.symm)
  subst y
  exact hne (ConnectedComponent.eq_of_common_vertex hx hy)

theorem high_component_not_low (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (C : (residual (augmentation G) U).ConnectedComponent)
    (hC : C∈highOddComponents (augmentation G) {z | Low G z} U)
    (z : AugType V) (hz : z∈componentVertices (augmentation G) U C) : ¬Low G z := by
  obtain ⟨x,hx,rfl⟩:=(mem_componentVertices (augmentation G) U C z).mp hz
  have hd:=(mem_filter.mp hC).2
  exact fun hlo => Set.disjoint_left.mp hd hx hlo

theorem high_component_original (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (C : (residual (augmentation G) U).ConnectedComponent)
    (hC : C∈highOddComponents (augmentation G) {z | Low G z} U)
    (z : AugType V) (hz : z∈componentVertices (augmentation G) U C) :
    ∃v : V,z=Sum.inl v := by
  cases z with
  | inl v => exact ⟨v,rfl⟩
  | inr e => exact False.elim (high_component_not_low G U C hC (.inr e) hz trivial)

theorem oldComponentSet_all_maximum (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (C : (residual (augmentation G) U).ConnectedComponent)
    (hC : C∈highOddComponents (augmentation G) {z | Low G z} U)
    (v : V) (hv : v∈oldComponentSet G U C) : G.degree v=G.maxDegree := by
  exact (not_low_inl_iff G v).mp
    (high_component_not_low G U C hC (.inl v) ((mem_oldComponentSet G U C v).mp hv))

theorem card_oldComponentSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (C : (residual (augmentation G) U).ConnectedComponent)
    (hC : C∈highOddComponents (augmentation G) {z | Low G z} U) :
    (oldComponentSet G U C).card=C.supp.ncard := by
  have he : (oldComponentSet G U C).image Sum.inl=componentVertices (augmentation G) U C := by
    ext z
    constructor
    · rintro hz
      obtain ⟨v,hv,rfl⟩:=mem_image.mp hz
      exact (mem_oldComponentSet G U C v).mp hv
    · intro hz
      obtain ⟨v,rfl⟩:=high_component_original G U C hC z hz
      exact mem_image.mpr ⟨v,(mem_oldComponentSet G U C v).mpr hz,rfl⟩
  calc
    _ = ((oldComponentSet G U C).image Sum.inl).card :=
      (card_image_of_injective _ Sum.inl_injective).symm
    _ = _ := by rw [he,componentVertices_card]

theorem oldComponentSet_odd (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (C : (residual (augmentation G) U).ConnectedComponent)
    (hC : C∈highOddComponents (augmentation G) {z | Low G z} U) :
    Odd (oldComponentSet G U C).card := by
  rw [card_oldComponentSet G U C hC]
  have hh : C∈(residual (augmentation G) U).oddComponents :=
    Set.mem_toFinset.mp (mem_filter.mp hC).1
  exact hh

theorem oldComponentSet_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (C D : (residual (augmentation G) U).ConnectedComponent)
    (hne : C≠D) : Disjoint (oldComponentSet G U C) (oldComponentSet G U D) := by
  apply Finset.disjoint_left.mpr
  intro v hvC hvD
  exact Finset.disjoint_left.mp (componentVertices_disjoint (augmentation G) U C D hne)
    ((mem_oldComponentSet G U C v).mp hvC) ((mem_oldComponentSet G U D v).mp hvD)

theorem oldComponentSet_disjoint_deletedOld (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (C : (residual (augmentation G) U).ConnectedComponent) :
    Disjoint (oldComponentSet G U C) (deletedOld G U) := by
  apply Finset.disjoint_left.mpr
  intro v hvC hvU
  exact componentVertices_not_deleted (augmentation G) U C (.inl v)
    ((mem_oldComponentSet G U C v).mp hvC) ((mem_deletedOld G U v).mp hvU)

/-- Original edges leaving a residual component can only enter deleted vertices. -/
theorem oldComponentSet_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) (C : (residual (augmentation G) U).ConnectedComponent)
    (v : V) (hv : v∈oldComponentSet G U C) (w : V) (hvw : G.Adj v w) :
    w∈oldComponentSet G U C ∨ w∈deletedOld G U := by
  by_cases hw : Sum.inl w∈U
  · exact Or.inr ((mem_deletedOld G U w).mpr hw)
  · left
    obtain ⟨x,hx,hxv⟩:=(mem_componentVertices (augmentation G) U C (.inl v)).mp
      ((mem_oldComponentSet G U C v).mp hv)
    let y : ((⊤ : (augmentation G).Subgraph).deleteVerts U).verts:=
      ⟨Sum.inl w,⟨by trivial,hw⟩⟩
    have hxy : (residual (augmentation G) U).Adj x y := by
      apply Subgraph.Adj.coe
      apply Subgraph.deleteVerts_adj.mpr
      refine ⟨by trivial,x.property.2,by trivial,y.property.2,?_⟩
      change (augmentation G).Adj x.val (Sum.inl w)
      rw [hxv]
      exact original_edge G hvw
    have hy:=C.mem_supp_of_adj_mem_supp hx hxy
    apply (mem_oldComponentSet G U C w).mpr
    exact (mem_componentVertices (augmentation G) U C (.inl w)).mpr ⟨y,hy,rfl⟩

theorem card_deletedOld_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set (AugType V)) : (deletedOld G U).card≤U.ncard := by
  have hsub : (deletedOld G U).image Sum.inl⊆U.toFinset := by
    intro z hz
    obtain ⟨v,hv,rfl⟩:=mem_image.mp hz
    exact Set.mem_toFinset.mpr ((mem_deletedOld G U v).mp hv)
  calc
    _ = ((deletedOld G U).image Sum.inl).card :=
      (card_image_of_injective _ Sum.inl_injective).symm
    _ ≤ U.toFinset.card := card_le_card hsub
    _ = _ := (Set.ncard_eq_toFinset_card' _).symm

end OverfullWork.MaximumMatching
