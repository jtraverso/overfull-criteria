module

public import OverfullWork.KuhnOsthusBaseCycleBlowup

@[expose] public section


/-! Coordinates for the ordinary vertices that retain the physical
50-refinement used by the exceptional factors. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V I : Type*} [Fintype V]

theorem exists_ordinary_cluster_style_coordinates
    (Z : Finset V) (X : I → Finset V) (C : Fin 50 × I → Finset V)
    (label : V → Fin 50) (m : ℕ)
    (hSize : ∀ i, (X i).card = 50*m)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hOrd : ∀ i, Disjoint (X i) Z) (hCover : ∀ x ∉ Z, ∃ i, x ∈ X i)
    (hCell : ∀ j, (C j).card = m ∧ C j ⊆ X j.2)
    (hCellCover : ∀ i, (univ : Finset (Fin 50)).biUnion (fun j => C (j,i)) = X i)
    (hLabel : ∀ j x, x ∈ C j → label x = j.1) :
    ∃ (a : I → Fin (50*m) ↪ ↥Zᶜ) (cluster : ↥Zᶜ → I),
      let b i := (a i).trans (Function.Embedding.subtype (· ∈ Zᶜ))
      let A i j := univ.filter (fun w => label (a i w).val = j)
      (∀ i x, cluster x = i ↔ ∃ w, a i w = x) ∧
      (∀ i, univ.map (b i) = X i) ∧
      (∀ i j, (A i j).map (b i) = C (j,i)) ∧
      ∀ i j, (A i j).card = m := by
  let e (i : I) : Fin (50*m) ≃ X i :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe,hSize i])).symm
  let a (i : I) : Fin (50*m) ↪ ↥Zᶜ :=
    ⟨fun w => ⟨(e i w).val,mem_compl.mpr (fun hz => disjoint_left.mp (hOrd i) (e i w).prop hz)⟩,
      fun _ _ h => (e i).injective (Subtype.ext (congrArg (fun x : ↥Zᶜ => x.val) h))⟩
  let b i := (a i).trans (Function.Embedding.subtype (· ∈ Zᶜ))
  let cluster (x : ↥Zᶜ) := (hCover x.val (mem_compl.mp x.prop)).choose
  have hEq (i : I) (x : V) : x ∈ X i ↔ ∃ w, b i w = x := by
    exact ⟨fun hx => ⟨(e i).symm ⟨x,hx⟩,congrArg Subtype.val ((e i).apply_symm_apply _)⟩,
      fun ⟨w,hw⟩ => hw ▸ (e i w).prop⟩
  have hCoord (i : I) (x : ↥Zᶜ) : cluster x = i ↔ ∃ w, a i w = x := by
    have hx : x.val ∈ X (cluster x) := (hCover x.val (mem_compl.mp x.prop)).choose_spec
    constructor
    · intro hix
      obtain ⟨w,hw⟩ := (hEq i x.val).mp (hix ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
    · rintro ⟨w,hw⟩
      by_contra hix
      exact disjoint_left.mp (hDis _ _ hix) hx ((hEq i _).mpr ⟨w,congrArg Subtype.val hw⟩)
  let A i j := univ.filter (fun w => label (a i w).val = j)
  have hMap (i : I) (j : Fin 50) : (A i j).map (b i) = C (j,i) := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨w,hw,rfl⟩
      have hx : b i w ∈ X i := (hEq i _).mpr ⟨w,rfl⟩
      rw [←hCellCover i] at hx
      obtain ⟨j',_,hx⟩ := mem_biUnion.mp hx
      have hj := (mem_filter.mp hw).2
      have he : j' = j := (hLabel (j',i) _ hx).symm.trans hj
      simpa only [he] using hx
    · intro hx
      obtain ⟨w,hw⟩ := (hEq i x).mp ((hCell (j,i)).2 hx)
      refine ⟨w,mem_filter.mpr ⟨mem_univ _,?_⟩,hw⟩
      change label (b i w) = j
      rw [hw]
      exact hLabel _ _ hx
  refine ⟨a,cluster,hCoord,?_,hMap,?_⟩
  · intro i
    ext x
    simpa only [mem_map,mem_univ,true_and] using (hEq i x).symm
  · intro i j
    rw [←card_map (b i),hMap]
    exact (hCell (j,i)).1

end OverfullWork.DirectedRobustExpansion
