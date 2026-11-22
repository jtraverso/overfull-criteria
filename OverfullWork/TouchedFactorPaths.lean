module

public import OverfullWork.MergeFactorCut

@[expose] public section


/-! Restrict the cut to the cycles that meet it, and transfer the paths
back to the original vertex type. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset DirectedAbsorbingLadder
open scoped Classical
variable {V : Type*} [Fintype V]

def touchesCut (σ : Equiv.Perm V) (S : Finset V) (v : V) : Prop :=
  ∃ w ∈ S, σ.SameCycle v w

omit [Fintype V] in
theorem touchesCut_of_mem (σ : Equiv.Perm V) {S : Finset V} {v : V} (h : v ∈ S) :
    touchesCut σ S v := ⟨v,h,Equiv.Perm.SameCycle.refl σ v⟩

omit [Fintype V] in
theorem touchesCut_congr {σ : Equiv.Perm V} {S : Finset V} {v w : V}
    (h : σ.SameCycle v w) : touchesCut σ S v ↔ touchesCut σ S w :=
  ⟨fun ⟨x,hx,hs⟩ => ⟨x,hx,h.symm.trans hs⟩,fun ⟨x,hx,hs⟩ => ⟨x,hx,h.trans hs⟩⟩

theorem exists_cut_paths_on_touched_cycles (σ : Equiv.Perm V) (S : Finset V) :
    ∃ P : S → PathRequest (cutFactor σ S), ∃ e : Equiv.Perm (↑S),
      (∀ i, (P i).target = i.val ∧ (P i).source = σ (e i).val) ∧
      (∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices) ∧
      ∀ v, (∃ i, v ∈ (P i).vertices) ↔ touchesCut σ S v := by
  let U := {v : V // touchesCut σ S v}
  let ρ : Equiv.Perm U := σ.subtypePerm (fun v => by
    exact touchesCut_congr ((Equiv.Perm.SameCycle.refl σ v).apply_left))
  let B : Finset U := univ.filter (fun v => v.val ∈ S)
  have hB (v : U) : v ∈ B ↔ v.val ∈ S := by simp [B]
  let j : (↑S) ≃ (↑B) :=
    { toFun := fun i => ⟨⟨i.val,touchesCut_of_mem σ i.prop⟩,(hB _).mpr i.prop⟩
      invFun := fun i => ⟨i.val.val,(hB _).mp i.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun i => Subtype.ext (Subtype.ext rfl) }
  obtain ⟨P,e,hEnds,hDis,hCover⟩ := exists_cut_factor_paths ρ B (fun v => by
    obtain ⟨w,hw,hvw⟩ := v.prop
    let u : U := ⟨w,touchesCut_of_mem σ hw⟩
    exact ⟨u,(hB _).mpr hw,hvw.subtypePerm⟩)
  let Q (i : S) : PathRequest (cutFactor σ S) :=
    ⟨(P (j i)).source.val,(P (j i)).target.val,(P (j i)).tail.map Subtype.val,
      ⟨List.isChain_map_of_isChain Subtype.val
        (fun x y h => ⟨fun hm => h.1 ((hB x).mpr hm),congrArg Subtype.val h.2⟩) (P (j i)).route.1,
        by
          have h := congrArg (Option.map Subtype.val) (P (j i)).route.2
          simpa only [←List.getLast?_map,List.map_cons,Option.map_some] using h⟩,
      (P (j i)).simple.map Subtype.val_injective⟩
  have hVertices (i : S) : (Q i).vertices = (P (j i)).vertices.map Subtype.val := rfl
  refine ⟨Q,j.trans (e.trans j.symm),?_,?_,?_⟩
  · intro i
    exact ⟨congrArg Subtype.val (hEnds (j i)).1,congrArg Subtype.val (hEnds (j i)).2⟩
  · intro i k hik v hv hw
    rw [hVertices] at hv hw
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hw
    have hyx : y = x := Subtype.ext he
    subst y
    exact hDis _ _ (fun h => hik (j.injective h)) hx hy
  · intro v
    constructor
    · rintro ⟨i,hi⟩
      rw [hVertices] at hi
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hi
      exact x.prop
    · intro hv
      obtain ⟨i,hi⟩ := hCover (⟨v,hv⟩ : U)
      refine ⟨j.symm i,?_⟩
      rw [hVertices,j.apply_symm_apply]
      exact List.mem_map.mpr ⟨_,hi,rfl⟩

end OverfullWork.DirectedRobustExpansion
