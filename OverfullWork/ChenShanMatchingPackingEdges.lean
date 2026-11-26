module

public import OverfullWork.ChenShanMatchingCandidates

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*}

/-- Both ordered representatives of every edge of the matching. -/
noncomputable def matchingArcs {X Y : Finset V} (f : X ≃ Y) : Finset (V × V) :=
  (univ : Finset X).biUnion fun x => {(x.1,(f x).1),((f x).1,x.1)}

theorem mem_matchingArcs {X Y : Finset V} (f : X ≃ Y) (u v : V) :
    (u,v) ∈ matchingArcs f ↔
      ∃ x : X, (u = x.1 ∧ v = (f x).1) ∨ (u = (f x).1 ∧ v = x.1) := by
  simp [matchingArcs,Prod.mk.injEq]

theorem matchingArcs_symm {X Y : Finset V} (f : X ≃ Y) {u v : V}
    (h : (u,v) ∈ matchingArcs f) : (v,u) ∈ matchingArcs f := by
  rw [mem_matchingArcs] at h ⊢
  obtain ⟨x,h|h⟩ := h
  · exact ⟨x,Or.inr ⟨h.2,h.1⟩⟩
  · exact ⟨x,Or.inl ⟨h.2,h.1⟩⟩

theorem matchingArcs_vertices {X Y : Finset V} (f : X ≃ Y) {u v : V}
    (h : (u,v) ∈ matchingArcs f) : u ∈ X ∪ Y ∧ v ∈ X ∪ Y := by
  obtain ⟨x,h|h⟩ := (mem_matchingArcs f u v).mp h
  · exact ⟨mem_union_left _ (h.1.symm ▸ x.2),mem_union_right _ (h.2.symm ▸ (f x).2)⟩
  · exact ⟨mem_union_right _ (h.1.symm ▸ (f x).2),mem_union_left _ (h.2.symm ▸ x.2)⟩

private theorem matchingArcs_mem_left {X Y : Finset V} (hXY : Disjoint X Y)
    (f : X ≃ Y) (x : X) (v : V) (h : (x.1,v) ∈ matchingArcs f) :
    v = (f x).1 := by
  obtain ⟨a,h|h⟩ := (mem_matchingArcs f _ _).mp h
  · have he : x = a := Subtype.ext h.1
    exact h.2.trans (congrArg (fun y : X => (f y).1) he.symm)
  · exact False.elim (disjoint_left.mp hXY x.2 (h.1.symm ▸ (f a).2))

theorem matchingArcs_unique_neighbor {X Y : Finset V} (hXY : Disjoint X Y)
    (f : X ≃ Y) {u v w : V} (hv : (u,v) ∈ matchingArcs f) (hw : (u,w) ∈ matchingArcs f) :
    v = w := by
  obtain ⟨x,h|h⟩ := (mem_matchingArcs f u v).mp hv
  · have hw' : (x.1,w) ∈ matchingArcs f := h.1 ▸ hw
    exact h.2.trans (matchingArcs_mem_left hXY f x w hw').symm
  · obtain ⟨a,ha|ha⟩ := (mem_matchingArcs f u w).mp hw
    · exact False.elim (disjoint_left.mp hXY (ha.1.symm ▸ a.2) (h.1.symm ▸ (f x).2))
    · have hxa : x = a := f.injective (Subtype.ext (h.1.symm.trans ha.1))
      exact h.2.trans ((congrArg Subtype.val hxa).trans ha.2.symm)

theorem matchingArcs_disjoint {X Y : Finset V} (hXY : Disjoint X Y)
    (f g : X ≃ Y) (hne : ∀ x, f x ≠ g x) : Disjoint (matchingArcs f) (matchingArcs g) := by
  apply disjoint_left.mpr
  rintro ⟨u,v⟩ hu hv
  obtain ⟨x,h|h⟩ := (mem_matchingArcs f u v).mp hu
  · have hg : (x.1,v) ∈ matchingArcs g := h.1 ▸ hv
    exact hne x (Subtype.ext (h.2.symm.trans (matchingArcs_mem_left hXY g x v hg)))
  · have hg : (x.1,u) ∈ matchingArcs g := h.2 ▸ matchingArcs_symm g hv
    exact hne x (Subtype.ext (h.1.symm.trans (matchingArcs_mem_left hXY g x u hg)))

/-- At most one candidate per neighbor can hit a fixed vertex in a
specified set. This applies on both sides of the matching. -/
theorem matchingArcs_candidate_hit_count {I : Type*} [Fintype I] {X Y : Finset V}
    (hXY : Disjoint X Y) (f : I → (X ≃ Y))
    (hDis : ∀ i j, i ≠ j → ∀ x, f i x ≠ f j x) (S : Finset V) (u : V) :
    ((univ : Finset I).filter (fun i => ∃ v ∈ S, (u,v) ∈ matchingArcs (f i))).card ≤
      (S ∩ (X ∪ Y)).card := by
  let H := (univ : Finset I).filter (fun i => ∃ v ∈ S, (u,v) ∈ matchingArcs (f i))
  have hWitness (i : H) : ∃ v ∈ S, (u,v) ∈ matchingArcs (f i.1) :=
    (mem_filter.mp i.2).2
  let pick (i : H) : V := (hWitness i).choose
  have hPick (i : H) : pick i ∈ S ∧ (u,pick i) ∈ matchingArcs (f i.1) := (hWitness i).choose_spec
  have hInj : Function.Injective pick := by
    intro i j he
    apply Subtype.ext
    by_contra hne
    have hD := matchingArcs_disjoint hXY _ _ (hDis i.1 j.1 hne)
    exact disjoint_left.mp hD (hPick i).2 (he.symm ▸ (hPick j).2)
  let emb : H ↪ V := ⟨pick,hInj⟩
  have hSub : (univ : Finset H).map emb ⊆ S ∩ (X ∪ Y) := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_map.mp hv
    exact mem_inter.mpr ⟨(hPick i).1,(matchingArcs_vertices _ (hPick i).2).2⟩
  have hCard := card_le_card hSub
  simpa only [card_map,card_univ,Fintype.card_coe] using hCard

end OverfullWork.ChenShan
