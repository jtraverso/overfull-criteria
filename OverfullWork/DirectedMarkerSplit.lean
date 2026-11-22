module

public import OverfullWork.RealRobustOrderedHamilton

@[expose] public section


/-! Open the stitched cycle in GGKLO Lemma 7.3(i) at the contraction
vertex, restoring the two endpoints of the distinguished layout edge. -/
namespace OverfullWork.DirectedMarkerSplit

open DirectedAbsorbingLadder DirectedRobustExpansion
open scoped Classical

/-- Split the vertex of a simple directed cycle into its outgoing and
incoming representatives. The path then runs from the outgoing representative
to the incoming one, through every retained vertex of the cycle exactly once. -/
theorem exists_path_of_split_marker {X V : Type*} (H : Digraph X) (D : Digraph V)
    (T : List X) (root z : X) (f : X → V) (a b : V)
    (hHead : T.head? = some root) (hCycle : (T ++ [root]).IsChain H.Adj)
    (hSimple : T.Nodup) (hz : z ∈ T) (hab : a ≠ b)
    (hInj : Set.InjOn f {x | x ≠ z})
    (hFresh : ∀ x ∈ T, x ≠ z → f x ≠ a ∧ f x ≠ b)
    (hLift : ∀ ⦃x y⦄, H.Adj x y →
      D.Adj (if x = z then a else f x) (if y = z then b else f y)) :
    ∃ l : List X, (z :: l).Perm T ∧
      (a :: l.map f ++ [b]).IsChain D.Adj ∧ (a :: l.map f ++ [b]).Nodup ∧
      ∀ v, v ∈ (a :: l.map f ++ [b]) ↔
        v = a ∨ v = b ∨ ∃ x ∈ T, x ≠ z ∧ f x = v := by
  obtain ⟨l,hPerm,hClosed⟩ :=
    DirectedPrescribedVertexPath.rotate_closed_word H T root z hHead hCycle hz
  obtain ⟨hzl,hl⟩ := List.nodup_cons.mp (hPerm.nodup_iff.mpr hSimple)
  have hne {x : X} (hx : x ∈ l) : x ≠ z := fun h => hzl (h ▸ hx)
  have hmem {x : X} (hx : x ∈ l) : x ∈ T := hPerm.mem_iff.mp (List.mem_cons_of_mem _ hx)
  have hback {x : X} (hx : x ∈ T) (hxz : x ≠ z) : x ∈ l :=
    (List.mem_cons.mp (hPerm.mem_iff.mpr hx)).resolve_left hxz
  let out : X → V := fun x => if x = z then a else f x
  let into : X → V := fun x => if x = z then b else f x
  have hOut : l.map out = l.map f := List.map_congr_left (fun _ hx => if_neg (hne hx))
  have hInto : l.map into = l.map f := List.map_congr_left (fun _ hx => if_neg (hne hx))
  have hLinks : List.Forall₂ D.Adj ((z :: l).map out) ((l ++ [z]).map into) := by
    rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
    exact (List.isChain_cons_append_singleton_iff_forall₂.mp hClosed).imp (fun _ _ h => hLift h)
  refine ⟨l,hPerm,List.isChain_cons_append_singleton_iff_forall₂.mpr ?_,?_,?_⟩
  · simpa only [List.map_cons,List.map_append,List.map_nil,hOut,hInto,out,into,if_pos rfl,if_true] using
      hLinks
  · apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
        exact (hFresh x (hmem hx) (hne hx)).1 he
      · exact hab (List.mem_singleton.mp hm)
    · refine List.nodup_append.mpr ⟨?_, by simp, ?_⟩
      · exact hl.map_on fun x hx y hy he => hInj (hne hx) (hne hy) he
      · intro v hv w hw
        obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        have hwb := List.mem_singleton.mp hw
        subst w
        exact (hFresh x (hmem hx) (hne hx)).2
  · intro v
    simp only [List.mem_append,List.mem_cons,List.mem_map,List.not_mem_nil,or_false]
    constructor
    · rintro ((rfl | ⟨x,hx,rfl⟩) | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨x,hmem hx,hne hx,rfl⟩)
      · exact Or.inr (Or.inl rfl)
    · rintro (rfl | rfl | ⟨x,hx,hxz,rfl⟩)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr rfl
      · exact Or.inl (Or.inr ⟨x,hback hx hxz,rfl⟩)

end OverfullWork.DirectedMarkerSplit
